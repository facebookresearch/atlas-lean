/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.DHSecurity
public import CSLibExt.Crypto.Framework.Games
public import CSLibExt.Crypto.Protocols.PerfectSecrecy.GroupOneTimePad

/-!
# Key encapsulation and hybrid (KEM/DEM) encryption

**Key-encapsulation mechanisms** (Katz and Lindell, Section 11.3). `KEMScheme K PK SK E` has key
generation, encapsulation `encaps pk : PMF (K × E)` (a symmetric key and its encapsulation) and
decapsulation `decaps sk e : Option K`; `KEMScheme.Correct` is perfect correctness.
`kemExp`, `kemGame = bitGame kemExp`, `kemAdvantage`: the CPA experiment `KEM^cpa`, in which the
adversary sees the public key, the encapsulation, and either the encapsulated key (`false`) or a
uniform key (`true`).

**Hybrid encryption** (Katz and Lindell, Section 11.3). For a KEM and a data-encapsulation
mechanism (DEM) given as a Framework `SymmEncScheme M K C`, `hybrid S D : PKEScheme M PK SK (E × C)`
encrypts `m` as `(e, c)` with `(k, e) ← encaps pk` and `c ← D.enc k m`.
* `hybrid_correct`: correct KEM and correct DEM give a correct hybrid scheme.
* `pubCpaAdvantage_hybrid_le` (Katz and Lindell, Theorem 11.12, concrete form): if the DEM's key
  generation is uniform and its encryption draws coins from a fixed distribution `ρ`, then for
  every Framework public-key adversary `A`,
  `pubCpaAdvantage (hybrid S D) A ≤ kemAdvantage S (kemReduction encR ρ A true)`
  `+ kemAdvantage S (kemReduction encR ρ A false) + cpaAdvantage D (demReduction S A)`,
  where `demReduction S A` makes no encryption queries (`demReduction_queryBounded`), so only
  eavesdropping security of the DEM is used. The proof is Katz and Lindell's three-step hybrid.

**The Diffie–Hellman KEM** (Katz and Lindell, Section 11.4.2), built directly from `gpow`:
`dhKEM q g H` has secret key `x`, public key `g ^ x`, encapsulation `g ^ y` and key `H (h ^ y)`
for a key-derivation function `H`.
* `dhKEM_correct`: decapsulation recovers the key, for every `H`.
* `kemAdvantage_dhKEM`: for uniform adversary coins, `g` a generator, `|G| = q` and `H` a uniform
  KDF (`DHSecurity.IsUniformKDF`), the KEM advantage is exactly half the DDH advantage of
  `DHSecurity.kdfDist H B.guess`.
* `otpDEM G`: CSLib's group one-time pad `groupOTP G` embedded as a DEM by
  `SymmEncScheme.ofEncScheme`; `cpaAdvantage_otpDEM_demReduction`: its term in the hybrid bound
  is `0`. `pubCpaAdvantage_dhHybrid_le`: the resulting ElGamal-style hybrid
  scheme has CPA advantage at most the average of two DDH advantages.

The KEM adversary's coins are a `PMF`, as in the Framework. The reduction to the KEM samples the
DEM's encryption coins in advance, which is why `pubCpaAdvantage_hybrid_le` asks for
`D.enc k m = ρ.map (encR k m)`; every DEM of Katz and Lindell has this form.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 11.3 and 11.4.2.
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.KEM

open Cslib.Crypto.Framework FreeM OracleComp
open Cslib.Probability.PMF (uniformOfFintype)

/-! ### Key-encapsulation mechanisms -/

/-- A **key-encapsulation mechanism** (Katz and Lindell, Section 11.3) with keys in `K` and
encapsulations in `E`. -/
structure KEMScheme (K PK SK E : Type*) where
  /-- Key generation, producing a public key and a secret key. -/
  gen : PMF (PK × SK)
  /-- Encapsulation: a symmetric key together with its encapsulation. -/
  encaps : PK → PMF (K × E)
  /-- Deterministic decapsulation, with `none` for `⊥`. -/
  decaps : SK → E → Option K

/-- **Correctness** of a KEM (perfect correctness): decapsulation recovers every encapsulated
key. -/
def KEMScheme.Correct {K PK SK E : Type*} (S : KEMScheme K PK SK E) : Prop :=
  ∀ kp ∈ S.gen.support, ∀ ke ∈ (S.encaps kp.1).support, S.decaps kp.2 ke.2 = some ke.1

/-- A CPA adversary against a KEM: from the public key, the encapsulation and a candidate key it
guesses whether the key is random. -/
structure KEMAdversary (PK E K R : Type*) where
  /-- The distribution of the adversary's random coins. -/
  coins : PMF R
  /-- The guess (`true`: the key is random). -/
  guess : PK → E → K → R → Bool

section CPA

variable {K PK SK E R : Type*} [Fintype K] [Nonempty K]

/-- The key the KEM adversary sees: the encapsulated key `k` for `false`, a uniform key for
`true`. -/
noncomputable def challengeKey (b : Bool) (k : K) : PMF K :=
  if b then uniformOfFintype K else PMF.pure k

/-- The left-or-right KEM experiment with challenge bit `b`. -/
noncomputable def kemExp (S : KEMScheme K PK SK E) (A : KEMAdversary PK E K R) (b : Bool) :
    PMF Bool :=
  S.gen.bind fun kp => A.coins.bind fun r => (S.encaps kp.1).bind fun ke =>
    (challengeKey b ke.1).map fun k => A.guess kp.1 ke.2 k r

/-- **`KEM^cpa`** (Katz and Lindell, Section 11.3): a uniform bit selects the real or a uniform
key, and the experiment outputs `1` when the adversary guesses the bit. -/
noncomputable def kemGame (S : KEMScheme K PK SK E) (A : KEMAdversary PK E K R) : PMF Bool :=
  bitGame (kemExp S A)

/-- The KEM advantage `|Pr[KEM^cpa = 1] - 1/2|`. -/
noncomputable def kemAdvantage (S : KEMScheme K PK SK E) (A : KEMAdversary PK E K R) : ℝ :=
  guessAdvantage (kemGame S A)

/-- The KEM advantage is half the distinguishing advantage between the two worlds. -/
theorem kemAdvantage_eq (S : KEMScheme K PK SK E) (A : KEMAdversary PK E K R) :
    kemAdvantage S A = advantage (kemExp S A true) (kemExp S A false) / 2 :=
  guessAdvantage_bitGame _

end CPA

/-! ### Hybrid encryption -/

section Hybrid

variable {M K PK SK E C : Type*}

/-- **Hybrid encryption** (Katz and Lindell, Section 11.3): encapsulate a key with the KEM and
encrypt the message under it with the DEM. Decryption fails when decapsulation fails. -/
noncomputable def hybrid (S : KEMScheme K PK SK E) (D : SymmEncScheme M K C) :
    PKEScheme M PK SK (E × C) where
  gen := S.gen
  enc pk m := (S.encaps pk).bind fun ke => (D.enc ke.1 m).map fun c => (ke.2, c)
  dec sk c := (S.decaps sk c.1).bind fun k => D.dec k c.2

/-- **Correctness of hybrid encryption**: a correct KEM whose keys are DEM keys, and a correct
DEM, give a correct public-key scheme. -/
theorem hybrid_correct {S : KEMScheme K PK SK E} {D : SymmEncScheme M K C} (hS : S.Correct)
    (hD : D.Correct)
    (hkey : ∀ kp ∈ S.gen.support, ∀ ke ∈ (S.encaps kp.1).support, ke.1 ∈ D.gen.support) :
    (hybrid S D).Correct := by
  intro kp hkp m c hc
  simp only [hybrid, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hc ⊢
  obtain ⟨ke, hke, c', hc', rfl⟩ := hc
  rw [hS kp hkp ke hke, Option.bind_some, hD ke.1 (hkey kp hkp ke hke) m c' hc']

variable {R Rho : Type*}

/-- The KEM adversary built from a public-key adversary `A` and a fixed challenge bit `b`: it
encrypts `m_b` under its candidate key with presampled DEM coins and runs `A`. -/
noncomputable def kemReduction (encR : K → M → Rho → C) (ρ : PMF Rho)
    (A : PubCPAAdversary M PK (E × C) R) (b : Bool) : KEMAdversary PK E K (R × Rho) where
  coins := A.coins.bind fun r => ρ.map fun s => (r, s)
  guess pk e k rs := A.guess pk (e, encR k (pick (A.choose pk rs.1) b) rs.2) rs.1

/-- The DEM eavesdropper built from a public-key adversary: it runs key generation and
encapsulation itself, and pairs its challenge ciphertext with the encapsulation. -/
noncomputable def demReduction (S : KEMScheme K PK SK E) (A : PubCPAAdversary M PK (E × C) R) :
    CPAAdversary M C (PK × E × R) where
  coins := S.gen.bind fun kp => (S.encaps kp.1).bind fun ke => A.coins.map fun r => (kp.1, ke.2, r)
  run x := pure (A.choose x.1 x.2.2, fun c => pure (A.guess x.1 (x.2.1, c) x.2.2))

/-- The DEM reduction makes no encryption queries: it is an eavesdropper. -/
theorem demReduction_queryBounded (S : KEMScheme K PK SK E)
    (A : PubCPAAdversary M PK (E × C) R) : (demReduction S A).QueryBounded 0 := fun _ _ =>
  isQueryBounded_pure 0 _

variable [Fintype K] [Nonempty K]

/-- The intermediate worlds of the hybrid proof: challenge bit `b`, and the DEM key is the
encapsulated key (`u = false`) or a uniform key (`u = true`). -/
noncomputable def hybWorld (S : KEMScheme K PK SK E) (D : SymmEncScheme M K C)
    (A : PubCPAAdversary M PK (E × C) R) (b u : Bool) : PMF Bool :=
  S.gen.bind fun kp => A.coins.bind fun r => (S.encaps kp.1).bind fun ke =>
    (challengeKey u ke.1).bind fun k =>
      (D.enc k (pick (A.choose kp.1 r) b)).map fun c => A.guess kp.1 (ke.2, c) r

/-- The public-key experiment of the hybrid scheme is the hybrid world with the real key. -/
theorem pubCpaExp_hybrid (S : KEMScheme K PK SK E) (D : SymmEncScheme M K C)
    (A : PubCPAAdversary M PK (E × C) R) (b : Bool) :
    pubCpaExp (hybrid S D) A b = hybWorld S D A b false := by
  simp [pubCpaExp, hybrid, hybWorld, challengeKey, PMF.map_bind, PMF.map_comp,
    Function.comp_def]

/-- The KEM experiment of `kemReduction` is the hybrid world with the corresponding key. -/
theorem kemExp_kemReduction (S : KEMScheme K PK SK E) {D : SymmEncScheme M K C}
    {encR : K → M → Rho → C} {ρ : PMF Rho} (hD : ∀ k m, D.enc k m = ρ.map (encR k m))
    (A : PubCPAAdversary M PK (E × C) R) (b u : Bool) :
    kemExp S (kemReduction encR ρ A b) u = hybWorld S D A b u := by
  simp only [kemExp, kemReduction, hybWorld, hD, PMF.bind_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def]
  congr 1; funext kp; congr 1; funext r
  simp only [← PMF.bind_pure_comp, Function.comp_def]
  rw [PMF.bind_comm ρ]
  congr 1; funext ke
  exact PMF.bind_comm _ _ _

/-- The CPA experiment of `demReduction` is the hybrid world with a uniform key. -/
theorem cpaExp_demReduction (S : KEMScheme K PK SK E) {D : SymmEncScheme M K C}
    (hgen : D.gen = uniformOfFintype K) (A : PubCPAAdversary M PK (E × C) R) (b : Bool) :
    cpaExp D (demReduction S A) b = hybWorld S D A b true := by
  simp only [cpaExp, demReduction, hybWorld, hgen, challengeKey, evalPMF_pure, PMF.pure_bind,
    PMF.bind_bind, PMF.bind_map, Function.comp_def, ite_true]
  simp only [← PMF.bind_pure_comp, Function.comp_def]
  rw [PMF.bind_comm (uniformOfFintype K)]
  congr 1; funext kp
  rw [PMF.bind_comm (uniformOfFintype K), PMF.bind_comm A.coins]
  congr 1; funext ke
  rw [PMF.bind_comm (uniformOfFintype K)]

/-- **Security of hybrid encryption** (Katz and Lindell, Theorem 11.12, concrete form): the CPA
advantage of `A` against the hybrid scheme is at most the KEM advantages of the two reductions
plus the eavesdropping advantage of the DEM reduction. -/
theorem pubCpaAdvantage_hybrid_le (S : KEMScheme K PK SK E) {D : SymmEncScheme M K C}
    (hgen : D.gen = uniformOfFintype K) {encR : K → M → Rho → C} {ρ : PMF Rho}
    (hD : ∀ k m, D.enc k m = ρ.map (encR k m)) (A : PubCPAAdversary M PK (E × C) R) :
    pubCpaAdvantage (hybrid S D) A ≤
      kemAdvantage S (kemReduction encR ρ A true) + kemAdvantage S (kemReduction encR ρ A false) +
        cpaAdvantage D (demReduction S A) := by
  rw [pubCpaAdvantage_eq, kemAdvantage_eq, kemAdvantage_eq, cpaAdvantage_eq,
    pubCpaExp_hybrid, pubCpaExp_hybrid, kemExp_kemReduction S hD, kemExp_kemReduction S hD,
    kemExp_kemReduction S hD, kemExp_kemReduction S hD, cpaExp_demReduction S hgen,
    cpaExp_demReduction S hgen]
  have h1 := advantage_triangle (hybWorld S D A true false) (hybWorld S D A true true)
    (hybWorld S D A false false)
  have h2 := advantage_triangle (hybWorld S D A true true) (hybWorld S D A false true)
    (hybWorld S D A false false)
  have c1 := advantage_comm (hybWorld S D A true false) (hybWorld S D A true true)
  have c2 := advantage_comm (hybWorld S D A false true) (hybWorld S D A false false)
  linarith

end Hybrid

/-! ### The Diffie–Hellman KEM -/

section DH

open DHSecurity ElGamal

variable {G : Type*} [CommGroup G] {q : ℕ} [NeZero q] (g : G) {K : Type*}

variable (q) in
/-- The **Diffie–Hellman KEM** (Katz and Lindell, Section 11.4.2) with key-derivation function
`H`: secret key `x`, public key `h = g ^ x`; encapsulation samples `y` and outputs the key
`H (h ^ y)` with encapsulation `g ^ y`; decapsulation of `e` is `H (e ^ x)`. -/
noncomputable def dhKEM (H : G → K) : KEMScheme K G (ZMod q) G where
  gen := (uniformOfFintype (ZMod q)).map fun x => (gpow g x, x)
  encaps h := (uniformOfFintype (ZMod q)).map fun y => (H (gpow h y), gpow g y)
  decaps x e := some (H (gpow e x))

/-- **Correctness of the Diffie–Hellman KEM**, for every key-derivation function. -/
theorem dhKEM_correct (H : G → K) : (dhKEM q g H).Correct := by
  intro kp hkp ke hke
  simp only [dhKEM, PMF.support_map, Set.mem_image] at hkp hke
  obtain ⟨x, -, rfl⟩ := hkp
  obtain ⟨y, -, rfl⟩ := hke
  change some (H (gpow (gpow g y) x)) = _
  rw [dh_agree g x y]

omit [NeZero q] in
private theorem uniformOfFintype_prod3 {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] [Fintype γ] [Nonempty γ] :
    uniformOfFintype (α × β × γ) = (uniformOfFintype α).bind fun a =>
      (uniformOfFintype β).bind fun b => (uniformOfFintype γ).map fun c => (a, b, c) := by
  rw [← Cslib.Probability.PMF.uniformOfFintype_prod, ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp [PMF.map_bind, PMF.map_comp, Function.comp_def]

variable [Fintype K] [Nonempty K] {R : Type*} [Fintype R] [Nonempty R]

/-- With the encapsulated key, the KEM experiment of the Diffie–Hellman KEM is the real world of
`KE^eav` with key derivation. -/
theorem kemExp_dhKEM_false (H : G → K) (B : KEMAdversary G G K R)
    (hB : B.coins = uniformOfFintype R) :
    kemExp (dhKEM q g H) B false = kdfReal q g H B.guess := by
  rw [kdfReal, uniformOfFintype_prod3]
  simp only [kemExp, dhKEM, hB, challengeKey, transcript, aliceKey, PMF.bind_map, PMF.map_bind,
    PMF.map_comp, Function.comp_def, Bool.false_eq_true, ite_false, PMF.pure_map]
  simp only [← PMF.bind_pure_comp, Function.comp_def]
  congr 1; funext x
  rw [PMF.bind_comm (uniformOfFintype R)]
  congr 1; funext y
  congr 1; funext r
  rw [dh_agree g x y]

/-- With a uniform key, the KEM experiment of the Diffie–Hellman KEM is the random world of
`KE^eav` with key derivation. -/
theorem kemExp_dhKEM_true (H : G → K) (B : KEMAdversary G G K R)
    (hB : B.coins = uniformOfFintype R) :
    kemExp (dhKEM q g H) B true = kdfRand q g B.guess := by
  rw [kdfRand, uniformOfFintype_prod3, ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [kemExp, dhKEM, hB, challengeKey, transcript, PMF.bind_map, PMF.map_bind,
    PMF.map_comp, Function.comp_def, ite_true]
  simp only [← PMF.bind_pure_comp, Function.comp_def]
  congr 1; funext x
  rw [PMF.bind_comm (uniformOfFintype R)]
  congr 1; funext y
  exact PMF.bind_comm _ _ _

variable [Fintype G]

/-- **The Diffie–Hellman KEM is CPA-secure if DDH is hard** (Katz and Lindell, Section 11.4.2),
exact form: for a uniform KDF `H` and an adversary with uniform coins, the KEM advantage is half
the DDH advantage of `kdfDist H B.guess`. -/
theorem kemAdvantage_dhKEM (hgen : ∀ x : G, x ∈ Subgroup.zpowers g) (hcard : Fintype.card G = q)
    {H : G → K} (hH : IsUniformKDF H) (B : KEMAdversary G G K R)
    (hB : B.coins = uniformOfFintype R) :
    kemAdvantage (dhKEM q g H) B = ddhAdvantage q g (kdfDist H B.guess) / 2 := by
  rw [kemAdvantage_eq, kemExp_dhKEM_true g H B hB, kemExp_dhKEM_false g H B hB,
    kdfRand_eq_keRand g hH, kdfReal_eq_keReal, advantage_comm,
    advantage_keReal_keRand g hgen hcard]

end DH

/-! ### The group one-time pad as a DEM, and the ElGamal-style hybrid -/

section OTP

variable (G : Type*) [Group G] [Fintype G]

/-- The group one-time pad as a DEM (Katz and Lindell, Section 11.4.1): CSLib's `groupOTP G`
(uniform key `k`, `Enc_k(m) = k m`, `Dec_k(c) = k⁻¹ c`) embedded by
`SymmEncScheme.ofEncScheme`. -/
noncomputable abbrev otpDEM : SymmEncScheme G G G :=
  SymmEncScheme.ofEncScheme (Cslib.Crypto.Protocols.PerfectSecrecy.groupOTP G)

/-- The one-time-pad DEM is correct, by `SymmEncScheme.correct_ofEncScheme`. -/
theorem otpDEM_correct : (otpDEM G).Correct := SymmEncScheme.correct_ofEncScheme _

variable {G} {PK SK E R : Type*}

/-- The DEM term of the hybrid bound vanishes for the one-time pad: a uniform key masks the
challenge message perfectly. -/
theorem cpaAdvantage_otpDEM_demReduction (S : KEMScheme G PK SK E)
    (A : PubCPAAdversary G PK (E × G) R) : cpaAdvantage (otpDEM G) (demReduction S A) = 0 := by
  have h : ∀ b, cpaExp (otpDEM G) (demReduction S A) b =
      (demReduction S A).coins.bind fun x =>
        (uniformOfFintype G).map fun c => A.guess x.1 (x.2.1, c) x.2.2 := by
    intro b
    simp only [cpaExp, otpDEM, SymmEncScheme.ofEncScheme,
      Cslib.Crypto.Protocols.PerfectSecrecy.groupOTP,
      Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.ofPure, demReduction, evalPMF_pure,
      PMF.pure_bind]
    rw [PMF.bind_comm (uniformOfFintype G)]
    congr 1; funext x
    conv_rhs => rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv
      (Equiv.mulRight (pick (A.choose x.1 x.2.2) b)), PMF.map_comp]
    rfl
  rw [cpaAdvantage_eq, h, h, advantage_self, zero_div]

end OTP

section DHHybrid

open DHSecurity ElGamal

variable {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} [NeZero q] (g : G) {R : Type*} [Fintype R]
  [Nonempty R]

/-- **CPA security of the ElGamal-style hybrid scheme** (Diffie–Hellman KEM with the identity KDF
and the one-time-pad DEM): its CPA advantage is at most the average DDH advantage of the two KEM
reductions. -/
theorem pubCpaAdvantage_dhHybrid_le (hgen : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Fintype.card G = q) (A : PubCPAAdversary G G (G × G) R)
    (hA : A.coins = uniformOfFintype R) :
    pubCpaAdvantage (hybrid (dhKEM q g id) (otpDEM G)) A ≤
      (ddhAdvantage q g (kdfDist id (kemReduction (fun k m (_ : Unit) => k * m)
          (uniformOfFintype Unit) A true).guess) +
        ddhAdvantage q g (kdfDist id (kemReduction (fun k m (_ : Unit) => k * m)
          (uniformOfFintype Unit) A false).guess)) / 2 := by
  have hD : ∀ k m, (otpDEM G).enc k m =
      (uniformOfFintype Unit).map ((fun k m (_ : Unit) => k * m) k m) :=
    fun k m => (PMF.map_const _ _).symm
  have hB : ∀ b, (kemReduction (fun k m (_ : Unit) => k * m) (uniformOfFintype Unit) A b).coins =
      uniformOfFintype (R × Unit) := fun b => by
    rw [kemReduction, hA]
    exact Cslib.Probability.PMF.uniformOfFintype_prod R Unit
  have hid : IsUniformKDF (id : G → G) := isUniformKDF_of_bijective Function.bijective_id
  have h := pubCpaAdvantage_hybrid_le (dhKEM q g id) (rfl : (otpDEM G).gen = _) hD A
  rw [kemAdvantage_dhKEM g hgen hcard hid _ (hB true),
    kemAdvantage_dhKEM g hgen hcard hid _ (hB false),
    cpaAdvantage_otpDEM_demReduction] at h
  linarith

end DHHybrid

end Cslib.Crypto.PublicKey.KEM
