/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.ElGamal
public import CSLibExt.Crypto.Framework.Advantage

/-!
# Security of Diffie–Hellman key agreement against eavesdroppers

Diffie–Hellman key agreement (Katz and Lindell, Construction 10.2) over a commutative group `G`
with an element `g` and exponents in `ZMod q`: Alice sends `transcript.1 = g ^ a`, Bob sends
`transcript.2 = g ^ b`, and both output `g ^ (a b)` (`aliceKey_eq_bobKey`).

**Eavesdropping security** (Katz and Lindell, Definition 10.1 and Theorem 10.3, in the modified
experiment where the random key is a uniform group element), in exact form. An eavesdropper
`E : G → G → G → S → Bool` sees the transcript, a candidate key and uniform coins in `S`.
* `keReal`: the candidate key is the key Alice outputs; `keRand`: a uniform element of `G`.
  `keGame = bitGame keExp` is `KE^eav`, and `keAdvantage = |Pr[KE^eav = 1] - 1/2|`.
* `keReal_eq_ddhReal`, `keRand_eq_ddhRand`: these are exactly the DDH experiments of
  `ElGamal.lean` (the latter needs `g` to generate `G` and `|G| = q`).
* `advantage_keReal_keRand`: the distinguishing advantage equals `ddhAdvantage q g E`;
  `keAdvantage_eq`: `keAdvantage q g E = ddhAdvantage q g E / 2`.

**Key derivation.** A key-derivation function is any `H : G → K`; the assumption on it is
`IsUniformKDF H`: `H` maps the uniform distribution on `G` to the uniform distribution on `K`
(`isUniformKDF_of_bijective`, and `isUniformKDF_of_card_fiber` for functions all of whose fibers
have the same size). This is a property of a fixed function, not a random oracle: the
eavesdropper may know `H`.
* `kdfReal`, `kdfRand`, `kdfAdvantage`: `KE^eav` for the derived key `H (g ^ (a b))` against a
  uniform key in `K`.
* `kdfAdvantage_eq`: for a uniform KDF, `kdfAdvantage q g H E = ddhAdvantage q g (kdfDist H E) / 2`,
  where `kdfDist H E` applies `H` to the third DDH component and runs `E`.

The eavesdropper's coins are uniform on a finite type, as in `ElGamal.ddhReal`; migrating to the
Framework convention (`coins : PMF R`) goes together with the DDH games.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 8.3.2 and 10.3.
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.DHSecurity

open Finset Cslib.Crypto.Framework Cslib.Crypto.PublicKey.ElGamal

/-! ### Uniform distributions on products -/

section Uniform

open Cslib.Probability.PMF

variable {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] [Fintype γ]
  [Nonempty γ]

/-- Mapping the first component of a uniform pair by a uniformity-preserving map. -/
theorem uniformOfFintype_map_prodMap_left {f : α → β}
    (hf : (uniformOfFintype α).map f = uniformOfFintype β) :
    (uniformOfFintype (α × γ)).map (Prod.map f id) = uniformOfFintype (β × γ) := by
  rw [← uniformOfFintype_prod, ← uniformOfFintype_prod, ← hf, PMF.bind_map, PMF.map_bind]
  congr 1
  funext a
  simp [PMF.map_comp, Function.comp_def]

/-- Mapping the second component of a uniform pair by a uniformity-preserving map. -/
theorem uniformOfFintype_map_prodMap_right {f : α → β}
    (hf : (uniformOfFintype α).map f = uniformOfFintype β) :
    (uniformOfFintype (γ × α)).map (Prod.map id f) = uniformOfFintype (γ × β) := by
  rw [← uniformOfFintype_prod, ← uniformOfFintype_prod, PMF.map_bind]
  congr 1
  funext c
  rw [← hf, PMF.map_comp, PMF.map_comp]
  rfl

/-- Mapping the third of four uniform components by a uniformity-preserving map. -/
theorem uniformOfFintype_map_third {A B S : Type*} [Fintype A] [Nonempty A] [Fintype B]
    [Nonempty B] [Fintype S] [Nonempty S] {f : α → β}
    (hf : (uniformOfFintype α).map f = uniformOfFintype β) :
    (uniformOfFintype (A × B × α × S)).map (fun ω => (ω.1, ω.2.1, f ω.2.2.1, ω.2.2.2)) =
      uniformOfFintype (A × B × β × S) :=
  uniformOfFintype_map_prodMap_right (uniformOfFintype_map_prodMap_right
    (uniformOfFintype_map_prodMap_left (γ := S) hf))

end Uniform

/-! ### The protocol -/

section Protocol

variable {G : Type*} [CommGroup G] {q : ℕ} (g : G)

/-- The transcript of Diffie–Hellman key agreement (Katz and Lindell, Construction 10.2): Alice's
message `g ^ a` and Bob's message `g ^ b`. -/
def transcript (a b : ZMod q) : G × G := (gpow g a, gpow g b)

/-- Alice's output: Bob's message raised to her secret `a`. -/
def aliceKey (a : ZMod q) (B : G) : G := gpow B a

/-- Bob's output: Alice's message raised to his secret `b`. -/
def bobKey (b : ZMod q) (A : G) : G := gpow A b

/-- **Correctness** of Diffie–Hellman key agreement (Katz and Lindell, Construction 10.2): both
parties output the same key. -/
theorem aliceKey_eq_bobKey (a b : ZMod q) :
    aliceKey a (transcript g a b).2 = bobKey b (transcript g a b).1 :=
  dh_agree g a b

end Protocol

/-! ### Eavesdropping security from DDH -/

section Security

variable {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} [NeZero q] (g : G)
  {S : Type*} [Fintype S] [Nonempty S]

variable (q) in
/-- The real world of `KE^eav` (Katz and Lindell, Definition 10.1): uniform secrets `a`, `b` and
coins `s`; the eavesdropper sees the transcript and the key Alice outputs. -/
noncomputable def keReal (E : G → G → G → S → Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q × ZMod q × S)).map fun ω =>
    E (transcript g ω.1 ω.2.1).1 (transcript g ω.1 ω.2.1).2
      (aliceKey ω.1 (transcript g ω.1 ω.2.1).2) ω.2.2

variable (q) in
/-- The random world of `KE^eav`: the eavesdropper sees the transcript and a uniform group
element, independent of the transcript (Katz and Lindell's modified experiment, Section 10.3). -/
noncomputable def keRand (E : G → G → G → S → Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q × ZMod q × G × S)).map fun ω =>
    E (transcript g ω.1 ω.2.1).1 (transcript g ω.1 ω.2.1).2 ω.2.2.1 ω.2.2.2

variable (q) in
/-- The left-or-right key-exchange experiment: `true` gives the random key, `false` the real
one. -/
noncomputable def keExp (E : G → G → G → S → Bool) (b : Bool) : PMF Bool :=
  if b then keRand q g E else keReal q g E

variable (q) in
/-- **`KE^eav`** (Katz and Lindell, Definition 10.1): a uniform bit chooses the real or the
random key, and the experiment outputs `1` when the eavesdropper guesses the bit. -/
noncomputable def keGame (E : G → G → G → S → Bool) : PMF Bool := bitGame (keExp q g E)

variable (q) in
/-- The key-exchange advantage `|Pr[KE^eav = 1] - 1/2|`. -/
noncomputable def keAdvantage (E : G → G → G → S → Bool) : ℝ := guessAdvantage (keGame q g E)

omit [Fintype G] in
/-- The real world of `KE^eav` is the real DDH experiment: the eavesdropper sees
`(g ^ a, g ^ b, g ^ (a b))`. -/
theorem keReal_eq_ddhReal (hg : g ^ q = 1) (E : G → G → G → S → Bool) :
    keReal q g E = ddhReal q g E := by
  simp only [keReal, ddhReal, transcript, aliceKey, dh_key_eq hg]

/-- The random world of `KE^eav` is the random DDH experiment: when `g` generates `G` and
`|G| = q`, a uniform group element is `g ^ z` for a uniform exponent `z`. -/
theorem keRand_eq_ddhRand (hgen : ∀ x : G, x ∈ Subgroup.zpowers g) (hcard : Fintype.card G = q)
    (E : G → G → G → S → Bool) : keRand q g E = ddhRand q g E := by
  have h : (Cslib.Probability.PMF.uniformOfFintype (ZMod q)).map (gpow g) =
      Cslib.Probability.PMF.uniformOfFintype G := by
    rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv (gpowEquiv hgen hcard)]
    congr 1
    funext a
    exact (gpowEquiv_apply hgen hcard a).symm
  rw [keRand, ← uniformOfFintype_map_third (A := ZMod q) (B := ZMod q) (S := S) h, PMF.map_comp]
  rfl

/-- **Diffie–Hellman key agreement is eavesdropping-secure if DDH is hard**, distinguishing form:
the advantage of `E` between the real and the random key is exactly its DDH advantage. -/
theorem advantage_keReal_keRand (hgen : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Fintype.card G = q) (E : G → G → G → S → Bool) :
    advantage (keReal q g E) (keRand q g E) = ddhAdvantage q g E := by
  rw [keReal_eq_ddhReal g (hcard ▸ pow_card_eq_one), keRand_eq_ddhRand g hgen hcard]
  rfl

/-- **Diffie–Hellman key agreement is eavesdropping-secure if DDH is hard** (Katz and Lindell,
Theorem 10.3), exact form: `keAdvantage q g E = ddhAdvantage q g E / 2`. -/
theorem keAdvantage_eq (hgen : ∀ x : G, x ∈ Subgroup.zpowers g) (hcard : Fintype.card G = q)
    (E : G → G → G → S → Bool) : keAdvantage q g E = ddhAdvantage q g E / 2 := by
  rw [keAdvantage, keGame, guessAdvantage_bitGame,
    show keExp q g E true = keRand q g E from rfl, show keExp q g E false = keReal q g E from rfl,
    advantage_comm, advantage_keReal_keRand g hgen hcard]

/-- Any bound `ε` on the DDH advantage gives the bound `ε / 2` on the key-exchange advantage. -/
theorem keAdvantage_le (hgen : ∀ x : G, x ∈ Subgroup.zpowers g) (hcard : Fintype.card G = q)
    (E : G → G → G → S → Bool) {ε : ℝ} (hε : ddhAdvantage q g E ≤ ε) :
    keAdvantage q g E ≤ ε / 2 := by
  rw [keAdvantage_eq g hgen hcard]
  linarith

end Security

/-! ### Key derivation -/

section KDF

variable {G K : Type*} [Fintype G] [Nonempty G] [Fintype K] [Nonempty K]

/-- A **uniform key-derivation function**: `H` maps a uniform element of `G` to a uniform element
of `K`. This is the minimal assumption under which hashing a uniform Diffie–Hellman key yields a
uniform symmetric key (Katz and Lindell, Section 11.4.2, use a hash function with this property).
Wave 3: unify with the ROM lane's KDF. -/
def IsUniformKDF (H : G → K) : Prop :=
  (Cslib.Probability.PMF.uniformOfFintype G).map H = Cslib.Probability.PMF.uniformOfFintype K

/-- Every bijection is a uniform KDF. -/
theorem isUniformKDF_of_bijective {H : G → K} (hH : Function.Bijective H) : IsUniformKDF H :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.ofBijective H hH)

/-- A function all of whose fibers have `|G| / |K|` elements is a uniform KDF. -/
theorem isUniformKDF_of_card_fiber [DecidableEq K] {H : G → K}
    (h : ∀ k, (univ.filter fun x => H x = k).card * Fintype.card K = Fintype.card G) :
    IsUniformKDF H := by
  classical
  ext k
  rw [PMF.map_apply, tsum_fintype]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hfilter : (univ.filter fun x => k = H x) = univ.filter fun x => H x = k := by
    ext x; simp [eq_comm]
  rw [hfilter]
  set c := (univ.filter fun x => H x = k).card
  have hk : ((c : ENNReal) * Fintype.card K) = Fintype.card G := by exact_mod_cast h k
  have hc0 : (c : ENNReal) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hk
    exact (by simp : (Fintype.card G : ENNReal) ≠ 0) hk.symm
  rw [← hk, ENNReal.mul_inv (Or.inl hc0) (Or.inl (ENNReal.natCast_ne_top _)), ← mul_assoc,
    ENNReal.mul_inv_cancel hc0 (ENNReal.natCast_ne_top _), one_mul]

end KDF

section KDFSecurity

variable {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} [NeZero q] (g : G)
  {K : Type*} [Fintype K] [Nonempty K] {S : Type*} [Fintype S] [Nonempty S]

variable (q) in
/-- The real world of `KE^eav` with key derivation: the eavesdropper sees the transcript and the
derived key `H (g ^ (a b))`. -/
noncomputable def kdfReal (H : G → K) (E : G → G → K → S → Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q × ZMod q × S)).map fun ω =>
    E (transcript g ω.1 ω.2.1).1 (transcript g ω.1 ω.2.1).2
      (H (aliceKey ω.1 (transcript g ω.1 ω.2.1).2)) ω.2.2

variable (q) in
/-- The random world of `KE^eav` with key derivation: a uniform key in `K`. -/
noncomputable def kdfRand (E : G → G → K → S → Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q × ZMod q × K × S)).map fun ω =>
    E (transcript g ω.1 ω.2.1).1 (transcript g ω.1 ω.2.1).2 ω.2.2.1 ω.2.2.2

variable (q) in
/-- The key-exchange advantage for the derived key, `|Pr[KE^eav = 1] - 1/2|`. -/
noncomputable def kdfAdvantage (H : G → K) (E : G → G → K → S → Bool) : ℝ :=
  guessAdvantage (bitGame fun b => if b then kdfRand q g E else kdfReal q g H E)

/-- The DDH distinguisher built from an eavesdropper on the derived key: it derives a key from
its third input. -/
def kdfDist (H : G → K) (E : G → G → K → S → Bool) : G → G → G → S → Bool :=
  fun X Y Z s => E X Y (H Z) s

omit [Fintype G] [Fintype K] [Nonempty K] in
/-- The real world with key derivation is the real world of `kdfDist H E`. -/
theorem kdfReal_eq_keReal (H : G → K) (E : G → G → K → S → Bool) :
    kdfReal q g H E = keReal q g (kdfDist H E) := rfl

/-- For a uniform KDF, the derived key from a uniform group element is a uniform key. -/
theorem kdfRand_eq_keRand {H : G → K} (hH : IsUniformKDF H) (E : G → G → K → S → Bool) :
    kdfRand q g E = keRand q g (kdfDist H E) := by
  rw [kdfRand, ← uniformOfFintype_map_third (A := ZMod q) (B := ZMod q) (S := S) hH,
    PMF.map_comp]
  rfl

/-- **Key derivation preserves eavesdropping security**: for a uniform KDF `H`, the advantage
against the derived key is exactly half the DDH advantage of `kdfDist H E`. -/
theorem kdfAdvantage_eq (hgen : ∀ x : G, x ∈ Subgroup.zpowers g) (hcard : Fintype.card G = q)
    {H : G → K} (hH : IsUniformKDF H) (E : G → G → K → S → Bool) :
    kdfAdvantage q g H E = ddhAdvantage q g (kdfDist H E) / 2 := by
  rw [kdfAdvantage, guessAdvantage_bitGame]
  change advantage (kdfRand q g E) (kdfReal q g H E) / 2 = _
  rw [kdfRand_eq_keRand g hH, kdfReal_eq_keReal, advantage_comm,
    advantage_keReal_keRand g hgen hcard]

end KDFSecurity

end Cslib.Crypto.PublicKey.DHSecurity
