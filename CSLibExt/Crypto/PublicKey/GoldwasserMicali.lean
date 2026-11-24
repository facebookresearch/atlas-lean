/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Games
public import CSLibExt.Crypto.PublicKey.SemanticSecurity
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Goldwasser–Micali probabilistic encryption

Goldwasser and Micali (STOC 1982, Section 4) encrypt one bit at a time modulo `N = p₁ p₂`. The
public key is `N` and a quadratic non-residue `y` modulo `N` with Jacobi symbol `+1`; the secret
key is the factorization. A bit `b` is encrypted as `x²` (`b = 0`) or `y x²` (`b = 1`) for a fresh
uniform unit `x`; the owner of the factorization decrypts by testing quadratic residuosity, which
by Euler's criterion and the Chinese remainder theorem is the test `c^((pᵢ - 1)/2) ≡ 1 (mod pᵢ)`
for `i = 1, 2` (their Lemma 2).

**Correctness.**
* `encryptBit y b x` is a square exactly when `b = false`, as soon as `y` is not a square
  (`isSquare_encryptBit_iff`).
* `isSquare_iff_euler` (Goldwasser and Micali, Lemma 2): for distinct primes `p`, `q` and a unit
  `c` modulo `p q`, `c` is a square if and only if `c^(p/2) = 1` in `ZMod p` and `c^(q/2) = 1`
  in `ZMod q` (`p / 2 = (p - 1)/2` for odd `p`).
* `decryptBit_encryptBit`: the trapdoor decryption `decryptBit p q`, which only computes these two
  powers, inverts encryption. `scheme_correct`: the scheme `scheme N kgen` is a correct framework
  `PKEScheme` (Katz and Lindell, Definition 11.1) for every key distribution whose keys are valid.

**Security, concrete form.** For a fixed modulus `N`, `qrExp kgen D b` is the quadratic-residuosity
distinguishing experiment: for a key `(y, (p, q))` from `kgen` the distinguisher `D` receives `y`
and either a uniform square `x²` (`b = false`) or `y x²` (`b = true`). Since `y` is a non-residue
with Jacobi symbol `+1`, `y x²` is a uniform element of the non-residues with Jacobi symbol `+1`
(this identification uses that the squares have index `2` in the Jacobi-`+1` subgroup; it is the
reason for the choice of `y` in Goldwasser and Micali, and it is **not** formalized here, so the
experiment is stated with `y x²` directly). `qrAdvantage` is its distinguishing advantage.
* `pubCpaAdvantage_eq_qrAdvantage` (**Goldwasser–Micali's main theorem for one bit, per
  adversary**, exact form): for every eavesdropper `A`,
  `pubCpaAdvantage (scheme N kgen) A = qrAdvantage kgen (reduction A) / 2`, where the reduction
  `reduction A` uses the challenge `z` as the ciphertext of the first challenge message (after
  multiplying by `y` when that message is `1`), and outputs `0` when the two messages coincide.
* `winProb_ssReal_le_qrAdvantage` (**semantic security for one bit, per adversary**): the success
  of any one adversary in computing a function of the plaintext bit exceeds that of a simulator
  that never sees the ciphertext by at most the residuosity advantage of one explicit
  distinguisher that calls the adversary once.
* `one_le_of_forall_qrAdvantage_le` and `not_indSecure_scheme`: a hypothesis over all
  distinguishers ("every distinguisher has residuosity advantage at most `ε`") is **vacuous against
  unbounded distinguishers**. In this concrete model every function counts, and for a key whose
  `y` is not a square the distinguisher that tests squareness has advantage `1`, so the hypothesis
  forces `ε ≥ 1`; indeed the scheme is not `IndSecure` for any `ε < 1`. So no all-distinguisher
  security theorem is stated here. The per-adversary statements are the ones that transfer to
  efficient adversaries.

**Messages of `ℓ` bits.** `schemeVec N kgen` encrypts each bit independently (`encryptVec`);
`schemeVec_correct`. `indExp_schemeVec_hybrid`: for two messages that differ exactly at position
`j`, the indistinguishability experiments are the two worlds of the residuosity experiment for
`hybridReduction D u j`, which encrypts the other bits itself and plants the challenge at `j`
(`uniform_map_update`: resampling one coordinate of a uniform vector keeps it uniform).
`indAdvantage_schemeVec_le` (**the hybrid argument**): the advantage of a distinguisher between
encryptions of `m` and `m'` is at most the sum over `j < ℓ` of the residuosity advantages of the
hybrid reductions between the hybrid messages `hybridMsg m m' j` and `hybridMsg m m' (j + 1)`;
`indAdvantage_schemeVec_le_mul` gives the factor `ℓ`.

This is the concrete form of Goldwasser and Micali's Theorem 3 (two "n-signatures" that a decision
function tells apart give a residuosity decider; the proof walks through adjacent signatures).

**Scope.** There is no security parameter: the asymptotic statements (Goldwasser and Micali's
Theorems 3-6, under their quadratic residuosity assumption on circuits) are not claimed, and
neither is the
random self-reducibility of quadratic residuosity (their Theorems 1 and 2). Key generation is an
arbitrary distribution `kgen` on keys `(y, (p, q))` for the fixed modulus `N`.

## References

* S. Goldwasser and S. Micali, *Probabilistic encryption & how to play mental poker keeping
  secret all partial information*, Proc. 14th ACM STOC (1982), 365-377, Sections 3 and 4
  (Lemma 2). The journal version is *Probabilistic encryption*, J. Comput. System Sci. 28 (1984),
  270-299.
* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Definitions 11.1 and 11.2 (the framework's public-key schemes and `PubK^eav`).
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.GoldwasserMicali

open Cslib.Crypto.Framework
open Cslib.Probability.PMF (uniformOfFintype uniformOfFintype_map_equiv)

/-! ### Encryption of one bit and its residuosity -/

section Bit

variable {M : Type*} [CommGroup M]

/-- **Goldwasser–Micali encryption of one bit** (Goldwasser and Micali, STOC 1982, Section 4):
with the public non-residue `y` and the randomness `x`, the bit `false` is encrypted as `x ^ 2`
and the bit `true` as `y * x ^ 2`. Stated in any commutative group; the scheme uses the units
modulo `N`. -/
def encryptBit (y : M) (b : Bool) (x : M) : M := if b then y * x ^ 2 else x ^ 2

/-- **Encryptions of `0` are squares.** -/
theorem isSquare_encryptBit_false (y x : M) : IsSquare (encryptBit y false x) :=
  ⟨x, by simp [encryptBit, sq]⟩

/-- **Encryptions of `1` are non-squares.** If `y` is not a square, an encryption of `true` is not
a square: `y x² = r²` would give
`y = (r x⁻¹)²`. -/
theorem not_isSquare_encryptBit_true {y : M} (hy : ¬ IsSquare y) (x : M) :
    ¬ IsSquare (encryptBit y true x) := by
  rintro ⟨r, hr⟩
  refine hy ⟨r * x⁻¹, ?_⟩
  simp only [encryptBit, ite_true] at hr
  calc y = y * x ^ 2 * (x⁻¹ * x⁻¹) := by group
    _ = r * x⁻¹ * (r * x⁻¹) := by rw [hr, mul_mul_mul_comm]

/-- **Residuosity reveals the bit.** If `y` is not a square, the encryption of `b` is a square
exactly when `b = false`. -/
theorem isSquare_encryptBit_iff {y : M} (hy : ¬ IsSquare y) (b : Bool) (x : M) :
    IsSquare (encryptBit y b x) ↔ b = false := by
  cases b
  · simpa using isSquare_encryptBit_false y x
  · simpa using not_isSquare_encryptBit_true hy x

end Bit

/-! ### Deciding residuosity with the factorization -/

/-- **Square units.** In a commutative monoid, a unit is the square of a unit as soon as it is a
square. -/
theorem isSquare_units_iff {R : Type*} [CommMonoid R] (c : Rˣ) :
    IsSquare c ↔ IsSquare (c : R) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by simp⟩
  · rintro ⟨r, hr⟩
    have hu : IsUnit r := isUnit_of_mul_isUnit_left (hr ▸ c.isUnit)
    refine ⟨hu.unit, Units.ext ?_⟩
    simp [hr]

/-- **Squares in a product**: a pair is a square exactly when both coordinates are. -/
theorem isSquare_prod_iff {R S : Type*} [Mul R] [Mul S] (a : R × S) :
    IsSquare a ↔ IsSquare a.1 ∧ IsSquare a.2 := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨⟨r.1, rfl⟩, ⟨r.2, rfl⟩⟩
  · rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
    exact ⟨(r, s), Prod.ext hr hs⟩

/-- **Goldwasser–Micali's Lemma 2** (STOC 1982, Section 4): for distinct primes `p` and `q`, a unit
`c` modulo `p q` is a quadratic residue if and only if `c ^ (p / 2) = 1` modulo `p` and
`c ^ (q / 2) = 1` modulo `q` (Euler's criterion in each factor, glued by the Chinese remainder
theorem). -/
theorem isSquare_iff_euler {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (c : (ZMod (p * q))ˣ) :
    IsSquare c ↔ ((c : ZMod (p * q)).cast : ZMod p) ^ (p / 2) = 1 ∧
      ((c : ZMod (p * q)).cast : ZMod q) ^ (q / 2) = 1 := by
  have hcop : p.Coprime q := (Nat.coprime_primes hp.out hq.out).mpr hpq
  set e := ZMod.chineseRemainder hcop
  have he : e (c : ZMod (p * q)) = (((c : ZMod (p * q)).cast : ZMod p),
      ((c : ZMod (p * q)).cast : ZMod q)) := by
    ext <;> simp [e, ZMod.chineseRemainder, ZMod.castHom_apply]
  have hsq : IsSquare (c : ZMod (p * q)) ↔ IsSquare (e (c : ZMod (p * q))) := by
    constructor
    · exact fun h => h.map e
    · intro h
      simpa using h.map e.symm
  have hunit : IsUnit (e (c : ZMod (p * q))) := c.isUnit.map e
  rw [he] at hunit
  have h₁ : ((c : ZMod (p * q)).cast : ZMod p) ≠ 0 := (Prod.isUnit_iff.mp hunit).1.ne_zero
  have h₂ : ((c : ZMod (p * q)).cast : ZMod q) ≠ 0 := (Prod.isUnit_iff.mp hunit).2.ne_zero
  rw [isSquare_units_iff, hsq, he, isSquare_prod_iff, ZMod.euler_criterion p h₁,
    ZMod.euler_criterion q h₂]

/-- **Goldwasser–Micali trapdoor decryption of one bit**: with the factors `p` and `q`, output
`false` when `c ^ (p / 2) = 1` modulo `p` and `c ^ (q / 2) = 1` modulo `q` (that is, when `c` is a
quadratic residue), and `true` otherwise. Computable: it only takes two modular powers. -/
def decryptBit {N : ℕ} (p q : ℕ) (c : ZMod N) : Bool :=
  !decide ((c.cast : ZMod p) ^ (p / 2) = 1 ∧ (c.cast : ZMod q) ^ (q / 2) = 1)

/-- A **valid Goldwasser–Micali key** for the modulus `N`: a pair `(y, (p, q))` of a unit `y`
modulo `N` that is not a square and of distinct primes `p`, `q` with `p q = N`. (Goldwasser and
Micali also take `y` with Jacobi symbol `+1`, so that `y` does not reveal itself as a non-residue;
correctness does not need it.) -/
def IsKey (N : ℕ) (k : (ZMod N)ˣ × ℕ × ℕ) : Prop :=
  k.2.1.Prime ∧ k.2.2.Prime ∧ k.2.1 ≠ k.2.2 ∧ k.2.1 * k.2.2 = N ∧ ¬ IsSquare k.1

/-- **Correctness of Goldwasser–Micali encryption of one bit** (STOC 1982, Section 4): for a valid
key `(y, (p, q))` and any randomness `x`, trapdoor decryption recovers the bit. -/
theorem decryptBit_encryptBit {N : ℕ} {k : (ZMod N)ˣ × ℕ × ℕ} (hk : IsKey N k) (b : Bool)
    (x : (ZMod N)ˣ) :
    decryptBit k.2.1 k.2.2 ((encryptBit k.1 b x : (ZMod N)ˣ) : ZMod N) = b := by
  obtain ⟨y, p, q⟩ := k
  simp only [IsKey] at hk
  obtain ⟨hp, hq, hpq, hN, hy⟩ := hk
  subst hN
  have := Fact.mk hp
  have := Fact.mk hq
  have h := (isSquare_iff_euler hpq (encryptBit y b x)).symm.trans (isSquare_encryptBit_iff hy b x)
  unfold decryptBit
  cases b
  · simp_all
  · simp_all
    tauto

/-! ### The scheme and its security -/

variable (N : ℕ) [NeZero N]

/-- **The Goldwasser–Micali scheme for one-bit messages** as a framework `PKEScheme`, for the fixed
modulus `N` and a key distribution `kgen` on pairs `(y, (p, q))`: the public key is `y`, the
secret key is `(p, q)`, encryption samples a uniform unit `x` and outputs `encryptBit y b x`, and
decryption is `decryptBit p q`. -/
noncomputable def scheme (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ)) :
    PKEScheme Bool (ZMod N)ˣ (ℕ × ℕ) (ZMod N)ˣ where
  gen := kgen
  enc y b := (uniformOfFintype (ZMod N)ˣ).map (encryptBit y b)
  dec sk c := some (decryptBit sk.1 sk.2 (c : ZMod N))

/-- **Correctness of the Goldwasser–Micali scheme**: if every key in the support of `kgen` is
valid, the scheme is correct (Katz and Lindell, Definition 11.1). -/
theorem scheme_correct {kgen : PMF ((ZMod N)ˣ × ℕ × ℕ)} (hkgen : ∀ k ∈ kgen.support, IsKey N k) :
    (scheme N kgen).Correct := by
  intro k hk b c hc
  simp only [scheme, PMF.support_map, Set.mem_image] at hc
  obtain ⟨x, -, rfl⟩ := hc
  exact congrArg some (decryptBit_encryptBit (hkgen k hk) b x)

variable {N}

/-- **The residuosity experiment** for the modulus `N` (Goldwasser and Micali, Section
3.2, as a concrete experiment): for a key `(y, (p, q))` from `kgen` and the distinguisher's coins
`r`, the distinguisher `D` receives `y` and either a uniform square `x ^ 2` (`b = false`) or
`y * x ^ 2` (`b = true`), a uniform non-residue with Jacobi symbol `+1` when `y` is one. -/
noncomputable def qrExp {R : Type*} (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ)) (coins : PMF R)
    (D : (ZMod N)ˣ → (ZMod N)ˣ → R → Bool) (b : Bool) : PMF Bool :=
  kgen.bind fun k => coins.bind fun r =>
    (uniformOfFintype (ZMod N)ˣ).map fun x => D k.1 (if b then k.1 * x ^ 2 else x ^ 2) r

/-- **Residuosity advantage** of a distinguisher: how well it tells a uniform square
from `y` times a uniform square. -/
noncomputable def qrAdvantage {R : Type*} (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ)) (coins : PMF R)
    (D : (ZMod N)ˣ → (ZMod N)ˣ → R → Bool) : ℝ :=
  advantage (qrExp kgen coins D true) (qrExp kgen coins D false)

/-- **The reduction from Goldwasser–Micali to the residuosity experiment.** From an eavesdropper
`A`: on the public key `y`, the challenge `z` and coins `r`, let `(m₀, m₁)` be `A`'s messages; if
they are equal output `false`, otherwise give `A` the ciphertext `z` (if `m₀ = false`) or `y z` (if
`m₀ = true`) and output its guess. A square `z` is then an encryption of `m₀`, and `z = y x²` an
encryption of `m₁ = !m₀`. -/
def reduction {R : Type*} (A : PubCPAAdversary Bool (ZMod N)ˣ (ZMod N)ˣ R) :
    (ZMod N)ˣ → (ZMod N)ˣ → R → Bool := fun y z r =>
  if (A.choose y r).1 = (A.choose y r).2 then false
  else A.guess y (if (A.choose y r).1 then y * z else z) r

/-- **The reduction for one key and one coin.** The two worlds of the
residuosity experiment and the two worlds of `PubK^eav` satisfy
`Pr[QR₁ = 1] + Pr[PubK₀ = 1] = Pr[QR₀ = 1] + Pr[PubK₁ = 1]`. -/
theorem inner_identity {R : Type*} (A : PubCPAAdversary Bool (ZMod N)ˣ (ZMod N)ˣ R)
    (y : (ZMod N)ˣ) (r : R) :
    ((uniformOfFintype (ZMod N)ˣ).map fun x => reduction A y (y * x ^ 2) r) true +
      ((uniformOfFintype (ZMod N)ˣ).map fun x =>
        A.guess y (encryptBit y (pick (A.choose y r) false) x) r) true =
    ((uniformOfFintype (ZMod N)ˣ).map fun x => reduction A y (x ^ 2) r) true +
      ((uniformOfFintype (ZMod N)ˣ).map fun x =>
        A.guess y (encryptBit y (pick (A.choose y r) true) x) r) true := by
  rcases hm : A.choose y r with ⟨m₀, m₁⟩
  by_cases h : m₀ = m₁
  · subst h
    simp [reduction, hm, pick]
  · have hm₁ : m₁ = !m₀ := by cases m₀ <;> cases m₁ <;> simp_all
    subst hm₁
    have hred : ∀ z, reduction A y z r = A.guess y (if m₀ then y * z else z) r := by
      intro z; simp [reduction, hm, h]
    simp only [hred, pick]
    cases m₀
    · simp [encryptBit, add_comm]
    · -- `y * (y * x ^ 2) = (y * x) ^ 2`, and `x ↦ y * x` preserves the uniform distribution
      have hshift : ((uniformOfFintype (ZMod N)ˣ).map fun x =>
          A.guess y (y * (y * x ^ 2)) r) =
          (uniformOfFintype (ZMod N)ˣ).map fun x => A.guess y (x ^ 2) r := by
        conv_rhs => rw [← uniformOfFintype_map_equiv (Equiv.mulLeft y)]
        rw [PMF.map_comp]
        congr 1
        funext x
        simp only [Function.comp, Equiv.coe_mulLeft]
        rw [mul_pow, ← mul_assoc, ← sq]
      simp [encryptBit, hshift, add_comm]

/-- **Goldwasser–Micali's main theorem for one bit, per adversary** (exact concrete form;
Goldwasser and Micali, STOC 1982, Section 4 and Theorem 3, for one bit): for every eavesdropper
`A`, the `PubK^eav` advantage of `A` against `scheme N kgen` is half the advantage of the
distinguisher `reduction A` (one call to `A`) in the residuosity experiment `qrExp`. So an
eavesdropper with guessing advantage `ε` gives a distinguisher of `x²` from `y x²` with advantage
`2 ε`, and an efficient eavesdropper an efficient distinguisher. `qrExp` gives the distinguisher
the key element `y`; its identification with the standard problem (uniform residues against
uniform non-residues of Jacobi symbol `+1`) is not formalized. -/
theorem pubCpaAdvantage_eq_qrAdvantage {R : Type*} (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ))
    (A : PubCPAAdversary Bool (ZMod N)ˣ (ZMod N)ˣ R) :
    pubCpaAdvantage (scheme N kgen) A = qrAdvantage kgen A.coins (reduction A) / 2 := by
  rw [pubCpaAdvantage_eq, qrAdvantage]
  congr 1
  have key : (qrExp kgen A.coins (reduction A) true) true +
      (pubCpaExp (scheme N kgen) A false) true =
      (qrExp kgen A.coins (reduction A) false) true +
      (pubCpaExp (scheme N kgen) A true) true := by
    unfold qrExp pubCpaExp
    refine apply_true_bind_add_eq _ _ _ _ _ fun k =>
      apply_true_bind_add_eq _ _ _ _ _ fun r => ?_
    simp only [scheme, PMF.map_comp, Function.comp_def, ite_true, Bool.false_eq_true, ite_false]
    exact inner_identity A k.1 r
  have hfin : ∀ G : PMF Bool, G true ≠ ⊤ := fun G => G.apply_ne_top _
  have hreal := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_add (hfin _) (hfin _), ENNReal.toReal_add (hfin _) (hfin _)] at hreal
  simp only [advantage, winProb]
  congr 1
  linarith

/-- **Residuosity bounds transfer to Goldwasser–Micali, per adversary.** A bound `ε` on the
advantage of `reduction A` in the residuosity experiment `qrExp` bounds the `PubK^eav` advantage of
`A` against the Goldwasser–Micali scheme by `ε / 2`. -/
theorem pubCpaAdvantage_le {R : Type*} (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ))
    (A : PubCPAAdversary Bool (ZMod N)ˣ (ZMod N)ˣ R) {ε : ℝ}
    (hε : qrAdvantage kgen A.coins (reduction A) ≤ ε) :
    pubCpaAdvantage (scheme N kgen) A ≤ ε / 2 := by
  rw [pubCpaAdvantage_eq_qrAdvantage]
  linarith

/-- **Distinguishing Goldwasser–Micali ciphertexts is deciding residuosity.** For one-bit messages,
the indistinguishability experiment of the Goldwasser–Micali scheme on
the message `b` is the quadratic-residuosity experiment in world `b`. -/
theorem indExp_scheme {R : Type*} (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ)) (coins : PMF R)
    (D : (ZMod N)ˣ → (ZMod N)ˣ → R → Bool) (b : Bool) :
    SemanticSecurity.indExp (scheme N kgen) coins D b = qrExp kgen coins D b := by
  simp only [SemanticSecurity.indExp, scheme, qrExp, PMF.map_comp, Function.comp_def, encryptBit]

/-- **An unbounded distinguisher decides residuosity**: for a key whose `y` is not a square, the
distinguisher that tests whether its challenge is a square has advantage `1` in the residuosity
experiment, so the hypothesis "every distinguisher has residuosity advantage at most `ε`" forces
`ε ≥ 1`. -/
theorem one_le_of_forall_qrAdvantage_le {R : Type*} (k : (ZMod N)ˣ × ℕ × ℕ) (hy : ¬ IsSquare k.1)
    (coins : PMF R) {ε : ℝ}
    (hqr : ∀ D : (ZMod N)ˣ → (ZMod N)ˣ → R → Bool, qrAdvantage (PMF.pure k) coins D ≤ ε) :
    1 ≤ ε := by
  classical
  have h := hqr fun _ z _ => decide (¬ IsSquare z)
  have h1 : qrExp (PMF.pure k) coins (fun _ z _ => decide (¬ IsSquare z)) true = PMF.pure true := by
    simp only [qrExp, PMF.pure_bind, ite_true]
    have : (fun x : (ZMod N)ˣ => decide (¬ IsSquare (k.1 * x ^ 2))) = fun _ => true := by
      funext x
      simpa [encryptBit] using not_isSquare_encryptBit_true hy x
    rw [this, show ((uniformOfFintype (ZMod N)ˣ).map fun _ => true) = PMF.pure true from
      PMF.map_const _ true, PMF.bind_const]
  have h0 : qrExp (PMF.pure k) coins (fun _ z _ => decide (¬ IsSquare z)) false =
      PMF.pure false := by
    simp only [qrExp, PMF.pure_bind, Bool.false_eq_true, ite_false]
    have : (fun x : (ZMod N)ˣ => decide (¬ IsSquare (x ^ 2))) = fun _ => false := by
      funext x
      simpa [encryptBit] using isSquare_encryptBit_false k.1 x
    rw [this, show ((uniformOfFintype (ZMod N)ˣ).map fun _ => false) = PMF.pure false from
      PMF.map_const _ false, PMF.bind_const]
  rw [qrAdvantage, h1, h0, advantage, winProb_pure, winProb_pure] at h
  norm_num at h
  exact h

/-- **The one-bit Goldwasser–Micali scheme is not indistinguishable against unbounded
distinguishers**: for the point key distribution on a key whose `y` is not a square, `IndSecure`
fails for every error `ε < 1` (an instance of `SemanticSecurity.not_indSecure_of_correct`). -/
theorem not_indSecure_scheme {R : Type*} (k : (ZMod N)ˣ × ℕ × ℕ) (hy : ¬ IsSquare k.1)
    (coins : PMF R) {ε : ℝ} (hε : ε < 1) :
    ¬ SemanticSecurity.IndSecure (scheme N (PMF.pure k)) (fun _ => 0) coins ε := by
  intro hS
  have : 1 ≤ ε := one_le_of_forall_qrAdvantage_le k hy coins fun D => by
    have := hS D true false rfl
    rwa [SemanticSecurity.indAdvantage, indExp_scheme, indExp_scheme] at this
  linarith

/-- **Semantic security of Goldwasser–Micali for one bit, per adversary** (concrete form):
for every adversary `A`, plaintext distribution `X`, information `h` and target `f`, `A` computes
`f` of the plaintext bit at most `ε` more often than the simulator of Goldreich's Proposition 5.2.6
(which runs `A` on an encryption of `0`), where `ε` is the quadratic-residuosity advantage of the
single distinguisher `ssDistinguisher A h f true`, which calls `A` once. This is the form that
transfers to efficient adversaries. -/
theorem winProb_ssReal_le_qrAdvantage {R H T : Type*} [DecidableEq T]
    (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ)) (coins : PMF R)
    (A : (ZMod N)ˣ → (ZMod N)ˣ → H → R → T) (X : PMF Bool) (h : Bool → H) (f : Bool → T) :
    winProb (SemanticSecurity.ssReal (scheme N kgen) coins A X h f) ≤
      winProb (SemanticSecurity.ssIdeal (fun _ => 0)
        (SemanticSecurity.simulator (scheme N kgen) coins (fun _ => false) A) X h f) +
        qrAdvantage kgen coins (SemanticSecurity.ssDistinguisher A h f true) := by
  refine SemanticSecurity.winProb_ssReal_le _ _ _ _ A X h f (advantage_nonneg _ _) fun x _ => ?_
  rw [SemanticSecurity.indAdvantage, indExp_scheme, indExp_scheme]
  cases x
  · rw [advantage_self]
    exact advantage_nonneg _ _
  · exact le_of_eq (by rw [qrAdvantage])

/-! ### Messages of several bits -/

section MultiBit

variable {ℓ : ℕ}

/-- **Bitwise Goldwasser–Micali encryption** of an `ℓ`-bit message `m` with randomness
`xs : Fin ℓ → (ZMod N)ˣ`: the `i`-th ciphertext component is `encryptBit y (m i) (xs i)`. -/
def encryptVec (y : (ZMod N)ˣ) (m : Fin ℓ → Bool) (xs : Fin ℓ → (ZMod N)ˣ) :
    Fin ℓ → (ZMod N)ˣ :=
  fun i => encryptBit y (m i) (xs i)

/-- **The Goldwasser–Micali scheme for `ℓ`-bit messages** (Goldwasser and Micali, STOC 1982,
Section 4): each bit is encrypted independently with fresh uniform randomness, and decrypted with
`decryptBit`. -/
noncomputable def schemeVec (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ)) :
    PKEScheme (Fin ℓ → Bool) (ZMod N)ˣ (ℕ × ℕ) (Fin ℓ → (ZMod N)ˣ) where
  gen := kgen
  enc y m := (uniformOfFintype (Fin ℓ → (ZMod N)ˣ)).map (encryptVec y m)
  dec sk c := some fun i => decryptBit sk.1 sk.2 (c i : ZMod N)

/-- **Correctness of bitwise Goldwasser–Micali encryption**: if every key in the support of `kgen`
is valid, the `ℓ`-bit scheme is correct. -/
theorem schemeVec_correct {kgen : PMF ((ZMod N)ˣ × ℕ × ℕ)}
    (hkgen : ∀ k ∈ kgen.support, IsKey N k) : (schemeVec (ℓ := ℓ) kgen).Correct := by
  intro k hk m c hc
  simp only [schemeVec, PMF.support_map, Set.mem_image] at hc
  obtain ⟨xs, -, rfl⟩ := hc
  exact congrArg some (funext fun i => decryptBit_encryptBit (hkgen k hk) (m i) (xs i))

/-- **Resampling one coordinate of a uniform vector**: drawing a uniform vector and replacing its
`j`-th coordinate by an independent uniform value gives a uniform vector. -/
theorem uniform_map_update (j : Fin ℓ) :
    ((uniformOfFintype (Fin ℓ → (ZMod N)ˣ)).bind fun xs =>
      (uniformOfFintype (ZMod N)ˣ).map fun x => Function.update xs j x) =
    uniformOfFintype (Fin ℓ → (ZMod N)ˣ) := by
  classical
  let e : (Fin ℓ → (ZMod N)ˣ) × (ZMod N)ˣ ≃ (Fin ℓ → (ZMod N)ˣ) × (ZMod N)ˣ :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have h := Cslib.Probability.PMF.uniformOfFintype_prod (Fin ℓ → (ZMod N)ˣ) (ZMod N)ˣ
  have h2 : (uniformOfFintype ((Fin ℓ → (ZMod N)ˣ) × (ZMod N)ˣ)).map Prod.fst =
      uniformOfFintype (Fin ℓ → (ZMod N)ˣ) := by
    have hc : ∀ a : Fin ℓ → (ZMod N)ˣ,
        (uniformOfFintype (ZMod N)ˣ).map (fun _ => a) = PMF.pure a := fun a =>
      PMF.map_const _ a
    rw [← h, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, hc, PMF.bind_pure]
  conv_rhs => rw [← h2, ← uniformOfFintype_map_equiv e, PMF.map_comp, ← h, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, e, Equiv.coe_fn_mk]

omit [NeZero N] in
/-- **Encrypting with updated randomness**: changing the `j`-th randomness changes only the
`j`-th ciphertext component. -/
theorem encryptVec_update (y : (ZMod N)ˣ) (m : Fin ℓ → Bool) (xs : Fin ℓ → (ZMod N)ˣ)
    (j : Fin ℓ) (x : (ZMod N)ˣ) :
    encryptVec y m (Function.update xs j x) =
      Function.update (encryptVec y m xs) j (encryptBit y (m j) x) := by
  funext i
  by_cases h : i = j
  · subst h; simp [encryptVec]
  · simp [encryptVec, Function.update_of_ne h]

/-- **The hybrid reduction at position `j`**: from a distinguisher `D` for `ℓ`-bit ciphertexts and
a message `u`, on the public key `y`, a residuosity challenge `z` and coins `(r, xs)`, encrypt `u`
with randomness `xs`, replace the `j`-th component by `z` (if `u j = false`) or `y z` (if
`u j = true`), and run `D`. -/
def hybridReduction {R : Type*} (D : (ZMod N)ˣ → (Fin ℓ → (ZMod N)ˣ) → R → Bool)
    (u : Fin ℓ → Bool) (j : Fin ℓ) :
    (ZMod N)ˣ → (ZMod N)ˣ → R × (Fin ℓ → (ZMod N)ˣ) → Bool := fun y z rs =>
  D y (Function.update (encryptVec y u rs.2) j (if u j then y * z else z)) rs.1

/-- **The coins of the hybrid reduction**: the distinguisher's coins and a uniform vector. -/
noncomputable def hybridCoins {R : Type*} (coins : PMF R) : PMF (R × (Fin ℓ → (ZMod N)ˣ)) :=
  coins.bind fun r => (uniformOfFintype (Fin ℓ → (ZMod N)ˣ)).map fun xs => (r, xs)

/-- **The `ℓ`-bit experiment with one coordinate resampled**: the indistinguishability experiment
of the `ℓ`-bit scheme, with the `j`-th randomness drawn separately. -/
theorem indExp_schemeVec_eq {R : Type*} (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ)) (coins : PMF R)
    (D : (ZMod N)ˣ → (Fin ℓ → (ZMod N)ˣ) → R → Bool) (w : Fin ℓ → Bool) (j : Fin ℓ) :
    SemanticSecurity.indExp (schemeVec kgen) coins D w =
      kgen.bind fun k => coins.bind fun r =>
        (uniformOfFintype (Fin ℓ → (ZMod N)ˣ)).bind fun xs =>
          (uniformOfFintype (ZMod N)ˣ).map fun x =>
            D k.1 (Function.update (encryptVec k.1 w xs) j (encryptBit k.1 (w j) x)) r := by
  simp only [SemanticSecurity.indExp, schemeVec]
  congr 1; funext k; congr 1; funext r
  conv_lhs => rw [← uniform_map_update j]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, encryptVec_update]

/-- **One hybrid step**: if the messages `u` and `v` differ exactly at position `j`, the
indistinguishability experiments on `u` and on `v` are the two worlds of the residuosity
experiment for `hybridReduction D u j`. -/
theorem indExp_schemeVec_hybrid {R : Type*} (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ)) (coins : PMF R)
    (D : (ZMod N)ˣ → (Fin ℓ → (ZMod N)ˣ) → R → Bool) {u v : Fin ℓ → Bool} {j : Fin ℓ}
    (hj : v j = !u j) (hne : ∀ i, i ≠ j → u i = v i) :
    SemanticSecurity.indExp (schemeVec kgen) coins D u =
        qrExp kgen (hybridCoins coins) (hybridReduction D u j) false ∧
      SemanticSecurity.indExp (schemeVec kgen) coins D v =
        qrExp kgen (hybridCoins coins) (hybridReduction D u j) true := by
  have hvec : ∀ (y : (ZMod N)ˣ) (xs : Fin ℓ → (ZMod N)ˣ), Function.update (encryptVec y v xs) j =
      Function.update (encryptVec y u xs) j := by
    intro y xs
    funext w i
    by_cases h : i = j
    · subst h; simp
    · simp [Function.update_of_ne h, encryptVec, hne i h]
  constructor
  · rw [indExp_schemeVec_eq _ _ _ _ j]
    simp only [qrExp, hybridCoins, hybridReduction, PMF.bind_bind, PMF.bind_map,
      Function.comp_def, ite_false, Bool.false_eq_true]
    rfl
  · rw [indExp_schemeVec_eq _ _ _ _ j]
    simp only [qrExp, hybridCoins, hybridReduction, PMF.bind_bind, PMF.bind_map,
      Function.comp_def, ite_true, hvec]
    congr 1; funext k; congr 1; funext r; congr 1; funext xs
    cases huj : u j
    · simp [huj] at hj
      simp [hj, encryptBit]
    · simp [huj] at hj
      simp only [hj, encryptBit, Bool.false_eq_true, ite_false, ite_true]
      conv_lhs => rw [← uniformOfFintype_map_equiv (Equiv.mulLeft k.1)]
      rw [PMF.map_comp]
      congr 1
      funext x
      simp only [Function.comp, Equiv.coe_mulLeft]
      rw [mul_pow, ← mul_assoc, ← sq]

/-- **The `j`-th hybrid message** between `m` and `m'`: the bits of `m'` before position `j` and
the bits of `m` from position `j` on. -/
def hybridMsg (m m' : Fin ℓ → Bool) (j : ℕ) : Fin ℓ → Bool :=
  fun i => if i.val < j then m' i else m i

/-- **The hybrid argument for bitwise Goldwasser–Micali encryption** (Goldwasser and Micali,
STOC 1982, Section 4, Theorem 3, concrete form): for every distinguisher `D` and all `ℓ`-bit
messages `m`, `m'`, the advantage of `D` between encryptions of `m` and of `m'` is at most the
sum over the positions `j` of the quadratic-residuosity advantages of the hybrid reductions
`hybridReduction D (hybridMsg m m' j) j`, each of which calls `D` once. -/
theorem indAdvantage_schemeVec_le {R : Type*} (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ)) (coins : PMF R)
    (D : (ZMod N)ˣ → (Fin ℓ → (ZMod N)ˣ) → R → Bool) (m m' : Fin ℓ → Bool) :
    SemanticSecurity.indAdvantage (schemeVec kgen) coins D m m' ≤
      ∑ j : Fin ℓ,
        qrAdvantage kgen (hybridCoins coins) (hybridReduction D (hybridMsg m m' j) j) := by
  set H : ℕ → PMF Bool := fun j =>
    SemanticSecurity.indExp (schemeVec kgen) coins D (hybridMsg m m' j) with hH
  have h0 : hybridMsg m m' 0 = m := by funext i; simp [hybridMsg]
  have hℓ : hybridMsg m m' ℓ = m' := by funext i; simp [hybridMsg, i.isLt]
  have hsum := advantage_le_sum H ℓ
  simp only [hH, h0, hℓ] at hsum
  rw [SemanticSecurity.indAdvantage]
  refine hsum.trans ?_
  rw [Finset.sum_range (fun j => advantage (H j) (H (j + 1)))]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [hH]
  by_cases hj : m j = m' j
  · have : hybridMsg m m' (j + 1) = hybridMsg m m' j := by
      funext i
      simp only [hybridMsg]
      by_cases hij : i = j
      · subst hij; simp [hj]
      · have : i.val < j.val + 1 ↔ i.val < j.val := by
          have : i.val ≠ j.val := fun h => hij (Fin.ext h)
          omega
        simp [this]
    rw [this, advantage_self]
    exact advantage_nonneg _ _
  · have hv : hybridMsg m m' (j + 1) j = !hybridMsg m m' j j := by
      simp only [hybridMsg, lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
      cases h₁ : m j <;> cases h₂ : m' j <;> simp_all
    have hne : ∀ i, i ≠ j → hybridMsg m m' j i = hybridMsg m m' (j + 1) i := by
      intro i hij
      have : i.val < j.val + 1 ↔ i.val < j.val := by
        have : i.val ≠ j.val := fun h => hij (Fin.ext h)
        omega
      simp [hybridMsg, this]
    obtain ⟨h₁, h₂⟩ := indExp_schemeVec_hybrid kgen coins D hv hne
    rw [h₁, h₂, qrAdvantage, advantage_comm]

/-- **Bitwise Goldwasser–Micali loses a factor `ℓ`**: if each of the `ℓ` hybrid reductions built
from a distinguisher `D` has advantage at most `ε` in the residuosity experiment, then `D` has
advantage at most `ℓ ε` between encryptions of the two `ℓ`-bit messages. -/
theorem indAdvantage_schemeVec_le_mul {R : Type*} (kgen : PMF ((ZMod N)ˣ × ℕ × ℕ))
    (coins : PMF R) (D : (ZMod N)ˣ → (Fin ℓ → (ZMod N)ˣ) → R → Bool) (m m' : Fin ℓ → Bool)
    {ε : ℝ}
    (hε : ∀ j : Fin ℓ,
      qrAdvantage kgen (hybridCoins coins) (hybridReduction D (hybridMsg m m' j) j) ≤ ε) :
    SemanticSecurity.indAdvantage (schemeVec kgen) coins D m m' ≤ ℓ * ε := by
  refine (indAdvantage_schemeVec_le kgen coins D m m').trans ?_
  calc ∑ j : Fin ℓ, qrAdvantage kgen (hybridCoins coins) (hybridReduction D (hybridMsg m m' j) j)
      ≤ ∑ _j : Fin ℓ, ε := Finset.sum_le_sum fun j _ => hε j
    _ = ℓ * ε := by simp

end MultiBit

end Cslib.Crypto.PublicKey.GoldwasserMicali
