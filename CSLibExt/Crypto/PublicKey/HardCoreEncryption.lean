/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.SemanticSecurity

/-!
# Public-key encryption from a hard-core predicate of a trapdoor permutation

Goldreich (*Foundations of Cryptography*, Vol. II, Construction 5.3.13) encrypts one bit `σ` with
a trapdoor permutation `p_α` and a hard-core predicate `b` of it: the ciphertext is
`(p_α(r), σ ⊕ b(r))` for a uniform `r` in the domain, and the owner of the trapdoor decrypts by
inverting `p_α`. Proposition 5.3.14: if `b` is hard-core, the scheme is secure. Together with the
Goldreich–Levin theorem (every one-way permutation has a hard-core predicate) this gives public-key
encryption from any trapdoor permutation (Theorem 5.3.15), the general form of Goldwasser and
Micali's probabilistic encryption.

Concrete form, for one fixed index distribution and a finite domain `D`:
* `scheme gen p inv b`: the scheme, with key pairs `(α, τ)` drawn from `gen`, the permutation
  `p α : D ≃ D`, the trapdoor inverse `inv τ`, and the predicate `b α`. `scheme_correct`: it is
  correct when `inv τ` inverts `p α` for every key pair in the support of `gen`.
* `hcExp`, `hcAdvantage`: the hard-core experiment in distinguishing form: tell
  `(α, p α x, b α x)` from `(α, p α x, ¬ b α x)` for uniform `x`. `predictGame`: the prediction
  form (Goldreich's Equation (5.9)): guess `b α x` from `(α, p α x)`.
* `indExp_scheme`: distinguishing encryptions of `0` and `1` is exactly the hard-core distinguishing
  experiment (the observation in the proof of Proposition 5.3.14).
* `winProb_predictGame_predictor` (**distinguishing implies predicting**, exact form): the
  predictor that guesses a random bit `c`, runs the distinguisher on `c` and keeps `c` exactly when
  it answers `1` predicts `b α x` with probability
  `1/2 + (Pr[D(b) = 1] - Pr[D(¬ b) = 1]) / 2`. This is the step that Goldreich's proof delegates to
  "the second proof of Theorem 3.4.1".
* `indAdvantage_eq_two_mul_predictAdvantage` (**Proposition 5.3.14, per adversary, exact
  form**, the security theorem): the advantage of a distinguisher between encryptions of `0` and
  `1` is twice the prediction advantage of the predictor built from it with one call.
* `half_le_of_forall_predict_le`: a hypothesis over all predictors is **vacuous against
  unbounded predictors**, because it forces `ε ≥ 1/2`. So no all-predictor security theorem is
  stated here; one needs a resource-bounded class of predictors that the reduction preserves.

**Scope.** No security parameter and no complexity bounds; the domain is a fixed finite type and
the index distribution `gen` is arbitrary. The Goldreich–Levin theorem itself is not used. The
per-adversary identity is the statement that transfers to bounded adversaries, because the
predictor makes one call to the distinguisher.

## References

* O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University
  Press, 2004, Section 5.3.4 (Construction 5.3.13, Proposition 5.3.14, Theorem 5.3.15, Equation
  (5.9)).
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.HardCoreEncryption

open Cslib.Crypto.Framework Cslib.Crypto.PublicKey.SemanticSecurity
open Cslib.Probability.PMF (uniformOfFintype)

variable {I T D : Type*} [Fintype D] [Nonempty D]

/-- **Encryption of one bit with a hard-core predicate** (Goldreich, *Foundations of
Cryptography*, Vol. II, Construction 5.3.13): with key pairs `(α, τ)` from `gen`, the permutation
`p α` of the finite domain `D`, the trapdoor inverse `inv τ` and the predicate `b α`, the bit `σ`
is encrypted as `(p α r, σ ⊕ b α r)` for a uniform `r`, and `(y, ς)` is decrypted as
`ς ⊕ b α (inv τ y)`. -/
noncomputable def scheme (gen : PMF (I × T)) (p : I → D ≃ D) (inv : T → D → D)
    (b : I → D → Bool) : PKEScheme Bool I (I × T) (D × Bool) where
  gen := gen.map fun k => (k.1, k)
  enc α σ := (uniformOfFintype D).map fun r => (p α r, xor σ (b α r))
  dec k c := some (xor c.2 (b k.1 (inv k.2 c.1)))

/-- **Correctness of encryption with a hard-core predicate**: if the trapdoor inverse `inv τ`
inverts `p α` for every key pair `(α, τ)` in the support of `gen`, every ciphertext decrypts to
its bit (the computation following Construction 5.3.13). -/
theorem scheme_correct {gen : PMF (I × T)} {p : I → D ≃ D} {inv : T → D → D} {b : I → D → Bool}
    (hinv : ∀ k ∈ gen.support, ∀ x, inv k.2 (p k.1 x) = x) : (scheme gen p inv b).Correct := by
  intro kp hkp σ c hc
  simp only [scheme, PMF.support_map, Set.mem_image] at hkp hc
  obtain ⟨k, hk, rfl⟩ := hkp
  obtain ⟨r, -, rfl⟩ := hc
  simp [scheme, hinv k hk r]

variable {R : Type*}

/-- **The hard-core experiment, distinguishing form**: draw a key pair `(α, τ)`, coins `r` and a
uniform `x`; the distinguisher `A` receives `α`, `p α x` and the bit `b α x` (`c = false`) or its
complement (`c = true`). -/
noncomputable def hcExp (gen : PMF (I × T)) (p : I → D ≃ D) (b : I → D → Bool) (coins : PMF R)
    (A : I → D × Bool → R → Bool) (c : Bool) : PMF Bool :=
  gen.bind fun k => coins.bind fun r =>
    (uniformOfFintype D).map fun x => A k.1 (p k.1 x, xor c (b k.1 x)) r

/-- **Hard-core distinguishing advantage**: how well `A` tells the hard-core bit from its
complement. -/
noncomputable def hcAdvantage (gen : PMF (I × T)) (p : I → D ≃ D) (b : I → D → Bool)
    (coins : PMF R) (A : I → D × Bool → R → Bool) : ℝ :=
  advantage (hcExp gen p b coins A false) (hcExp gen p b coins A true)

/-- **The hard-core prediction experiment** (Goldreich, *Foundations of Cryptography*, Vol. II,
Equation (5.9)): the predictor `P` receives `α` and `p α x` for a uniform `x` and wins when it
outputs `b α x`. -/
noncomputable def predictGame (gen : PMF (I × T)) (p : I → D ≃ D) (b : I → D → Bool)
    (coins : PMF R) (P : I → D → R → Bool) : PMF Bool :=
  gen.bind fun k => coins.bind fun r =>
    (uniformOfFintype D).map fun x => P k.1 (p k.1 x) r == b k.1 x

/-- **Distinguishing encryptions is distinguishing the hard-core bit**: for the scheme of
Construction 5.3.13, the indistinguishability experiment on the bit `σ` is the hard-core
experiment in world `σ` (proof of Goldreich's Proposition 5.3.14). -/
theorem indExp_scheme (gen : PMF (I × T)) (p : I → D ≃ D) (inv : T → D → D) (b : I → D → Bool)
    (coins : PMF R) (A : I → D × Bool → R → Bool) (σ : Bool) :
    indExp (scheme gen p inv b) coins A σ = hcExp gen p b coins A σ := by
  simp only [indExp, scheme, hcExp, PMF.bind_map, Function.comp_def, PMF.map_comp]

/-- **The predictor built from a distinguisher**: with coins `(r, c)`, run `A` on the bit `c` and
output `c` if `A` answers `1`, and `¬ c` otherwise. -/
def predictor (A : I → D × Bool → R → Bool) : I → D → R × Bool → Bool :=
  fun α y rc => if A α (y, rc.2) rc.1 then rc.2 else !rc.2

/-- **The predictor's success for one key and one coin**: with a fair coin `c`, the predictor
built from `A` wins with probability `1/2 + (Pr[A(b) = 1] - Pr[A(¬ b) = 1]) / 2`, the
probabilities being over a uniform `x`. -/
theorem winProb_inner (α : I) (q : D ≃ D) (bα : D → Bool) (A : I → D × Bool → R → Bool) (r : R) :
    winProb (fairCoin.bind fun c => (uniformOfFintype D).map fun x =>
        predictor A α (q x) (r, c) == bα x) =
      1 / 2 + (winProb ((uniformOfFintype D).map fun x => A α (q x, xor false (bα x)) r) -
        winProb ((uniformOfFintype D).map fun x => A α (q x, xor true (bα x)) r)) / 2 := by
  classical
  rw [winProb_bind]
  simp only [tsum_fintype, Fintype.sum_bool, fairCoin, Cslib.Probability.PMF.uniformOfFintype_apply,
    Fintype.card_bool, winProb_map_uniform]
  have hpt : ∀ x, ((if (predictor A α (q x) (r, true) == bα x) = true then 1 else 0 : ℕ) +
      (if (predictor A α (q x) (r, false) == bα x) = true then 1 else 0 : ℕ)) +
      (if A α (q x, xor true (bα x)) r = true then 1 else 0 : ℕ) =
      (if A α (q x, xor false (bα x)) r = true then 1 else 0 : ℕ) + 1 := by
    intro x
    cases hb : bα x <;> cases h1 : A α (q x, true) r <;> cases h0 : A α (q x, false) r <;>
      simp [predictor, h1, h0]
  have hsum := congrArg (fun f => ∑ x : D, f x) (funext hpt)
  simp only [Finset.sum_add_distrib, ← Finset.card_filter, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] at hsum
  have hD : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hsumR : ((Finset.univ.filter fun x => (predictor A α (q x) (r, true) == bα x) = true).card
      : ℝ) + (Finset.univ.filter fun x => (predictor A α (q x) (r, false) == bα x) = true).card +
      (Finset.univ.filter fun x => A α (q x, xor true (bα x)) r = true).card =
      (Finset.univ.filter fun x => A α (q x, xor false (bα x)) r = true).card + Fintype.card D := by
    exact_mod_cast hsum
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, Nat.cast_ofNat]
  field_simp
  linarith

/-- **Distinguishing implies predicting** (exact form): the predictor built from `A`, with a fair
extra coin, guesses the hard-core bit with probability
`1/2 + (Pr[A(b) = 1] - Pr[A(¬ b) = 1]) / 2`. -/
theorem winProb_predictGame_predictor (gen : PMF (I × T)) (p : I → D ≃ D) (b : I → D → Bool)
    (coins : PMF R) (A : I → D × Bool → R → Bool) :
    winProb (predictGame gen p b (coins.bind fun r => fairCoin.map fun c => (r, c))
        (predictor A)) =
      1 / 2 +
        (winProb (hcExp gen p b coins A false) - winProb (hcExp gen p b coins A true)) / 2 := by
  unfold predictGame hcExp
  refine winProb_bind_affine gen _ _ _ fun k => ?_
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine winProb_bind_affine coins _ _ _ fun r => ?_
  exact winProb_inner k.1 (p k.1) (b k.1) A r

/-- **The coins of the predictor** built from a distinguisher: the distinguisher's coins and a
fair bit. -/
noncomputable def predictorCoins (coins : PMF R) : PMF (R × Bool) :=
  coins.bind fun r => fairCoin.map fun c => (r, c)

/-- **Goldreich's Proposition 5.3.14, per adversary** (exact form): for the scheme of
Construction 5.3.13, the advantage of a distinguisher `A` between encryptions of `0` and `1` is
`2 |Pr[predictor A wins] - 1/2|`, twice the prediction advantage of the predictor built from `A`
with one call. So a distinguisher with advantage `ε` gives a predictor of the hard-core bit with
advantage `ε / 2`, and an efficient distinguisher an equally efficient predictor: this is the
security of encryption from a hard-core predicate. -/
theorem indAdvantage_eq_two_mul_predictAdvantage (gen : PMF (I × T)) (p : I → D ≃ D)
    (inv : T → D → D) (b : I → D → Bool) (coins : PMF R) (A : I → D × Bool → R → Bool) :
    indAdvantage (scheme gen p inv b) coins A false true =
      2 * |winProb (predictGame gen p b (predictorCoins coins) (predictor A)) - 1 / 2| := by
  rw [indAdvantage, indExp_scheme, indExp_scheme, advantage, predictorCoins,
    winProb_predictGame_predictor, add_sub_cancel_left, abs_div, abs_two]
  ring

/-- **Negating a distinguisher** complements its success probability in the hard-core
experiment. -/
theorem winProb_hcExp_not (gen : PMF (I × T)) (p : I → D ≃ D) (b : I → D → Bool)
    (coins : PMF R) (A : I → D × Bool → R → Bool) (c : Bool) :
    winProb (hcExp gen p b coins (fun α y r => !A α y r) c) =
      1 - winProb (hcExp gen p b coins A c) := by
  have : hcExp gen p b coins (fun α y r => !A α y r) c = (hcExp gen p b coins A c).map (!·) := by
    simp only [hcExp, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [this, ← toReal_apply_false, winProb, PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp

/-- **An unbounded predictor always wins**: the hypothesis "every predictor guesses the hard-core
bit with probability at most `1/2 + ε`" forces `ε ≥ 1/2`, since the predictor
`b α ((p α).symm y)` inverts the permutation. -/
theorem half_le_of_forall_predict_le (gen : PMF (I × T)) (p : I → D ≃ D) (b : I → D → Bool)
    (coins : PMF R) {ε : ℝ}
    (hpred : ∀ P : I → D → R × Bool → Bool,
      winProb (predictGame gen p b (predictorCoins coins) P) ≤ 1 / 2 + ε) :
    1 / 2 ≤ ε := by
  have h := hpred fun α y _ => b α ((p α).symm y)
  have hone : predictGame gen p b (predictorCoins coins) (fun α y _ => b α ((p α).symm y)) =
      PMF.pure true := by
    simp only [predictGame, Equiv.symm_apply_apply, BEq.rfl, PMF.bind_const]
    exact PMF.map_const _ true
  rw [hone, winProb_pure] at h
  simp at h
  linarith

end Cslib.Crypto.PublicKey.HardCoreEncryption
