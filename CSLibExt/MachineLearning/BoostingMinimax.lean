/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ZeroSumMinimax

/-!
# Weak learnability and the minimax theorem

Freund and Schapire, *Game theory, on-line prediction and boosting*, COLT 1996, Section 4.1:
take finitely many instances `x`, finitely many hypotheses `h` and a target concept `c`, and
consider the mistake matrix `M(x, h) = 1` if `h(x) ≠ c(x)` and `0` otherwise. If every
distribution `Q` on the instances admits a hypothesis of weighted error at most `1 / 2 - γ`
(γ-weak learnability on this finite domain), then von Neumann's minimax theorem gives a single
distribution `P` on the hypotheses under which *every* instance is misclassified with
probability at most `1 / 2 - γ`. For `γ > 0` the target is therefore exactly the
`P`-weighted majority vote of the hypotheses. This is the game-theoretic reason boosting can
exist: AdaBoost approximates such a `P` by running multiplicative weights on the dual game.

Main results:

* `exists_forall_mistake_le`: weak learnability yields a mixed hypothesis misclassifying every
  point with probability at most `1 / 2 - γ`.
* `exists_weightedVote_eq`: for `γ > 0`, the target is a weighted majority vote of the
  hypotheses.

The proof applies `matrixGame_exists_isSaddlePointOn` (von Neumann's theorem as a saddle point)
to the mistake matrix, with the instances as the maximizing row player and the hypotheses as the
minimizing column player.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.BoostingMinimax

open Matrix Convexity

variable {n k : ℕ}

/-- **The mistake matrix** of `k` hypotheses `H j` against a target `c` on `n` instances:
`M(x, j) = 1` if `H j x ≠ c x` and `0` otherwise (rows are instances, columns hypotheses). -/
def mistakeMatrix (H : Fin k → Fin n → Bool) (c : Fin n → Bool) : Matrix (Fin n) (Fin k) ℝ :=
  fun x j => if H j x = c x then 0 else 1

private theorem dotProduct_mulVec_single (A : Matrix (Fin n) (Fin k) ℝ) (p : Fin n → ℝ)
    (j : Fin k) :
    p ⬝ᵥ (A *ᵥ ((StdSimplex.single j : StdSimplex ℝ (Fin k)).weights : Fin k → ℝ)) =
      ∑ x, p x * A x j := by
  simp [dotProduct, mulVec, Finsupp.single_apply]

private theorem single_dotProduct_mulVec (A : Matrix (Fin n) (Fin k) ℝ) (q : Fin k → ℝ)
    (x : Fin n) :
    ((StdSimplex.single x : StdSimplex ℝ (Fin n)).weights : Fin n → ℝ) ⬝ᵥ (A *ᵥ q) =
      ∑ j, A x j * q j := by
  simp [dotProduct, mulVec, Finsupp.single_apply]

/-- **Weak learnability gives a mixed hypothesis that errs on no instance with probability above
`1 / 2 - γ`** (Freund and Schapire, *Game theory, on-line prediction and boosting*, COLT 1996,
Section 4.1, the argument from their equation (6)): let `H` be `k` hypotheses on a domain of
`n > 0` instances and `c` a target. If for every distribution `Q` on the instances some
hypothesis has weighted error `∑ₓ Q(x) 1[H j x ≠ c x] ≤ 1 / 2 - γ`, then some distribution `P`
on the hypotheses satisfies `∑ⱼ P(j) 1[H j x ≠ c x] ≤ 1 / 2 - γ` for every instance `x`. -/
theorem exists_forall_mistake_le (hn : 0 < n) (H : Fin k → Fin n → Bool) (c : Fin n → Bool)
    {γ : ℝ}
    (hweak : ∀ Q : StdSimplex ℝ (Fin n),
      ∃ j, ∑ x, Q.weights x * (if H j x = c x then 0 else 1) ≤ 1 / 2 - γ) :
    ∃ P : StdSimplex ℝ (Fin k),
      ∀ x, ∑ j, P.weights j * (if H j x = c x then 0 else 1) ≤ 1 / 2 - γ := by
  have hQ0 : StdSimplex ℝ (Fin n) := StdSimplex.single ⟨0, hn⟩
  have hk : 0 < k := by
    obtain ⟨j, -⟩ := hweak hQ0
    exact Fin.pos j
  obtain ⟨Q, P, hrow, hcol⟩ := matrixGame_exists_isSaddlePointOn hn hk (mistakeMatrix H c)
  obtain ⟨j, hj⟩ := hweak Q
  refine ⟨P, fun x => ?_⟩
  have h1 := hrow (StdSimplex.single x)
  have h2 := hcol (StdSimplex.single j)
  rw [single_dotProduct_mulVec] at h1
  rw [dotProduct_mulVec_single] at h2
  have e1 : ∑ j', P.weights j' * (if H j' x = c x then 0 else 1) =
      ∑ j', mistakeMatrix H c x j' * P.weights j' :=
    Finset.sum_congr rfl fun j' _ => by rw [mistakeMatrix, mul_comm]
  have e2 : ∑ x', Q.weights x' * mistakeMatrix H c x' j =
      ∑ x', Q.weights x' * (if H j x' = c x' then 0 else 1) := rfl
  rw [e1]
  linarith

/-- **The weighted majority vote**: the `P`-weighted majority vote of the hypotheses `H` at the
point `x`: `true` when the hypotheses voting `true` carry more than half of the weight. -/
noncomputable def weightedVote (P : Fin k → ℝ) (H : Fin k → Fin n → Bool) (x : Fin n) : Bool :=
  decide (1 / 2 < ∑ j, P j * (if H j x then 1 else 0))

/-- **Under γ-weak learnability with `γ > 0`, the target is a weighted majority vote** (Freund
and Schapire, *Game theory, on-line prediction and boosting*, COLT 1996, Section 4.1): with the
hypotheses of `exists_forall_mistake_le`, some distribution `P` on the hypotheses has
`weightedVote P H x = c x` for every instance `x`, and every instance is classified correctly by
hypotheses of total weight at least `1 / 2 + γ`. -/
theorem exists_weightedVote_eq (hn : 0 < n) (H : Fin k → Fin n → Bool) (c : Fin n → Bool)
    {γ : ℝ} (hγ : 0 < γ)
    (hweak : ∀ Q : StdSimplex ℝ (Fin n),
      ∃ j, ∑ x, Q.weights x * (if H j x = c x then 0 else 1) ≤ 1 / 2 - γ) :
    ∃ P : StdSimplex ℝ (Fin k), ∀ x,
      1 / 2 + γ ≤ ∑ j, P.weights j * (if H j x = c x then 1 else 0) ∧
        weightedVote (fun j => P.weights j) H x = c x := by
  obtain ⟨P, hP⟩ := exists_forall_mistake_le hn H c hweak
  refine ⟨P, fun x => ?_⟩
  have htot : ∑ j, P.weights j * (if H j x = c x then 1 else 0) +
      ∑ j, P.weights j * (if H j x = c x then 0 else 1) = 1 := by
    rw [← Finset.sum_add_distrib]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans P.total_of_fintype
    split_ifs <;> ring
  have hgood : 1 / 2 + γ ≤ ∑ j, P.weights j * (if H j x = c x then 1 else 0) := by
    linarith [hP x]
  refine ⟨hgood, ?_⟩
  unfold weightedVote
  cases hc : c x
  · -- the hypotheses voting `true` are exactly the mistaken ones
    have e : ∑ j, P.weights j * (if H j x then 1 else 0) =
        ∑ j, P.weights j * (if H j x = c x then 0 else 1) :=
      Finset.sum_congr rfl fun j _ => by cases H j x <;> simp [hc]
    rw [e]
    simp only [decide_eq_false_iff_not, not_lt]
    linarith [hP x]
  · have e : ∑ j, P.weights j * (if H j x then 1 else 0) =
        ∑ j, P.weights j * (if H j x = c x then 1 else 0) :=
      Finset.sum_congr rfl fun j _ => by cases H j x <;> simp [hc]
    rw [e]
    simp only [decide_eq_true_eq]
    linarith

end Cslib.MachineLearning.BoostingMinimax
