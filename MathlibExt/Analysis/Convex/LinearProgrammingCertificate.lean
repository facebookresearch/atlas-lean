/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.LinearProgrammingWeakDuality

/-!
# LP certificate: a feasible primal/dual pair with equal objectives is optimal

For primal-feasible `x` (`x ≥ 0`, `A *ᵥ x ≤ b`) and dual-feasible `y`
(`y ≥ 0`, `c ≤ Aᵀ *ᵥ y`) with equal objectives `c ⬝ᵥ x = b ⬝ᵥ y`, the pair
is optimal for both: every feasible primal point has objective at most
`c ⬝ᵥ x`, and every feasible dual point has objective at least `b ⬝ᵥ y`.
This is the certificate corollary of weak duality
(`MathlibExt.Analysis.Convex.LPWeakDuality.weak_linear_programming_duality`,
whose docstring already states it in words); strong duality returns such a
pair but does not state this lemma.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.LPCertificate

open scoped Matrix

/-- **LP certificate (M14.T02).** A feasible primal/dual pair with equal
objectives is optimal for both: every feasible primal point has objective
at most `c ⬝ᵥ x`, and every feasible dual point has objective at least
`b ⬝ᵥ y`. One application of weak duality per conjunct, rewriting with the
equal-objective hypothesis. -/
theorem feasible_pair_equal_objectives_optimal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hAx : ∀ j, (A.mulVec x) j ≤ b j)
    {y : Fin m → ℝ} (hy : ∀ j, 0 ≤ y j)
    (hAty : ∀ i, c i ≤ (Aᵀ.mulVec y) i)
    (heq : c ⬝ᵥ x = b ⬝ᵥ y) :
    (∀ x' : Fin n → ℝ, (∀ i, 0 ≤ x' i) →
      (∀ j, (A.mulVec x') j ≤ b j) → c ⬝ᵥ x' ≤ c ⬝ᵥ x) ∧
    (∀ y' : Fin m → ℝ, (∀ j, 0 ≤ y' j) →
      (∀ i, c i ≤ (Aᵀ.mulVec y') i) → b ⬝ᵥ y ≤ b ⬝ᵥ y') := by
  constructor
  · intro x' hx' hAx'
    calc c ⬝ᵥ x' ≤ b ⬝ᵥ y :=
          MathlibExt.Analysis.Convex.LPWeakDuality.weak_linear_programming_duality
            A b c hx' hAx' hy hAty
      _ = c ⬝ᵥ x := heq.symm
  · intro y' hy' hAty'
    calc b ⬝ᵥ y = c ⬝ᵥ x := heq.symm
      _ ≤ b ⬝ᵥ y' :=
          MathlibExt.Analysis.Convex.LPWeakDuality.weak_linear_programming_duality
            A b c hx hAx hy' hAty'

end MathlibExt.Analysis.Convex.LPCertificate
