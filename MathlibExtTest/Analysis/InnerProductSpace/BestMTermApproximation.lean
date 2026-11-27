/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.BestMTermApproximation

/-!
# Tests for best `M`-term approximation in an orthonormal basis
-/

open scoped InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.BestMTermApproximation

namespace MathlibExtTest.Analysis.InnerProductSpace.BestMTermApproximation

/-- The hypotheses of the best `M`-term theorem are satisfiable: in the standard basis of `ℝ³`,
`S = {0, 2}` holds the two largest coefficients of `f = (3, -1, 2)`. -/
example : ∀ i ∈ ({0, 2} : Finset (Fin 3)), ∀ j ∉ ({0, 2} : Finset (Fin 3)),
    ‖⟪EuclideanSpace.basisFun (Fin 3) ℝ j, (!₂[3, -1, 2] : EuclideanSpace ℝ (Fin 3))⟫_ℝ‖ ≤
      ‖⟪EuclideanSpace.basisFun (Fin 3) ℝ i, (!₂[3, -1, 2] : EuclideanSpace ℝ (Fin 3))⟫_ℝ‖ := by
  intro i hi j hj
  fin_cases i <;> fin_cases j <;> simp_all [EuclideanSpace.inner_single_left]

/-- Keeping the two largest coefficients of `(3, -1, 2)` beats every other two-term
approximation in the standard basis of `ℝ³`. -/
example (T : Finset (Fin 3)) (hT : T.card ≤ 2) (a : Fin 3 → ℝ) :
    ‖(!₂[3, -1, 2] : EuclideanSpace ℝ (Fin 3)) -
        ∑ i ∈ ({0, 2} : Finset (Fin 3)),
          ⟪EuclideanSpace.basisFun (Fin 3) ℝ i, (!₂[3, -1, 2] : EuclideanSpace ℝ (Fin 3))⟫_ℝ •
            EuclideanSpace.basisFun (Fin 3) ℝ i‖ ≤
      ‖(!₂[3, -1, 2] : EuclideanSpace ℝ (Fin 3)) -
        ∑ i ∈ T, a i • EuclideanSpace.basisFun (Fin 3) ℝ i‖ := by
  refine norm_sub_sum_inner_smul_le _ _ (by simpa using hT) ?_ a
  intro i hi j hj
  fin_cases i <;> fin_cases j <;> simp_all [EuclideanSpace.inner_single_left]

/-- The error of keeping the coefficients on `{0, 2}` is the dropped coefficient: `1`. -/
example :
    ‖(!₂[3, -1, 2] : EuclideanSpace ℝ (Fin 3)) -
        ∑ i ∈ ({0, 2} : Finset (Fin 3)),
          ⟪EuclideanSpace.basisFun (Fin 3) ℝ i, (!₂[3, -1, 2] : EuclideanSpace ℝ (Fin 3))⟫_ℝ •
            EuclideanSpace.basisFun (Fin 3) ℝ i‖ ^ 2 = 1 := by
  rw [norm_sub_sum_inner_smul_sq]
  have : ({0, 2} : Finset (Fin 3))ᶜ = {1} := by decide
  rw [this]
  simp [EuclideanSpace.inner_single_left]

/-- The rearrangement lemma needs nonnegative weights only through the minimum on `S \ T`;
here a direct instance on three weights. -/
example : ∑ i ∈ ({1} : Finset (Fin 3)), (![3, 1, 2] : Fin 3 → ℝ) i ≤
    ∑ i ∈ ({0} : Finset (Fin 3)), (![3, 1, 2] : Fin 3 → ℝ) i := by
  refine sum_le_sum_of_forall_le _ (fun i => by fin_cases i <;> norm_num) (by simp) ?_
  intro i hi j hj
  simp only [Finset.mem_singleton] at hi hj
  subst hi
  fin_cases j <;> first | exact absurd rfl hj | norm_num

end MathlibExtTest.Analysis.InnerProductSpace.BestMTermApproximation
