/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.CombinatorialNullstellensatz

@[expose] public section

open MvPolynomial MathlibExt.Combinatorics.Additive.CombinatorialNullstellensatz

namespace MathlibExtTest.Combinatorics.Additive.CombinatorialNullstellensatz

-- Chevalley–Warning with one linear form in three variables over `ℤ/2`: the common zero `0` of
-- `x₀ + x₁` is not the only one.
example : ∃ y : Fin 3 → ZMod 2, y ≠ 0 ∧ ∀ j ∈ ({()} : Finset Unit),
    eval y ((fun _ => X 0 + X 1 : Unit → MvPolynomial (Fin 3) (ZMod 2)) j) = 0 := by
  refine exists_ne_common_zero ?_ ?_
  · simp only [Finset.sum_singleton, Fintype.card_fin]
    calc (X 0 + X 1 : MvPolynomial (Fin 3) (ZMod 2)).totalDegree
        ≤ max (X 0 : MvPolynomial (Fin 3) (ZMod 2)).totalDegree (X 1).totalDegree :=
          totalDegree_add _ _
      _ < 3 := by simp [totalDegree_X]
  · simp

-- Theorem 1.2 for `f = x₀ x₁` with `t = (1, 1)` and `S₀ = S₁ = {0, 1}` over `ℚ`.
example : ∃ s : Fin 2 → ℚ, (∀ i, s i ∈ ({0, 1} : Finset ℚ)) ∧
    eval s (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) ≠ 0 := by
  have hmon : (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    simp [X]
  have ht : Finsupp.equivFunOnFinite.symm ![1, 1] =
      (Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) := by
    ext i; fin_cases i <;> simp
  refine exists_eval_ne_zero _ ![1, 1] ?_ ?_ (fun _ => {0, 1}) fun i => ?_
  · rw [hmon, totalDegree_monomial _ one_ne_zero]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  · rw [hmon, ht, coeff_monomial]
    simp
  · fin_cases i <;> simp

end MathlibExtTest.Combinatorics.Additive.CombinatorialNullstellensatz
