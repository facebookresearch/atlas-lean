/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.HomogeneousResultant

@[expose] public section

open MvPolynomial MathlibExt.AlgebraicGeometry.HomogeneousResultant

-- Coefficient extraction reads the indicated form's actual coefficient: for the binary linear
-- forms `F i = ∑ j, m i j • X j`, the index `(i, single j 1)` gives the matrix entry `m i j`.
example (m : Fin 2 → Fin 2 → ℤ) (i j : Fin 2) :
    coefficients (n := 1) (d := fun _ ↦ 1)
      (fun i ↦ ∑ j, monomial (Finsupp.single j 1) (m i j))
      ⟨i, ⟨Finsupp.single j 1, by simp⟩⟩ = m i j := by
  fin_cases j <;> simp [coefficients, coeff_monomial, Finsupp.single_left_inj one_ne_zero]

-- With input degrees `(2, 3)`, the coefficients of the first form have block degree `3` and
-- those of the second form have block degree `2`: the product of the other forms' degrees.
example (P : UniversalResultant 1 ![2, 3]) :
    IsWeightedHomogeneous
      (fun a : CoefficientIndex 1 ![2, 3] ↦ if a.1 = 0 then (1 : ℕ) else 0) P.polynomial 3 := by
  have h : ∏ j ∈ Finset.univ.erase (0 : Fin 2), (![2, 3] : Fin 2 → ℕ) j = 3 := by decide
  simpa [h] using P.blockDegree 0

example (P : UniversalResultant 1 ![2, 3]) :
    IsWeightedHomogeneous
      (fun a : CoefficientIndex 1 ![2, 3] ↦ if a.1 = 1 then (1 : ℕ) else 0) P.polynomial 2 := by
  have h : ∏ j ∈ Finset.univ.erase (1 : Fin 2), (![2, 3] : Fin 2 → ℕ) j = 2 := by decide
  simpa [h] using P.blockDegree 1
