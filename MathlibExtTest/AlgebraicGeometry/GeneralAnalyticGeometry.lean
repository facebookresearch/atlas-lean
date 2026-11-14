/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralAnalyticGeometry
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fin.VecNotation

/-!
Provider-free interface checks: genuine two-variable holomorphic evaluation
and an I-relation retained through quotient, sheafification and pullback.
The square-zero ideal tests a nonreduced local model without a manifold or
GAGA provider.
-/

open MathlibExt.AlgebraicGeometry.PolynomialAnalyticSpaces
open scoped Manifold ContDiff

@[expose] public noncomputable section

example : polynomialSections 2 ⊤
    ((MvPolynomial.X (0 : Fin 2)) ^ 2 + 3 * MvPolynomial.X 1 - MvPolynomial.C 7)
    ⟨![2, 5], by trivial⟩ = (12 : ℂ) := by
  rw [polynomialSections_eval]
  norm_num

example : polynomialMap 1
    (Ideal.span {(MvPolynomial.X (0 : Fin 1)) ^ 2})
    (MvPolynomial.X (0 : Fin 1)) ^ 2 = 0 := by
  rw [← map_pow]
  exact polynomialMap_relation 1 _ _ (Ideal.subset_span (Set.mem_singleton _))

example : polynomialMap 1
    (Ideal.span {MvPolynomial.X (0 : Fin 1) - MvPolynomial.C 3})
    (MvPolynomial.X (0 : Fin 1)) =
      polynomialMap 1 (Ideal.span {MvPolynomial.X (0 : Fin 1) - MvPolynomial.C 3})
        (MvPolynomial.C 3) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact polynomialMap_relation 1 _ _ (Ideal.subset_span (Set.mem_singleton _))
