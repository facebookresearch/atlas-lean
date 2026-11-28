/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HomogeneousIdealQuotient
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Tests for `MathlibExt.RingTheory.HomogeneousIdealQuotient`. -/

@[expose] public section

open MvPolynomial

#check @Ideal.quotientGrading
#check @Ideal.mk_mem_quotientGrading
#check @Ideal.quotientGradingMk
#check @Ideal.coe_quotientGradingMk
#check @Ideal.quotientGrading.gradedMonoid
#check @Ideal.quotientDecomposeAux
#check @Ideal.quotientDecomposeAux_apply
#check @Ideal.quotientDecomposeAux_of_mem
#check @Ideal.coe_quotientDecomposeAux
#check @Ideal.quotientDecomposeAux_eq_zero
#check @Ideal.quotientDecompose
#check @Ideal.IsHomogeneous.gradedAlgebra
#check @Ideal.IsHomogeneous.decompose_mk

attribute [local instance] MvPolynomial.gradedAlgebra

namespace HomogeneousIdealQuotientTest

/-- The ideal `(X₀ X₁)` of `ℚ[X₀, X₁]` is homogeneous. -/
theorem isHomogeneous_span_X_mul_X :
    (Ideal.span {(X 0 * X 1 : MvPolynomial (Fin 2) ℚ)}).IsHomogeneous
      (homogeneousSubmodule (Fin 2) ℚ) :=
  Ideal.homogeneous_span _ _ fun _ hx => by
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨2, (mem_homogeneousSubmodule _ _).mpr (by
      simpa using (isHomogeneous_X ℚ (0 : Fin 2)).mul (isHomogeneous_X ℚ (1 : Fin 2)))⟩

/-- In `ℚ[X₀, X₁] / (X₀ X₁)`, the degree `1` component of the class of `X₀ + 1` is the class of
`X₀`. -/
example :
    letI := isHomogeneous_span_X_mul_X.gradedAlgebra
    ((DirectSum.decompose (Ideal.quotientGrading (homogeneousSubmodule (Fin 2) ℚ)
        (Ideal.span {(X 0 * X 1 : MvPolynomial (Fin 2) ℚ)}))
        (Ideal.Quotient.mk _ (X 0 + 1)) 1 : _) :
        MvPolynomial (Fin 2) ℚ ⧸ Ideal.span {(X 0 * X 1 : MvPolynomial (Fin 2) ℚ)}) =
      Ideal.Quotient.mk _ (X 0) := by
  rw [isHomogeneous_span_X_mul_X.decompose_mk]
  congr 1
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
    DirectSum.decompose_of_mem_same _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X ℚ 0)),
    DirectSum.decompose_of_mem_ne _ ((mem_homogeneousSubmodule 0 _).mpr
      (isHomogeneous_one (Fin 2) ℚ)) (by norm_num), add_zero]

end HomogeneousIdealQuotientTest
