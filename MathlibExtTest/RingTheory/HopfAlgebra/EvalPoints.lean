/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HopfAlgebra.EvalPoints

@[expose] public section

open scoped TensorProduct

-- Consumer with the original binders and the original inline evaluation map: the source's
-- bijective statement follows from the injective one through `hev.1`. The source spells the
-- product map with the now-deprecated `Pi.algHom`.
set_option linter.deprecated false in
example
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
    [Module.Finite ↥(IntermediateField.fixedField D) A]
    [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ)
          (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) →
            AlgebraicClosure ℚ))
        (Pi.algHom ↥(IntermediateField.fixedField D) _
          fun ν : WithConv
              (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
            (WithConv.ofConv ν :
              A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ]
          (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) →
            AlgebraicClosure ℚ)))
    (u u' : A →ₐ[↥(IntermediateField.fixedField D)] A)
    (h : ∀ ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ,
      ν.comp u = ν.comp u') :
    u = u' :=
  HopfAlgebra.algHom_eq_of_forall_comp_eq_of_injective_evalPoints D A hev.1 u u' h

-- Higher-universe consumer that has only injectivity of the evaluation map, and no finiteness
-- assumption on the algebra or its points.
example
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type 1) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
    (hev : Function.Injective (HopfAlgebra.evalPointsAlgHom D A))
    (u u' : A →ₐ[↥(IntermediateField.fixedField D)] A)
    (h : ∀ ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ,
      ν.comp u = ν.comp u') :
    u = u' :=
  HopfAlgebra.algHom_eq_of_forall_comp_eq_of_injective_evalPoints D A hev u u' h

-- The evaluation map sends a right tensor factor to evaluation at a point.
example
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
    (a : A)
    (ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)) :
    HopfAlgebra.evalPointsAlgHom D A (Algebra.TensorProduct.includeRight a) ν =
      (WithConv.ofConv ν) a := by
  rw [HopfAlgebra.evalPointsAlgHom_includeRight]
