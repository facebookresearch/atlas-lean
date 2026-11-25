/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Author: @toskua
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The zero-morphism argument generalizes the first-quadrant proof by
@junekim623 and Muse from the Hartshorne development.
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.TotalComplex
public import MathlibExt.CategoryTheory.GradedObject.FiniteFibers
public import MathlibExt.CategoryTheory.GradedObject.Evaluation

/-!
# Exactness of totalization

Totalization is degreewise pushforward of the underlying graded object.
The coproducts over each total-shape fiber provide its terms. Exactness
of these coproducts makes totalization preserve finite limits; finite
colimits are preserved without the exactness assumption. Finite
biproducts supply the finite-fiber specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w₁ w₂ w₁₂ v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  {c₁₂ : ComplexShape I₁₂} [TotalComplexShape c₁ c₂ c₁₂]

/-- The bidegrees contributing to a fixed total degree. -/
abbrev TotalFiber (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
    (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]
    (i₁₂ : I₁₂) :=
  (ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {i₁₂}

/-- A total shape has finite fibers when each total degree receives only
finitely many bidegrees. -/
abbrev FiniteTotalFibers (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
    (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂] : Prop :=
  GradedObject.FiniteFibers (ComplexShape.π c₁ c₂ c₁₂)

/-- Finite fibers of the total-shape projection make every bicomplex
totalizable in any category with finite coproducts. -/
theorem hasTotal_of_finiteFibers (K : HomologicalComplex₂ C c₁ c₂)
    [FiniteTotalFibers c₁ c₂ c₁₂]
    [HasFiniteCoproducts C] : K.HasTotal c₁₂ :=
  inferInstance

/-- Forgetting both differentials of a bicomplex preserves limits computed
pointwise. -/
noncomputable instance preservesLimitsOfShape_toGradedObjectFunctor
    (K : Type*) [Category* K] [HasLimitsOfShape K C] :
    PreservesLimitsOfShape K (toGradedObjectFunctor C c₁ c₂) := by
  let E := (piEquivalenceFunctorDiscrete (I₁ × I₂) C).functor
  let : PreservesLimitsOfShape K (toGradedObjectFunctor C c₁ c₂ ⋙ E) := by
    apply preservesLimitsOfShape_of_evaluation _ K
    rintro ⟨⟨i₁, i₂⟩⟩
    change PreservesLimitsOfShape K
      (HomologicalComplex.eval _ c₁ i₁ ⋙ HomologicalComplex.eval C c₂ i₂)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (toGradedObjectFunctor C c₁ c₂) E

/-- Forgetting both differentials of a bicomplex preserves colimits computed
pointwise. -/
noncomputable instance preservesColimitsOfShape_toGradedObjectFunctor
    (K : Type*) [Category* K] [HasColimitsOfShape K C] :
    PreservesColimitsOfShape K (toGradedObjectFunctor C c₁ c₂) := by
  let E := (piEquivalenceFunctorDiscrete (I₁ × I₂) C).functor
  let : PreservesColimitsOfShape K
      (toGradedObjectFunctor C c₁ c₂ ⋙ E) := by
    apply preservesColimitsOfShape_of_evaluation _ K
    rintro ⟨⟨i₁, i₂⟩⟩
    change PreservesColimitsOfShape K
      (HomologicalComplex.eval _ c₁ i₁ ⋙ HomologicalComplex.eval C c₂ i₂)
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (toGradedObjectFunctor C c₁ c₂) E

section TotalFunctor

variable [DecidableEq I₁₂]
  [∀ n, HasColimitsOfShape (Discrete (TotalFiber c₁ c₂ c₁₂ n)) C]

omit [DecidableEq I₁₂] in
/-- The fiber coproducts make every bicomplex totalizable, including infinite fibers. -/
theorem hasTotal_of_colimit_fibers (K : HomologicalComplex₂ C c₁ c₂) : K.HasTotal c₁₂ := by
  intro n
  infer_instance

/-- In each total degree, `totalFunctor` is graded pushforward followed by
evaluation. -/
noncomputable def totalFunctorCompEvalIso (i₁₂ : I₁₂) :
    totalFunctor C c₁ c₂ c₁₂ ⋙ HomologicalComplex.eval C c₁₂ i₁₂ ≅
      toGradedObjectFunctor C c₁ c₂ ⋙
        GradedObject.map C (ComplexShape.π c₁ c₂ c₁₂) ⋙
          GradedObject.eval i₁₂ :=
  Iso.refl _

/-- Totalization along any total shape with its actual fiber coproducts preserves zero maps. -/
instance totalFunctor_preservesZeroMorphisms :
    (totalFunctor C c₁ c₂ c₁₂).PreservesZeroMorphisms where
  map_zero X Y := by
    simp only [totalFunctor_map]
    apply HomologicalComplex.hom_ext
    intro n
    change GradedObject.mapMap (toGradedObjectMap (0 : X ⟶ Y)) _ n = 0
    apply GradedObject.mapObj_ext _ _
    intro i hi
    rw [GradedObject.ι_mapMap, toGradedObjectMap_apply,
      HomologicalComplex.zero_f, HomologicalComplex.zero_f]
    exact zero_comp.trans comp_zero.symm

/-- Exact coproducts over the total-shape fibers make totalization preserve finite limits. -/
theorem totalFunctor_preservesFiniteLimits_of_exact_fibers
    [∀ n, HasExactColimitsOfShape (Discrete (TotalFiber c₁ c₂ c₁₂ n)) C]
    [HasFiniteLimits C] : PreservesFiniteLimits (totalFunctor C c₁ c₂ c₁₂) where
  preservesFiniteLimits K := by
    intro _ _
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro i₁₂
    letI : PreservesLimitsOfShape K (toGradedObjectFunctor C c₁ c₂) :=
      preservesLimitsOfShape_toGradedObjectFunctor K
    letI : PreservesLimitsOfShape K
        (GradedObject.map C (ComplexShape.π c₁ c₂ c₁₂)) :=
      GradedObject.preservesLimitsOfShape_map_of_exact_fibers K _
    letI : PreservesLimitsOfShape K (GradedObject.eval (C := C) i₁₂) := inferInstance
    let : PreservesLimitsOfShape K
        (toGradedObjectFunctor C c₁ c₂ ⋙
          GradedObject.map C (ComplexShape.π c₁ c₂ c₁₂) ⋙ GradedObject.eval i₁₂) :=
      inferInstance
    exact preservesLimitsOfShape_of_natIso
      (totalFunctorCompEvalIso (C := C)
        (c₁ := c₁) (c₂ := c₂) (c₁₂ := c₁₂) i₁₂).symm

/-- Totalization preserves finite colimits whenever its actual fiber coproducts exist. -/
theorem totalFunctor_preservesFiniteColimits_of_colimit_fibers
    [HasFiniteColimits C] : PreservesFiniteColimits (totalFunctor C c₁ c₂ c₁₂) where
  preservesFiniteColimits K := by
    intro _ _
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro i₁₂
    letI : PreservesColimitsOfShape K (toGradedObjectFunctor C c₁ c₂) :=
      preservesColimitsOfShape_toGradedObjectFunctor K
    letI : PreservesColimitsOfShape K
        (GradedObject.map C (ComplexShape.π c₁ c₂ c₁₂)) :=
      GradedObject.preservesColimitsOfShape_map K _
    letI : PreservesColimitsOfShape K (GradedObject.eval (C := C) i₁₂) := inferInstance
    let : PreservesColimitsOfShape K
        (toGradedObjectFunctor C c₁ c₂ ⋙
          GradedObject.map C (ComplexShape.π c₁ c₂ c₁₂) ⋙ GradedObject.eval i₁₂) :=
      inferInstance
    exact preservesColimitsOfShape_of_natIso
      (totalFunctorCompEvalIso (C := C)
        (c₁ := c₁) (c₂ := c₂) (c₁₂ := c₁₂) i₁₂).symm

/-- Exact fiber coproducts preserve an actual short exact bicomplex sequence under totalization. -/
theorem totalFunctor_map_shortExact_of_exact_fibers
    [∀ n, HasExactColimitsOfShape (Discrete (TotalFiber c₁ c₂ c₁₂ n)) C]
    [HasFiniteLimits C] [HasFiniteColimits C]
    (S : ShortComplex (HomologicalComplex₂ C c₁ c₂)) (hS : S.ShortExact) :
    (S.map (totalFunctor C c₁ c₂ c₁₂)).ShortExact := by
  letI : PreservesFiniteLimits (totalFunctor C c₁ c₂ c₁₂) :=
    totalFunctor_preservesFiniteLimits_of_exact_fibers
  letI : PreservesFiniteColimits (totalFunctor C c₁ c₂ c₁₂) :=
    totalFunctor_preservesFiniteColimits_of_colimit_fibers
  exact hS.map_of_exact (totalFunctor C c₁ c₂ c₁₂)

end TotalFunctor

section FiniteTotalFunctor

variable [DecidableEq I₁₂]
  [GradedObject.FiniteFibers (ComplexShape.π c₁ c₂ c₁₂)]
  [HasFiniteCoproducts C]

/-- Totalization along a finite-fiber total shape preserves finite limits. -/
noncomputable instance totalFunctor_preservesFiniteLimits
    [HasFiniteBiproducts C] [HasFiniteLimits C] :
    PreservesFiniteLimits (totalFunctor C c₁ c₂ c₁₂) :=
  totalFunctor_preservesFiniteLimits_of_exact_fibers

/-- Totalization along a finite-fiber total shape preserves finite
colimits. -/
noncomputable instance totalFunctor_preservesFiniteColimits
    [HasFiniteColimits C] :
    PreservesFiniteColimits (totalFunctor C c₁ c₂ c₁₂) :=
  totalFunctor_preservesFiniteColimits_of_colimit_fibers

/-- Totalization along a finite-fiber total shape preserves short exact
sequences. -/
theorem totalFunctor_map_shortExact [HasFiniteBiproducts C]
    [HasFiniteLimits C] [HasFiniteColimits C]
    (S : ShortComplex (HomologicalComplex₂ C c₁ c₂))
    (hS : S.ShortExact) :
    (S.map (totalFunctor C c₁ c₂ c₁₂)).ShortExact :=
  totalFunctor_map_shortExact_of_exact_fibers S hS

end FiniteTotalFunctor

end HomologicalComplex₂

end
