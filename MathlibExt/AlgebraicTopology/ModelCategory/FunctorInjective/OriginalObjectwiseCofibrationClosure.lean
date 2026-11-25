/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.BoundedGenerators
public import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import MathlibExt.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import MathlibExt.CategoryTheory.Functor.SmallIndex

/-!
# Original objectwise closure and the bounded-family reverse inclusion

The original coefficient weak factorization systems give all four objectwise
closure properties. The actual bounded-family small-object argument then
places its whole cellular and generated left classes inside the original
objectwise cofibrations. Exhaustion of all objectwise cofibrations is separate.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.FunctorInjective

attribute [local instance] CategoryTheory.Functor.EssentialIndexData.indexCategory

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C]

section ObjectwiseClosure

variable [HasColimitsOfSize.{w, w} C]

/-- Bare objectwise cofibrations inherit all four closures from the original model. -/
theorem objectwiseCofibrations_stable :
    ((cofibrations C).functorCategory D).IsStableUnderCoproducts.{w} ∧
      ((cofibrations C).functorCategory D).IsStableUnderCobaseChange ∧
      IsStableUnderTransfiniteComposition.{w} ((cofibrations C).functorCategory D) ∧
      ((cofibrations C).functorCategory D).IsStableUnderRetracts := by
  let _ : (cofibrations C).IsStableUnderCoproducts.{w} :=
    IsStableUnderCoproducts.of_llp_eq (cofibrations C) (trivialFibrations C)
      (trivialFibrations_llp C)
  let _ : IsStableUnderTransfiniteComposition.{w} (cofibrations C) :=
    { isStableUnderTransfiniteCompositionOfShape := fun K _ _ _ _ => by
        rw [← trivialFibrations_llp C]
        infer_instance }
  have hCoproducts :
      ((cofibrations C).functorCategory D).IsStableUnderCoproducts.{w} :=
    { isStableUnderCoproductsOfShape := fun I => inferInstance }
  have hTransfinite :
      IsStableUnderTransfiniteComposition.{w} ((cofibrations C).functorCategory D) :=
    { isStableUnderTransfiniteCompositionOfShape := fun K _ _ _ _ => inferInstance }
  exact ⟨hCoproducts, inferInstance, hTransfinite, inferInstance⟩

/-- Bare objectwise trivial cofibrations have the same four derived closures. -/
theorem objectwiseTrivialCofibrations_stable :
    ((trivialCofibrations C).functorCategory D).IsStableUnderCoproducts.{w} ∧
      ((trivialCofibrations C).functorCategory D).IsStableUnderCobaseChange ∧
      IsStableUnderTransfiniteComposition.{w} ((trivialCofibrations C).functorCategory D) ∧
      ((trivialCofibrations C).functorCategory D).IsStableUnderRetracts := by
  let _ : (trivialCofibrations C).IsStableUnderCoproducts.{w} :=
    IsStableUnderCoproducts.of_llp_eq (trivialCofibrations C) (fibrations C)
      (fibrations_llp C)
  let _ : IsStableUnderTransfiniteComposition.{w} (trivialCofibrations C) :=
    { isStableUnderTransfiniteCompositionOfShape := fun K _ _ _ _ => by
        rw [← fibrations_llp C]
        infer_instance }
  have hCoproducts :
      ((trivialCofibrations C).functorCategory D).IsStableUnderCoproducts.{w} :=
    { isStableUnderCoproductsOfShape := fun I => inferInstance }
  have hTransfinite :
      IsStableUnderTransfiniteComposition.{w} ((trivialCofibrations C).functorCategory D) :=
    { isStableUnderTransfiniteCompositionOfShape := fun K _ _ _ _ => inferInstance }
  exact ⟨hCoproducts, inferInstance, hTransfinite, inferInstance⟩

end ObjectwiseClosure

section OriginalBoundedFamily

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} D C)
  (b : BoundedConstruction d κLP s.equivalence)

/-- Every actual chosen bounded generator is an original objectwise cofibration. -/
theorem originalGenerators_le_objectwiseCofibrations :
    b.family.generators ≤ (cofibrations C).functorCategory D := by
  intro F G f hf
  exact (b.family.generators_le_compact f hf).1

/-- The full original bounded-family weak saturation is objectwise cofibrant.
No objectwise-generation equality is an input. -/
theorem originalGenerators_weakSaturation_le_objectwiseCofibrations :
    (transfiniteCompositions.{w} (coproducts.{w} b.family.generators).pushouts).retracts ≤
      (cofibrations C).functorCategory D := by
  let P := (cofibrations C).functorCategory D
  obtain ⟨hCoproducts, hCobase, hTransfinite, hRetracts⟩ :=
    objectwiseCofibrations_stable.{w} (D := D) (C := C)
  let _ : P.IsStableUnderCoproducts.{w} := hCoproducts
  let _ : P.IsStableUnderCobaseChange := hCobase
  let _ : IsStableUnderTransfiniteComposition.{w} P := hTransfinite
  let _ : P.IsStableUnderRetracts := hRetracts
  have hC : (coproducts.{w} b.family.generators) ≤ P :=
    (coproducts_monotone (originalGenerators_le_objectwiseCofibrations d κLP s b)).trans
      P.coproducts_le
  have hP : (coproducts.{w} b.family.generators).pushouts ≤ P :=
    (pushouts_monotone hC).trans P.pushouts_le
  have hT : transfiniteCompositions.{w} (coproducts.{w} b.family.generators).pushouts ≤ P :=
    (transfiniteCompositions_monotone hP).trans (transfiniteCompositions_le P)
  exact (retracts_monotone hT).trans P.retracts_le

/-- The same original bounded family's entire right-then-left class is objectwise
cofibrant, using its actual internally derived small-object argument. -/
theorem originalGenerators_rlp_llp_le_objectwiseCofibrations :
    b.family.generators.rlp.llp ≤ (cofibrations C).functorCategory D := by
  let _ : b.family.generators.HasSmallObjectArgument.{w} := b.hasSmallObjectArgument
  rw [b.family.generators.llp_rlp_of_hasSmallObjectArgument]
  exact originalGenerators_weakSaturation_le_objectwiseCofibrations d κLP s b

end OriginalBoundedFamily

end HomotopicalAlgebra.FunctorInjective
