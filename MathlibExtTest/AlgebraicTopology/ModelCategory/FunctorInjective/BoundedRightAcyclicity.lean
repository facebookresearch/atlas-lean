/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.BoundedRightAcyclicity

/-!
# Entire original free I images and bounded-right acyclicity

All original index objects, original I labels, full Hom coproduct maps,
representative Arrow isomorphisms and actual lift structures remain explicit.
The owner checks actual original components and strict square equations,
without a diagram model or all-cofibration saturation input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits
open HomotopicalAlgebra HomotopicalAlgebra.FunctorInjective
open CategoryTheory.Presentable HomPowerAccessibility

namespace MathlibExtTest.FunctorInjectiveBoundedRightAcyclicity

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} D C)
  (b : BoundedConstruction d κLP s.equivalence)

/-- The owner retains the actual entire original free I Arrow value. -/
theorem whole_original_free_I (a : D) (i : d.I.toSet) :
    originalFreeIArrow d κLP s a i =
      Arrow.mk ((HomPowerAccessibility.free C κLP s.equivalence a).map i.1.hom) := rfl

/-- Each original free I Arrow retains its original base map on every Hom summand. -/
theorem original_free_I_component_map (a c : D) (i : d.I.toSet) :
    let _ : HasCoproductsOfShape (a ⟶ c) C := homCoproducts C κLP s.equivalence a c
    (originalFreeIArrow d κLP s a i).hom.app c =
      Sigma.desc (fun h : a ⟶ c ↦ i.1.hom ≫ Sigma.ι (fun _ : a ⟶ c ↦ i.1.right) h) :=
  homCopower_map C κLP s.equivalence c a i.1.hom

/-- Every original free source, target and component has its actual compactness witness. -/
theorem original_free_I_compactness (a : D) (i : d.I.toSet) :
    IsCardinalPresentable (originalFreeIArrow d κLP s a i).left b.cardinal ∧
      IsCardinalPresentable (originalFreeIArrow d κLP s a i).right b.cardinal ∧
      (∀ c : D, IsCardinalPresentable
        ((originalFreeIArrow d κLP s a i).left.obj c) b.cardinal) ∧
      ∀ c : D, IsCardinalPresentable
        ((originalFreeIArrow d κLP s a i).right.obj c) b.cardinal :=
  ⟨originalFreeIArrow_source_presentable d κLP s b a i,
    originalFreeIArrow_target_presentable d κLP s b a i,
    originalFreeIArrow_source_component_presentable d κLP s b a i,
    originalFreeIArrow_target_component_presentable d κLP s b a i⟩

/-- Every original free I Arrow is a compact original objectwise cofibration. -/
theorem original_free_I_membership (a : D) (i : d.I.toSet) :
    compactCofibrationArrows D C b.cardinal (originalFreeIArrow d κLP s a i) :=
  originalFreeIArrow_compact d κLP s b a i

/-- The owner uses the actual whole original free-I representative isomorphism. -/
def originalFreeIComparison (a : D) (i : d.I.toSet) :
    originalFreeIArrow d κLP s a i ≅
      b.family.arrow (originalFreeIRepresentative d κLP s b a i) :=
  originalFreeIRepresentativeIso d κLP s b a i

/-- The full representative square retains every original free-I component equation. -/
theorem originalFreeIComparison_square (a : D) (i : d.I.toSet) (c : D) :
    (originalFreeIComparison d κLP s b a i).hom.left.app c ≫
        (b.family.arrow (originalFreeIRepresentative d κLP s b a i)).hom.app c =
      (originalFreeIArrow d κLP s a i).hom.app c ≫
        (originalFreeIComparison d κLP s b a i).hom.right.app c :=
  congr_app (originalFreeIComparison d κLP s b a i).hom.w c

include d κLP s in
/-- Every original bounded right map has the actual objectwise base TF and W equations. -/
theorem complete_original_right_acyclicity :
    b.family.generators.rlp ≤ (trivialFibrations C).functorCategory D ∧
      b.family.generators.rlp ≤ (weakEquivalences C).functorCategory D :=
  ⟨boundedRight_le_objectwise_trivialFibrations d κLP s b,
    boundedRight_le_objectwise_weak d κLP s b⟩

include κLP s in
/-- The native free/evaluation adjunction supplies all original component I lifting. -/
theorem every_original_component_I_lift {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) :
    ∀ (a : D) (i : d.I.toSet), HasLiftingProperty i.1.hom (p.app a) :=
  boundedRight_component_I_lifting d κLP s b p hp

/-- The whole actual component lift structure is retained for an incoming original square. -/
def originalComponentLift {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : i.1.left ⟶ F.obj a} {g : i.1.right ⟶ G.obj a}
    (sq : CommSq f i.1.hom (p.app a) g) : sq.LiftStruct :=
  boundedRightComponentLift d κLP s b p hp a i sq

/-- The actual component lift satisfies both original endpoint equations. -/
theorem originalComponentLift_equations {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : i.1.left ⟶ F.obj a} {g : i.1.right ⟶ G.obj a}
    (sq : CommSq f i.1.hom (p.app a) g) :
    i.1.hom ≫ (originalComponentLift d κLP s b p hp a i sq).l = f ∧
      (originalComponentLift d κLP s b p hp a i sq).l ≫ p.app a = g :=
  ⟨boundedRightComponentLift_left d κLP s b p hp a i sq,
    boundedRightComponentLift_right d κLP s b p hp a i sq⟩

/-- The actual full free square receives the same original natural-transformation lift structure. -/
def originalFreeLift {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : (originalFreeIArrow d κLP s a i).left ⟶ F}
    {g : (originalFreeIArrow d κLP s a i).right ⟶ G}
    (sq : CommSq f (originalFreeIArrow d κLP s a i).hom p g) : sq.LiftStruct :=
  boundedRightFreeLift d κLP s b p hp a i sq

/-- The actual transpose uses the native free/evaluation lift equivalence on the same record. -/
theorem originalFreeLift_transpose {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : (originalFreeIArrow d κLP s a i).left ⟶ F}
    {g : (originalFreeIArrow d κLP s a i).right ⟶ G}
    (sq : CommSq f (originalFreeIArrow d κLP s a i).hom p g) :
    (boundedRightFreeLiftTranspose d κLP s b p hp a i sq).l =
      (freeEvaluationAdjunction C κLP s.equivalence a).homEquiv i.1.right F
        (originalFreeLift d κLP s b p hp a i sq).l :=
  boundedRightFreeLiftTranspose_function d κLP s b p hp a i sq

/-- The whole inverse transpose recovers the original natural-transformation lift structure. -/
theorem originalFreeLift_inverse_transpose {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : (originalFreeIArrow d κLP s a i).left ⟶ F}
    {g : (originalFreeIArrow d κLP s a i).right ⟶ G}
    (sq : CommSq f (originalFreeIArrow d κLP s a i).hom p g) :
    (sq.rightAdjointLiftStructEquiv (freeEvaluationAdjunction C κLP s.equivalence a)).symm
        (boundedRightFreeLiftTranspose d κLP s b p hp a i sq) =
      originalFreeLift d κLP s b p hp a i sq :=
  boundedRightFreeLiftTranspose_inverse d κLP s b p hp a i sq

/-- All original index components of the whole free lift retain both original equations. -/
theorem originalFreeLift_equations {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : (originalFreeIArrow d κLP s a i).left ⟶ F}
    {g : (originalFreeIArrow d κLP s a i).right ⟶ G}
    (sq : CommSq f (originalFreeIArrow d κLP s a i).hom p g) (c : D) :
    (originalFreeIArrow d κLP s a i).hom.app c ≫
        (originalFreeLift d κLP s b p hp a i sq).l.app c = f.app c ∧
      (originalFreeLift d κLP s b p hp a i sq).l.app c ≫ p.app c = g.app c :=
  ⟨boundedRightFreeLift_left_components d κLP s b p hp a i sq c,
    boundedRightFreeLift_right_components d κLP s b p hp a i sq c⟩

end MathlibExtTest.FunctorInjectiveBoundedRightAcyclicity
