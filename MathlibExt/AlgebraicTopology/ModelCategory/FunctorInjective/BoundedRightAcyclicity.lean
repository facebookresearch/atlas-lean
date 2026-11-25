/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.BoundedGenerators
public import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import MathlibExt.CategoryTheory.Functor.SmallIndex

/-!
# Internal acyclicity of the actual bounded cofibration right class

Every original free I-image is an actual compact original diagram
cofibration at the full profile. Its whole representative isomorphism
transports lifting from the selected bounded family. Evaluation gives
the original base trivial-fibration class at every original index object.
No diagram WFS, exhaustion, acyclicity or model is an input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Presentable HomPowerAccessibility
open CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.FunctorInjective

attribute [local instance] CategoryTheory.Functor.EssentialIndexData.indexCategory

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} D C)
  (b : BoundedConstruction d κLP s.equivalence)

/-- The entire original free I-image Arrow uses the actual original free/evaluation value. -/
def originalFreeIArrow (a : D) (i : d.I.toSet) : Arrow (D ⥤ C) :=
  Arrow.mk ((HomPowerAccessibility.free C κLP s.equivalence a).map i.1.hom)

/-- Every original free I-image component is a base cofibration through its Hom coproduct. -/
theorem originalFreeIArrow_cofibration (a : D) (i : d.I.toSet) (c : D) :
    cofibrations C ((originalFreeIArrow d κLP s a i).hom.app c) := by
  let _ : LocallySmall.{w} D := s.locallySmallIndex
  let _ : HasCoproductsOfShape (a ⟶ c) C := homCoproducts C κLP s.equivalence a c
  have hi : cofibrations C i.1.hom := by
    have h := d.I.le_llp_rlp _ i.2
    rw [d.I_rlp, trivialFibrations_llp C] at h
    exact h
  let _ : IsStableUnderCoproducts.{w} (cofibrations C) := by
    rw [← trivialFibrations_llp C]
    infer_instance
  have hCoprod : MorphismProperty.coproducts.{w} (cofibrations C)
      ((originalFreeIArrow d κLP s a i).hom.app c) := by
    let A := Discrete.functor (fun _ : a ⟶ c ↦ i.1.left)
    let B := Discrete.functor (fun _ : a ⟶ c ↦ i.1.right)
    let f : A ⟶ B := Discrete.natTrans (fun _ ↦ i.1.hom)
    have hf : (cofibrations C).colimitsOfShape (Discrete (a ⟶ c)) (colimMap f) :=
      colimitsOfShape_colimMap f (fun _ ↦ hi)
    have hActual : colimMap f = (originalFreeIArrow d κLP s a i).hom.app c := by
      apply Sigma.hom_ext
      intro h
      simp [A, B, f, originalFreeIArrow, HomPowerAccessibility.free]
    rw [hActual] at hf
    exact coproducts_of_small _ _ hf
  exact (cofibrations C).coproducts_le _ hCoprod

/-- Every original free I-source component is compact at the actual chosen profile. -/
theorem originalFreeIArrow_source_component_presentable (a : D) (i : d.I.toSet) (c : D) :
    IsCardinalPresentable ((originalFreeIArrow d κLP s a i).left.obj c) b.cardinal := by
  let _ : IsCardinalPresentable i.1.left b.cardinal := b.profile.sourceI i
  exact homCopower_presentable C κLP s.equivalence c a b.cardinal
    (b.original_hom_bound a c) i.1.left

/-- Every original free I-target component is compact at that same actual profile. -/
theorem originalFreeIArrow_target_component_presentable (a : D) (i : d.I.toSet) (c : D) :
    IsCardinalPresentable ((originalFreeIArrow d κLP s a i).right.obj c) b.cardinal := by
  let _ : IsCardinalPresentable i.1.right b.cardinal := b.profile.targetI i
  exact homCopower_presentable C κLP s.equivalence c a b.cardinal
    (b.original_hom_bound a c) i.1.right

/-- The entire original free I-source diagram is compact by the actual whole/component criterion. -/
theorem originalFreeIArrow_source_presentable (a : D) (i : d.I.toSet) :
    IsCardinalPresentable (originalFreeIArrow d κLP s a i).left b.cardinal :=
  (b.profile.criterion (originalFreeIArrow d κLP s a i).left).mpr
    (originalFreeIArrow_source_component_presentable d κLP s b a i)

/-- The entire original free I-target diagram is compact by that same criterion. -/
theorem originalFreeIArrow_target_presentable (a : D) (i : d.I.toSet) :
    IsCardinalPresentable (originalFreeIArrow d κLP s a i).right b.cardinal :=
  (b.profile.criterion (originalFreeIArrow d κLP s a i).right).mpr
    (originalFreeIArrow_target_component_presentable d κLP s b a i)

/-- Every actual original free I-image belongs to the original compact diagram class. -/
theorem originalFreeIArrow_compact (a : D) (i : d.I.toSet) :
    compactCofibrationArrows D C b.cardinal (originalFreeIArrow d κLP s a i) :=
  ⟨originalFreeIArrow_cofibration d κLP s a i,
    originalFreeIArrow_source_presentable d κLP s b a i,
    originalFreeIArrow_target_presentable d κLP s b a i⟩

/-- The original free I-image chooses its actual original bounded-family representative. -/
def originalFreeIRepresentative (a : D) (i : d.I.toSet) : b.family.index :=
  b.family.representative (originalFreeIArrow d κLP s a i)
    (originalFreeIArrow_compact d κLP s b a i)

/-- The complete free-I comparison is an actual whole original diagram Arrow iso. -/
def originalFreeIRepresentativeIso (a : D) (i : d.I.toSet) :
    originalFreeIArrow d κLP s a i ≅ b.family.arrow
      (originalFreeIRepresentative d κLP s b a i) :=
  b.family.representativeIso (originalFreeIArrow d κLP s a i)
    (originalFreeIArrow_compact d κLP s b a i)

/-- Bounded-family right lifting implies lifting against every original free I-image. -/
theorem boundedRight_freeI_lifting {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet) :
    HasLiftingProperty (originalFreeIArrow d κLP s a i).hom p := by
  let k := originalFreeIRepresentative d κLP s b a i
  let _ : HasLiftingProperty (b.family.arrow k).hom p := hp _ (b.family.arrow_mem k)
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (originalFreeIRepresentativeIso d κLP s b a i) p).mpr inferInstance

/-- Native free/evaluation transposition gives original base I lifting at every original object. -/
theorem boundedRight_component_I_lifting {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet) :
    HasLiftingProperty i.1.hom (p.app a) := by
  have h := boundedRight_freeI_lifting d κLP s b p hp a i
  exact ((freeEvaluationAdjunction C κLP s.equivalence a).hasLiftingProperty_iff i.1.hom p).mp h

include d κLP s in
/-- The actual bounded right class consists of objectwise original base trivial fibrations. -/
theorem boundedRight_le_objectwise_trivialFibrations :
    b.family.generators.rlp ≤ (trivialFibrations C).functorCategory D := by
  intro F G p hp a
  rw [← d.I_rlp]
  intro A B i hi
  exact boundedRight_component_I_lifting d κLP s b p hp a ⟨Arrow.mk i, hi⟩

include d κLP s in
/-- The needed right-class acyclicity is derived internally on every original diagram arrow. -/
theorem boundedRight_le_objectwise_weak :
    b.family.generators.rlp ≤ (weakEquivalences C).functorCategory D := by
  intro F G p hp a
  exact (boundedRight_le_objectwise_trivialFibrations d κLP s b p hp a).2

/-- Every original bounded right map is an original base fibration at each original object. -/
theorem boundedRight_component_fibration {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) : fibrations C (p.app a) :=
  (boundedRight_le_objectwise_trivialFibrations d κLP s b p hp a).1

/-- Every original bounded right map is weak at each original object. -/
theorem boundedRight_component_weak {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) : weakEquivalences C (p.app a) :=
  boundedRight_le_objectwise_weak d κLP s b p hp a

/-- The actual lift of an original component square is chosen from the proved original lifting. -/
def boundedRightComponentLift {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : i.1.left ⟶ F.obj a} {g : i.1.right ⟶ G.obj a}
    (sq : CommSq f i.1.hom (p.app a) g) : sq.LiftStruct := by
  let _ : HasLiftingProperty i.1.hom (p.app a) :=
    boundedRight_component_I_lifting d κLP s b p hp a i
  exact (inferInstance : sq.HasLift).exists_lift.some

/-- The actual original component lift satisfies its complete source equation. -/
theorem boundedRightComponentLift_left {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : i.1.left ⟶ F.obj a} {g : i.1.right ⟶ G.obj a}
    (sq : CommSq f i.1.hom (p.app a) g) :
    i.1.hom ≫ (boundedRightComponentLift d κLP s b p hp a i sq).l = f :=
  (boundedRightComponentLift d κLP s b p hp a i sq).fac_left

/-- The actual original component lift satisfies its complete target equation. -/
theorem boundedRightComponentLift_right {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : i.1.left ⟶ F.obj a} {g : i.1.right ⟶ G.obj a}
    (sq : CommSq f i.1.hom (p.app a) g) :
    (boundedRightComponentLift d κLP s b p hp a i sq).l ≫ p.app a = g :=
  (boundedRightComponentLift d κLP s b p hp a i sq).fac_right

/-- An entire original free-I square receives an actual natural-transformation lift. -/
def boundedRightFreeLift {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : (originalFreeIArrow d κLP s a i).left ⟶ F}
    {g : (originalFreeIArrow d κLP s a i).right ⟶ G}
    (sq : CommSq f (originalFreeIArrow d κLP s a i).hom p g) : sq.LiftStruct := by
  let _ : HasLiftingProperty (originalFreeIArrow d κLP s a i).hom p :=
    boundedRight_freeI_lifting d κLP s b p hp a i
  exact (inferInstance : sq.HasLift).exists_lift.some

/-- The native adjunction transports that same original whole free lift to its component square. -/
def boundedRightFreeLiftTranspose {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : (originalFreeIArrow d κLP s a i).left ⟶ F}
    {g : (originalFreeIArrow d κLP s a i).right ⟶ G}
    (sq : CommSq f (originalFreeIArrow d κLP s a i).hom p g) :
    (sq.right_adjoint (freeEvaluationAdjunction C κLP s.equivalence a)).LiftStruct :=
  (sq.rightAdjointLiftStructEquiv (freeEvaluationAdjunction C κLP s.equivalence a))
    (boundedRightFreeLift d κLP s b p hp a i sq)

/-- The whole forward lift transpose is exactly the original free/evaluation Hom function. -/
theorem boundedRightFreeLiftTranspose_function {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : (originalFreeIArrow d κLP s a i).left ⟶ F}
    {g : (originalFreeIArrow d κLP s a i).right ⟶ G}
    (sq : CommSq f (originalFreeIArrow d κLP s a i).hom p g) :
    (boundedRightFreeLiftTranspose d κLP s b p hp a i sq).l =
      (freeEvaluationAdjunction C κLP s.equivalence a).homEquiv i.1.right F
        (boundedRightFreeLift d κLP s b p hp a i sq).l := rfl

/-- Inverting the actual full lift transpose recovers the same original free lift record. -/
theorem boundedRightFreeLiftTranspose_inverse {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : (originalFreeIArrow d κLP s a i).left ⟶ F}
    {g : (originalFreeIArrow d κLP s a i).right ⟶ G}
    (sq : CommSq f (originalFreeIArrow d κLP s a i).hom p g) :
    (sq.rightAdjointLiftStructEquiv (freeEvaluationAdjunction C κLP s.equivalence a)).symm
        (boundedRightFreeLiftTranspose d κLP s b p hp a i sq) =
      boundedRightFreeLift d κLP s b p hp a i sq :=
  (sq.rightAdjointLiftStructEquiv
      (freeEvaluationAdjunction C κLP s.equivalence a)).symm_apply_apply _

/-- The whole lifted free square retains every original source component equation. -/
theorem boundedRightFreeLift_left_components {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : (originalFreeIArrow d κLP s a i).left ⟶ F}
    {g : (originalFreeIArrow d κLP s a i).right ⟶ G}
    (sq : CommSq f (originalFreeIArrow d κLP s a i).hom p g) (c : D) :
    (originalFreeIArrow d κLP s a i).hom.app c ≫
      (boundedRightFreeLift d κLP s b p hp a i sq).l.app c = f.app c :=
  congr_app (boundedRightFreeLift d κLP s b p hp a i sq).fac_left c

/-- The whole lifted free square retains every original target component equation. -/
theorem boundedRightFreeLift_right_components {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : (originalFreeIArrow d κLP s a i).left ⟶ F}
    {g : (originalFreeIArrow d κLP s a i).right ⟶ G}
    (sq : CommSq f (originalFreeIArrow d κLP s a i).hom p g) (c : D) :
    (boundedRightFreeLift d κLP s b p hp a i sq).l.app c ≫ p.app c = g.app c :=
  congr_app (boundedRightFreeLift d κLP s b p hp a i sq).fac_right c

/-- The original whole lift is natural on every original index morphism. -/
theorem boundedRightFreeLift_naturality {F G : D ⥤ C} (p : F ⟶ G)
    (hp : b.family.generators.rlp p) (a : D) (i : d.I.toSet)
    {f : (originalFreeIArrow d κLP s a i).left ⟶ F}
    {g : (originalFreeIArrow d κLP s a i).right ⟶ G}
    (sq : CommSq f (originalFreeIArrow d κLP s a i).hom p g)
    {c e : D} (h : c ⟶ e) :
    (originalFreeIArrow d κLP s a i).right.map h ≫
        (boundedRightFreeLift d κLP s b p hp a i sq).l.app e =
      (boundedRightFreeLift d κLP s b p hp a i sq).l.app c ≫ F.map h :=
  (boundedRightFreeLift d κLP s b p hp a i sq).l.naturality h

end HomotopicalAlgebra.FunctorInjective
