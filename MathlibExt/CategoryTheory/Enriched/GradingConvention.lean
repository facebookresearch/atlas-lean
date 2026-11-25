/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.CentralGradedInputActions
public import MathlibExt.CategoryTheory.Enriched.GradedComponentActions
public import MathlibExt.CategoryTheory.Enriched.GradeNaturality
public import MathlibExt.CategoryTheory.Enriched.MappingEndOrientation
public import MathlibExt.CategoryTheory.Enriched.GradedInputComposition
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedEnd

/-!
The original end relation and the positive canonical center grade have explicit
inverse component normalizations. Genuine coefficient and input actions are
retained. The conditional end comparison uses only that original end's products
and equalizer; it adds no end hypothesis to Kan construction.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory BraidedCategory Limits
open scoped MonoidalClosed

namespace CategoryTheory.GradingConvention

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]

/-- The coefficient arrow acts between the reverse center grades. -/
def reverseCenterMap {K L : V} (h : K ⟶ L) :
    @Center.ofBraidedObj _ _ _ (reverseBraiding _) K ⟶
      @Center.ofBraidedObj _ _ _ (reverseBraiding _) L where
  f := h
  comm H := braiding_inv_naturality_left h H

/-- The original full reverse Center Map f identity. -/
@[simp]
theorem reverseCenterMap_f {K L : V} (h : K ⟶ L) : (reverseCenterMap h).f = h := rfl

variable [MonoidalClosed V] {A : Type uA} [EnrichedCategory V A]
  {F G : EnrichedFunctor V A V}

/-- Convert reverse grading to positive grading with the same grade-first components. -/
@[no_expose]
def positiveOfReverse {K : V}
    (t : GradedNatTrans (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) F G) :
    GradedNatTrans ((Center.ofBraided V).obj K) F G :=
  GradedNatTrans.ofGradeFirstComponents ((Center.ofBraided V).obj K)
    (GradedNatTrans.gradeFirstComponent (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) t)
    (fun a b => GradedNatTrans.gradeFirstComponent_naturality
      (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) t a b)

/-- Convert positive grading to reverse grading with the same grade-first components. -/
@[no_expose]
def reverseOfPositive {K : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj K) F G) :
    GradedNatTrans (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) F G :=
  GradedNatTrans.ofGradeFirstComponents (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K)
    (GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj K) t)
    (fun a b => GradedNatTrans.gradeFirstComponent_naturality
      ((Center.ofBraided V).obj K) t a b)

set_option backward.isDefEq.respectTransparency false in
/-- The original full positive Of Reverse app identity. -/
theorem positiveOfReverse_app {K : V}
    (t : GradedNatTrans (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) F G) (a : A) :
    (positiveOfReverse t).app a = MonoidalClosed.curry
      ((β_ K (F.obj a)).inv ≫ (β_ (F.obj a) K).inv ≫ MonoidalClosed.uncurry (t.app a)) := by
  change (GradedNatTrans.ofGradeFirstComponents ((Center.ofBraided V).obj K) _ _).app a = _
  rw [GradedNatTrans.ofGradeFirstComponents_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original full reverse Of Positive app identity. -/
theorem reverseOfPositive_app {K : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj K) F G) (a : A) :
    (reverseOfPositive t).app a = MonoidalClosed.curry
      ((β_ (F.obj a) K).hom ≫ (β_ K (F.obj a)).hom ≫ MonoidalClosed.uncurry (t.app a)) := by
  change (GradedNatTrans.ofGradeFirstComponents
    (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) _ _).app a = _
  rw [GradedNatTrans.ofGradeFirstComponents_app]
  rfl

/-- The original full positive Of Reverse grade First identity. -/
theorem positiveOfReverse_gradeFirst {K : V}
    (t : GradedNatTrans (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) F G) (a : A) :
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj K) (positiveOfReverse t) a =
      GradedNatTrans.gradeFirstComponent (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) t a :=
  GradedNatTrans.ofGradeFirstComponents_gradeFirstComponent _ _ _ a

/-- The original full reverse Of Positive grade First identity. -/
theorem reverseOfPositive_gradeFirst {K : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj K) F G) (a : A) :
    GradedNatTrans.gradeFirstComponent
        (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) (reverseOfPositive t) a =
      GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj K) t a :=
  GradedNatTrans.ofGradeFirstComponents_gradeFirstComponent _ _ _ a

/-- The original full reverse positive identity. -/
theorem reverse_positive {K : V}
    (t : GradedNatTrans (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) F G) :
    reverseOfPositive (positiveOfReverse t) = t := by
  apply GradedNatTrans.gradeFirstComponent_ext (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K)
  intro a
  rw [reverseOfPositive_gradeFirst, positiveOfReverse_gradeFirst]

/-- The original full positive reverse identity. -/
theorem positive_reverse {K : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj K) F G) :
    positiveOfReverse (reverseOfPositive t) = t := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj K)
  intro a
  rw [positiveOfReverse_gradeFirst, reverseOfPositive_gradeFirst]

/-- Positive and reverse grading have the constructed inverse conversions. -/
@[no_expose]
def conventionEquiv (K : V) :
    GradedNatTrans (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) F G ≃
      GradedNatTrans ((Center.ofBraided V).obj K) F G where
  toFun := positiveOfReverse
  invFun := reverseOfPositive
  left_inv := reverse_positive
  right_inv := positive_reverse

/-- The original full positive Of Reverse regrade identity. -/
theorem positiveOfReverse_regrade {K L : V} (h : K ⟶ L)
    (t : GradedNatTrans (@Center.ofBraidedObj _ _ _ (reverseBraiding _) L) F G) :
    positiveOfReverse (GradedNatTrans.regrade (reverseCenterMap h) t) =
      GradedNatTrans.regrade ((Center.ofBraided V).map h) (positiveOfReverse t) := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj K)
  intro a
  rw [positiveOfReverse_gradeFirst, GradedNatTrans.gradeFirstComponent_regrade,
    GradedNatTrans.gradeFirstComponent_regrade, positiveOfReverse_gradeFirst]
  rfl

/-- The original full reverse Of Positive regrade identity. -/
theorem reverseOfPositive_regrade {K L : V} (h : K ⟶ L)
    (t : GradedNatTrans ((Center.ofBraided V).obj L) F G) :
    reverseOfPositive (GradedNatTrans.regrade ((Center.ofBraided V).map h) t) =
      GradedNatTrans.regrade (reverseCenterMap h) (reverseOfPositive t) := by
  apply GradedNatTrans.gradeFirstComponent_ext (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K)
  intro a
  rw [reverseOfPositive_gradeFirst, GradedNatTrans.gradeFirstComponent_regrade,
    GradedNatTrans.gradeFirstComponent_regrade, reverseOfPositive_gradeFirst]
  rfl

section Inputs

variable {F' F₀ G₀ G' : EnrichedFunctorCat V A}

/-- The original full positive Of Reverse precomp identity. -/
theorem positiveOfReverse_precomp {K : V} (p : F' ⟶ F₀)
    (t : GradedNatTrans (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K)
      F₀.toEnrichedFunctor G₀.toEnrichedFunctor) :
    positiveOfReverse
        (EnrichedFunctorCat.gradedPrecomp (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) p t) =
      EnrichedFunctorCat.gradedPrecomp ((Center.ofBraided V).obj K) p (positiveOfReverse t) := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj K)
  intro a
  rw [positiveOfReverse_gradeFirst, EnrichedFunctorCat.gradeFirstComponent_gradedPrecomp,
    EnrichedFunctorCat.gradeFirstComponent_gradedPrecomp,
    positiveOfReverse_gradeFirst]
  rfl

/-- The original full positive Of Reverse postcomp identity. -/
theorem positiveOfReverse_postcomp {K : V}
    (t : GradedNatTrans (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K)
      F₀.toEnrichedFunctor G₀.toEnrichedFunctor) (q : G₀ ⟶ G') :
    positiveOfReverse
        (EnrichedFunctorCat.gradedPostcomp (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) t q) =
      EnrichedFunctorCat.gradedPostcomp ((Center.ofBraided V).obj K) (positiveOfReverse t) q := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj K)
  intro a
  rw [positiveOfReverse_gradeFirst, EnrichedFunctorCat.gradeFirstComponent_gradedPostcomp,
    EnrichedFunctorCat.gradeFirstComponent_gradedPostcomp,
    positiveOfReverse_gradeFirst]
  rfl

/-- The original full reverse Of Positive precomp identity. -/
theorem reverseOfPositive_precomp {K : V} (p : F' ⟶ F₀)
    (t : GradedNatTrans ((Center.ofBraided V).obj K) F₀.toEnrichedFunctor G₀.toEnrichedFunctor) :
    reverseOfPositive (EnrichedFunctorCat.gradedPrecomp ((Center.ofBraided V).obj K) p t) =
      EnrichedFunctorCat.gradedPrecomp (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K)
        p (reverseOfPositive t) := by
  apply GradedNatTrans.gradeFirstComponent_ext (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K)
  intro a
  rw [reverseOfPositive_gradeFirst, EnrichedFunctorCat.gradeFirstComponent_gradedPrecomp,
    EnrichedFunctorCat.gradeFirstComponent_gradedPrecomp,
    reverseOfPositive_gradeFirst]
  rfl

/-- The original full reverse Of Positive postcomp identity. -/
theorem reverseOfPositive_postcomp {K : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj K) F₀.toEnrichedFunctor G₀.toEnrichedFunctor)
    (q : G₀ ⟶ G') :
    reverseOfPositive (EnrichedFunctorCat.gradedPostcomp ((Center.ofBraided V).obj K) t q) =
      EnrichedFunctorCat.gradedPostcomp (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K)
        (reverseOfPositive t) q := by
  apply GradedNatTrans.gradeFirstComponent_ext (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K)
  intro a
  rw [reverseOfPositive_gradeFirst, EnrichedFunctorCat.gradeFirstComponent_gradedPostcomp,
    EnrichedFunctorCat.gradeFirstComponent_gradedPostcomp,
    reverseOfPositive_gradeFirst]
  rfl

end Inputs

set_option backward.isDefEq.respectTransparency false in
/-- The original full positive Of Reverse app tensor Unit identity. -/
theorem positiveOfReverse_app_tensorUnit
    (t : GradedNatTrans (@Center.ofBraidedObj _ _ _ (reverseBraiding _) (𝟙_ V)) F G) (a : A) :
    (positiveOfReverse t).app a = t.app a := by
  rw [positiveOfReverse_app, braiding_inv_tensorUnit_left, braiding_inv_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  exact MonoidalClosed.curry_uncurry (t.app a)

set_option backward.isDefEq.respectTransparency false in
/-- The original full reverse Of Positive app tensor Unit identity. -/
theorem reverseOfPositive_app_tensorUnit
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) (a : A) :
    (reverseOfPositive t).app a = t.app a := by
  rw [reverseOfPositive_app, braiding_tensorUnit_right, braiding_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  exact MonoidalClosed.curry_uncurry (t.app a)

section OriginalEnd

variable (W X : EnrichedFunctor V A V)
  [HasProduct (Enriched.weightedEnd.objects W X)]
  [HasProduct (Enriched.weightedEnd.relations W X)]
  [HasEqualizer (Enriched.weightedEnd.leftMap W X) (Enriched.weightedEnd.rightMap W X)]

/-- The complete weighted-end projections give the reverse graded transformation. -/
@[no_expose]
def reverseEndProjections :
    GradedNatTrans
      (@Center.ofBraidedObj _ _ _ (reverseBraiding _) (Enriched.weightedEnd W X)) W X :=
  MappingEndOrientationProbe.reverseGradeOfEndRelations (Enriched.weightedEnd.π W X)
    (Enriched.weightedEnd.condition W X)

/-- The original full reverse End Projections app identity. -/
theorem reverseEndProjections_app (a : A) :
    (reverseEndProjections W X).app a = Enriched.weightedEnd.π W X a :=
  MappingEndOrientationProbe.reverseGradeOfEndRelations_app _ _ a

/-- Normalize the complete weighted-end projections to positive grading. -/
@[no_expose]
def positiveEndProjections :
    GradedNatTrans ((Center.ofBraided V).obj (Enriched.weightedEnd W X)) W X :=
  positiveOfReverse (reverseEndProjections W X)

/-- The original full positive End Projections app identity. -/
theorem positiveEndProjections_app (a : A) :
    (positiveEndProjections W X).app a = MonoidalClosed.curry
      ((β_ (Enriched.weightedEnd W X) (W.obj a)).inv ≫
        (β_ (W.obj a) (Enriched.weightedEnd W X)).inv ≫
        MonoidalClosed.uncurry (Enriched.weightedEnd.π W X a)) := by
  change (positiveOfReverse (reverseEndProjections W X)).app a = _
  rw [positiveOfReverse_app, reverseEndProjections_app]

/-- Convert the given end arrow to its full positive graded transformation. -/
@[no_expose]
def endToPositive {K : V} (f : K ⟶ Enriched.weightedEnd W X) :
    GradedNatTrans ((Center.ofBraided V).obj K) W X :=
  positiveOfReverse
    (GradedNatTrans.regrade (reverseCenterMap f) (reverseEndProjections W X))

/-- The original full end To Positive reverse app identity. -/
theorem endToPositive_reverse_app {K : V} (f : K ⟶ Enriched.weightedEnd W X) (a : A) :
    (reverseOfPositive (endToPositive W X f)).app a = f ≫ Enriched.weightedEnd.π W X a := by
  change (reverseOfPositive (positiveOfReverse _)).app a = _
  rw [reverse_positive, GradedNatTrans.regrade_app, reverseEndProjections_app]
  rfl

/-- The original full end To Positive app identity. -/
theorem endToPositive_app {K : V} (f : K ⟶ Enriched.weightedEnd W X) (a : A) :
    (endToPositive W X f).app a = MonoidalClosed.curry
      ((β_ K (W.obj a)).inv ≫ (β_ (W.obj a) K).inv ≫
        MonoidalClosed.uncurry (f ≫ Enriched.weightedEnd.π W X a)) := by
  change (positiveOfReverse _).app a = _
  rw [positiveOfReverse_app, GradedNatTrans.regrade_app, reverseEndProjections_app]
  rfl

/-- Lift the given positive transformation through the original weighted end. -/
@[no_expose]
def endFromPositive {K : V} (t : GradedNatTrans ((Center.ofBraided V).obj K) W X) :
    K ⟶ Enriched.weightedEnd W X :=
  Enriched.weightedEnd.lift W X (fun a => (reverseOfPositive t).app a)
    (fun a b => (MappingEndOrientationProbe.reverseAmbientNaturality_iff_endRelation
      (fun a => (reverseOfPositive t).app a) a b).1 ((reverseOfPositive t).naturality a b))

/-- The original full end From Positive π identity. -/
theorem endFromPositive_π {K : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj K) W X) (a : A) :
    endFromPositive W X t ≫ Enriched.weightedEnd.π W X a = (reverseOfPositive t).app a :=
  Enriched.weightedEnd.lift_π W X _ _ a

/-- The original full end From Positive to Positive identity. -/
theorem endFromPositive_toPositive {K : V} (f : K ⟶ Enriched.weightedEnd W X) :
    endFromPositive W X (endToPositive W X f) = f := by
  apply Enriched.weightedEnd.hom_ext W X
  intro a
  rw [endFromPositive_π, endToPositive_reverse_app]

/-- The original full end To Positive from Positive identity. -/
theorem endToPositive_fromPositive {K : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj K) W X) :
    endToPositive W X (endFromPositive W X t) = t := by
  apply (conventionEquiv (F := W) (G := X) K).symm.injective
  apply GradedNatTrans.ext
  funext a
  change (reverseOfPositive (endToPositive W X (endFromPositive W X t))).app a =
    (reverseOfPositive t).app a
  rw [endToPositive_reverse_app, endFromPositive_π]

/-- The original end arrows and positive graded transformations have inverse conversions. -/
@[no_expose]
def endHomEquiv (K : V) : (K ⟶ Enriched.weightedEnd W X) ≃
    GradedNatTrans ((Center.ofBraided V).obj K) W X where
  toFun := endToPositive W X
  invFun := endFromPositive W X
  left_inv := endFromPositive_toPositive W X
  right_inv := endToPositive_fromPositive W X

private theorem endHomEquiv_apply_private {K : V} (f : K ⟶ Enriched.weightedEnd W X) :
    endHomEquiv W X K f = endToPositive W X f := rfl

/-- The original full end Hom Equiv apply identity. -/
theorem endHomEquiv_apply {K : V} (f : K ⟶ Enriched.weightedEnd W X) :
    endHomEquiv W X K f = endToPositive W X f := endHomEquiv_apply_private W X f

private theorem endHomEquiv_symm_apply_private {K : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj K) W X) :
    (endHomEquiv W X K).symm t = endFromPositive W X t := rfl

/-- The original full end Hom Equiv symm apply identity. -/
theorem endHomEquiv_symm_apply {K : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj K) W X) :
    (endHomEquiv W X K).symm t = endFromPositive W X t :=
  endHomEquiv_symm_apply_private W X t

/-- The original full end To Positive naturality identity. -/
theorem endToPositive_naturality {K L : V} (h : K ⟶ L) (f : L ⟶ Enriched.weightedEnd W X) :
    endToPositive W X (h ≫ f) =
      GradedNatTrans.regrade ((Center.ofBraided V).map h) (endToPositive W X f) := by
  apply (conventionEquiv (F := W) (G := X) K).symm.injective
  apply GradedNatTrans.ext
  funext a
  change (reverseOfPositive (endToPositive W X (h ≫ f))).app a =
    (reverseOfPositive (GradedNatTrans.regrade ((Center.ofBraided V).map h)
      (endToPositive W X f))).app a
  rw [endToPositive_reverse_app, reverseOfPositive_regrade, GradedNatTrans.regrade_app,
    endToPositive_reverse_app]
  exact Category.assoc _ _ _

/-- The original full end From Positive naturality identity. -/
theorem endFromPositive_naturality {K L : V} (h : K ⟶ L)
    (t : GradedNatTrans ((Center.ofBraided V).obj L) W X) :
    endFromPositive W X (GradedNatTrans.regrade ((Center.ofBraided V).map h) t) =
      h ≫ endFromPositive W X t := by
  apply Enriched.weightedEnd.hom_ext W X
  intro a
  rw [endFromPositive_π, reverseOfPositive_regrade, GradedNatTrans.regrade_app,
    Category.assoc, endFromPositive_π]
  rfl

/-- The original full end To Positive app tensor Unit identity. -/
theorem endToPositive_app_tensorUnit (f : 𝟙_ V ⟶ Enriched.weightedEnd W X) (a : A) :
    (endToPositive W X f).app a = f ≫ Enriched.weightedEnd.π W X a := by
  change (positiveOfReverse _).app a = _
  rw [positiveOfReverse_app_tensorUnit, GradedNatTrans.regrade_app,
    reverseEndProjections_app]
  rfl

/-- The original full end From Positive tensor Unit π identity. -/
theorem endFromPositive_tensorUnit_π
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W X) (a : A) :
    endFromPositive W X t ≫ Enriched.weightedEnd.π W X a = t.app a := by
  rw [endFromPositive_π, reverseOfPositive_app_tensorUnit]

/-- The original end represents the full positive graded-transformation presheaf. -/
@[no_expose]
def endNatTransYonedaIso :
    yoneda.obj (Enriched.weightedEnd W X) ⋙ uliftFunctor.{max uA vV, vV} ≅
      enrichedNatTransYoneda W X ⋙ uliftFunctor.{max uA vV, max uA vV} :=
  NatIso.ofComponents
    (fun M => (Equiv.ulift.trans ((endHomEquiv W X M.unop).trans Equiv.ulift.symm)).toIso)
    (by
      intro M N h
      apply ConcreteCategory.ext_apply
      intro f
      apply ULift.ext
      change endToPositive W X (h.unop ≫ f.down) =
        GradedNatTrans.regrade ((Center.ofBraided V).map h.unop) (endToPositive W X f.down)
      exact endToPositive_naturality W X h.unop f.down)

private theorem endNatTransYonedaIso_hom_app_private (M : Vᵒᵖ)
    (f : ULift.{max uA vV} (M.unop ⟶ Enriched.weightedEnd W X)) :
    (endNatTransYonedaIso W X).hom.app M f = ULift.up (endToPositive W X f.down) := rfl

/-- The original full end Nat Trans Yoneda Iso hom app identity. -/
theorem endNatTransYonedaIso_hom_app (M : Vᵒᵖ)
    (f : ULift.{max uA vV} (M.unop ⟶ Enriched.weightedEnd W X)) :
    (endNatTransYonedaIso W X).hom.app M f = ULift.up (endToPositive W X f.down) :=
  endNatTransYonedaIso_hom_app_private W X M f

private theorem endNatTransYonedaIso_inv_app_private (M : Vᵒᵖ)
    (t : ULift.{max uA vV} ((enrichedNatTransYoneda W X).obj M)) :
    (endNatTransYonedaIso W X).inv.app M t = ULift.up (endFromPositive W X t.down) := rfl

/-- The original full end Nat Trans Yoneda Iso inv app identity. -/
theorem endNatTransYonedaIso_inv_app (M : Vᵒᵖ)
    (t : ULift.{max uA vV} ((enrichedNatTransYoneda W X).obj M)) :
    (endNatTransYonedaIso W X).inv.app M t = ULift.up (endFromPositive W X t.down) :=
  endNatTransYonedaIso_inv_app_private W X M t

end OriginalEnd

section EndTarget

variable (W X Y : EnrichedFunctor V A V)
  [HasProduct (Enriched.weightedEnd.objects W X)]
  [HasProduct (Enriched.weightedEnd.relations W X)]
  [HasEqualizer (Enriched.weightedEnd.leftMap W X) (Enriched.weightedEnd.rightMap W X)]
  [HasProduct (Enriched.weightedEnd.objects W Y)]
  [HasProduct (Enriched.weightedEnd.relations W Y)]
  [HasEqualizer (Enriched.weightedEnd.leftMap W Y) (Enriched.weightedEnd.rightMap W Y)]

/-- The original full end To Positive map Diagram identity. -/
theorem endToPositive_mapDiagram {K : V} (f : K ⟶ Enriched.weightedEnd W X)
    (p : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) X Y) :
    endToPositive W Y (f ≫ Enriched.weightedEnd.mapDiagram W X Y p) =
      EnrichedFunctorCat.gradedPostcomp (F := ⟨W⟩) (G := ⟨X⟩) (H := ⟨Y⟩)
        ((Center.ofBraided V).obj K) (endToPositive W X f) p := by
  apply (conventionEquiv (F := W) (G := Y) K).symm.injective
  apply GradedNatTrans.ext
  funext a
  change (reverseOfPositive (endToPositive W Y
    (f ≫ Enriched.weightedEnd.mapDiagram W X Y p))).app a =
      (reverseOfPositive (EnrichedFunctorCat.gradedPostcomp (F := ⟨W⟩) (G := ⟨X⟩) (H := ⟨Y⟩)
        ((Center.ofBraided V).obj K) (endToPositive W X f) p)).app a
  rw [endToPositive_reverse_app, reverseOfPositive_postcomp,
    EnrichedFunctorCat.gradedPostcomp_app, endToPositive_reverse_app,
    Category.assoc, Enriched.weightedEnd.mapDiagram_π]
  exact (Category.assoc _ _ _).symm

/-- The original full end From Positive map Diagram identity. -/
theorem endFromPositive_mapDiagram {K : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj K) W X)
    (p : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) X Y) :
    endFromPositive W Y (EnrichedFunctorCat.gradedPostcomp (F := ⟨W⟩) (G := ⟨X⟩) (H := ⟨Y⟩)
      ((Center.ofBraided V).obj K) t p) =
      endFromPositive W X t ≫ Enriched.weightedEnd.mapDiagram W X Y p := by
  apply Enriched.weightedEnd.hom_ext W Y
  intro a
  rw [endFromPositive_π, reverseOfPositive_postcomp, EnrichedFunctorCat.gradedPostcomp_app,
    Category.assoc, Enriched.weightedEnd.mapDiagram_π, ← Category.assoc, endFromPositive_π]
  rfl

end EndTarget

section EndSource

variable (W' W X : EnrichedFunctor V A V)
  [HasProduct (Enriched.weightedEnd.objects W X)]
  [HasProduct (Enriched.weightedEnd.relations W X)]
  [HasEqualizer (Enriched.weightedEnd.leftMap W X) (Enriched.weightedEnd.rightMap W X)]
  [HasProduct (Enriched.weightedEnd.objects W' X)]
  [HasProduct (Enriched.weightedEnd.relations W' X)]
  [HasEqualizer (Enriched.weightedEnd.leftMap W' X) (Enriched.weightedEnd.rightMap W' X)]

/-- The original full end To Positive map Weight identity. -/
theorem endToPositive_mapWeight {K : V} (f : K ⟶ Enriched.weightedEnd W X)
    (p : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W' W) :
    endToPositive W' X (f ≫ Enriched.weightedEnd.mapWeight W X W' p) =
      EnrichedFunctorCat.gradedPrecomp (F := ⟨W'⟩) (G := ⟨W⟩) (H := ⟨X⟩)
        ((Center.ofBraided V).obj K) p (endToPositive W X f) := by
  apply (conventionEquiv (F := W') (G := X) K).symm.injective
  apply GradedNatTrans.ext
  funext a
  change (reverseOfPositive (endToPositive W' X
    (f ≫ Enriched.weightedEnd.mapWeight W X W' p))).app a =
      (reverseOfPositive (EnrichedFunctorCat.gradedPrecomp (F := ⟨W'⟩) (G := ⟨W⟩) (H := ⟨X⟩)
        ((Center.ofBraided V).obj K) p (endToPositive W X f))).app a
  rw [endToPositive_reverse_app, reverseOfPositive_precomp,
    EnrichedFunctorCat.gradedPrecomp_app, endToPositive_reverse_app,
    Category.assoc, Enriched.weightedEnd.mapWeight_π]
  exact (Category.assoc _ _ _).symm

/-- The original full end From Positive map Weight identity. -/
theorem endFromPositive_mapWeight {K : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj K) W X)
    (p : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W' W) :
    endFromPositive W' X (EnrichedFunctorCat.gradedPrecomp (F := ⟨W'⟩) (G := ⟨W⟩) (H := ⟨X⟩)
      ((Center.ofBraided V).obj K) p t) =
      endFromPositive W X t ≫ Enriched.weightedEnd.mapWeight W X W' p := by
  apply Enriched.weightedEnd.hom_ext W' X
  intro a
  rw [endFromPositive_π, reverseOfPositive_precomp, EnrichedFunctorCat.gradedPrecomp_app,
    Category.assoc, Enriched.weightedEnd.mapWeight_π, ← Category.assoc, endFromPositive_π]
  rfl

end EndSource

section Symmetric

variable {S : Type uV} [Category.{vV} S] [MonoidalCategory S]
  [SymmetricCategory S] [MonoidalClosed S]
  {C : Type uA} [EnrichedCategory S C] {Fₛ Gₛ : EnrichedFunctor S C S}

set_option backward.isDefEq.respectTransparency false in
/-- The original full positive Of Reverse app symmetric identity. -/
theorem positiveOfReverse_app_symmetric {K : S}
    (t : GradedNatTrans (@Center.ofBraidedObj _ _ _ (reverseBraiding _) K) Fₛ Gₛ) (a : C) :
    (positiveOfReverse t).app a = t.app a := by
  rw [positiveOfReverse_app,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding (Fₛ.obj a) K]
  simp only [Iso.inv_hom_id_assoc]
  exact MonoidalClosed.curry_uncurry (t.app a)

set_option backward.isDefEq.respectTransparency false in
/-- The original full reverse Of Positive app symmetric identity. -/
theorem reverseOfPositive_app_symmetric {K : S}
    (t : GradedNatTrans ((Center.ofBraided S).obj K) Fₛ Gₛ) (a : C) :
    (reverseOfPositive t).app a = t.app a := by
  rw [reverseOfPositive_app, SymmetricCategory.braiding_swap_eq_inv_braiding K (Fₛ.obj a)]
  simp only [Iso.inv_hom_id_assoc]
  exact MonoidalClosed.curry_uncurry (t.app a)

variable (Wₛ Xₛ : EnrichedFunctor S C S)
  [HasProduct (Enriched.weightedEnd.objects Wₛ Xₛ)]
  [HasProduct (Enriched.weightedEnd.relations Wₛ Xₛ)]
  [HasEqualizer (Enriched.weightedEnd.leftMap Wₛ Xₛ) (Enriched.weightedEnd.rightMap Wₛ Xₛ)]

/-- The original full positive End Projections app symmetric identity. -/
theorem positiveEndProjections_app_symmetric (a : C) :
    (positiveEndProjections Wₛ Xₛ).app a = Enriched.weightedEnd.π Wₛ Xₛ a := by
  change (positiveOfReverse (reverseEndProjections Wₛ Xₛ)).app a = _
  rw [positiveOfReverse_app_symmetric, reverseEndProjections_app]

/-- The original full end To Positive app symmetric identity. -/
theorem endToPositive_app_symmetric {K : S} (f : K ⟶ Enriched.weightedEnd Wₛ Xₛ) (a : C) :
    (endToPositive Wₛ Xₛ f).app a = f ≫ Enriched.weightedEnd.π Wₛ Xₛ a := by
  change (positiveOfReverse _).app a = _
  rw [positiveOfReverse_app_symmetric, GradedNatTrans.regrade_app,
    reverseEndProjections_app]
  rfl

/-- The original full end From Positive symmetric π identity. -/
theorem endFromPositive_symmetric_π {K : S}
    (t : GradedNatTrans ((Center.ofBraided S).obj K) Wₛ Xₛ) (a : C) :
    endFromPositive Wₛ Xₛ t ≫ Enriched.weightedEnd.π Wₛ Xₛ a = t.app a := by
  rw [endFromPositive_π, reverseOfPositive_app_symmetric]

end Symmetric



section RepresentedInputs

variable (X Y Z : EnrichedFunctorCat V A)

section Source

variable
  [HasProduct (Enriched.weightedEnd.objects Y.toEnrichedFunctor Z.toEnrichedFunctor)]
  [HasProduct (Enriched.weightedEnd.relations Y.toEnrichedFunctor Z.toEnrichedFunctor)]
  [HasEqualizer (Enriched.weightedEnd.leftMap Y.toEnrichedFunctor Z.toEnrichedFunctor)
    (Enriched.weightedEnd.rightMap Y.toEnrichedFunctor Z.toEnrichedFunctor)]
  [HasProduct (Enriched.weightedEnd.objects X.toEnrichedFunctor Z.toEnrichedFunctor)]
  [HasProduct (Enriched.weightedEnd.relations X.toEnrichedFunctor Z.toEnrichedFunctor)]
  [HasEqualizer (Enriched.weightedEnd.leftMap X.toEnrichedFunctor Z.toEnrichedFunctor)
    (Enriched.weightedEnd.rightMap X.toEnrichedFunctor Z.toEnrichedFunctor)]

/-- The original represented presheaf isomorphism is natural in the entire source diagram map. -/
theorem endNatTransYonedaIso_pre (g : X ⟶ Y) :
    Functor.whiskerRight
        (yoneda.map (Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor Z.toEnrichedFunctor
          X.toEnrichedFunctor g))
        uliftFunctor.{max uA vV, vV} ≫
      (endNatTransYonedaIso X.toEnrichedFunctor Z.toEnrichedFunctor).hom =
    (endNatTransYonedaIso Y.toEnrichedFunctor Z.toEnrichedFunctor).hom ≫
      Functor.whiskerRight
        ((centralGradedYonedaOfBraidedIso Y.toEnrichedFunctor Z.toEnrichedFunctor).inv ≫
          Functor.whiskerLeft (Center.ofBraided V).op
            (EnrichedFunctorCat.centralGradedYonedaPrecomp (G := Z) g) ≫
          (centralGradedYonedaOfBraidedIso X.toEnrichedFunctor Z.toEnrichedFunctor).hom)
        uliftFunctor.{max uA vV, max uA vV} := by
  apply NatTrans.ext
  funext K
  apply ConcreteCategory.hom_ext
  intro h
  change ULift.up (endToPositive X.toEnrichedFunctor Z.toEnrichedFunctor
      (h.down ≫ Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor Z.toEnrichedFunctor
          X.toEnrichedFunctor g)) =
    ULift.up (EnrichedFunctorCat.gradedPrecomp ((Center.ofBraided V).obj K.unop) g
      (endToPositive Y.toEnrichedFunctor Z.toEnrichedFunctor h.down))
  exact congrArg ULift.up
    (endToPositive_mapWeight X.toEnrichedFunctor Y.toEnrichedFunctor Z.toEnrichedFunctor
      h.down g)

/-- The inverse original representation retains the complete contravariant source square. -/
theorem endNatTransYonedaIso_pre_inv (g : X ⟶ Y) :
    Functor.whiskerRight
        ((centralGradedYonedaOfBraidedIso Y.toEnrichedFunctor Z.toEnrichedFunctor).inv ≫
          Functor.whiskerLeft (Center.ofBraided V).op
            (EnrichedFunctorCat.centralGradedYonedaPrecomp (G := Z) g) ≫
          (centralGradedYonedaOfBraidedIso X.toEnrichedFunctor Z.toEnrichedFunctor).hom)
        uliftFunctor.{max uA vV, max uA vV} ≫
      (endNatTransYonedaIso X.toEnrichedFunctor Z.toEnrichedFunctor).inv =
    (endNatTransYonedaIso Y.toEnrichedFunctor Z.toEnrichedFunctor).inv ≫
      Functor.whiskerRight
        (yoneda.map (Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor Z.toEnrichedFunctor
          X.toEnrichedFunctor g))
        uliftFunctor.{max uA vV, vV} := by
  apply (cancel_epi (endNatTransYonedaIso Y.toEnrichedFunctor Z.toEnrichedFunctor).hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun t => t ≫
      (endNatTransYonedaIso X.toEnrichedFunctor Z.toEnrichedFunctor).inv)
      (endNatTransYonedaIso_pre X Y Z g).symm

end Source

section Target

variable
  [HasProduct (Enriched.weightedEnd.objects X.toEnrichedFunctor Y.toEnrichedFunctor)]
  [HasProduct (Enriched.weightedEnd.relations X.toEnrichedFunctor Y.toEnrichedFunctor)]
  [HasEqualizer (Enriched.weightedEnd.leftMap X.toEnrichedFunctor Y.toEnrichedFunctor)
    (Enriched.weightedEnd.rightMap X.toEnrichedFunctor Y.toEnrichedFunctor)]
  [HasProduct (Enriched.weightedEnd.objects X.toEnrichedFunctor Z.toEnrichedFunctor)]
  [HasProduct (Enriched.weightedEnd.relations X.toEnrichedFunctor Z.toEnrichedFunctor)]
  [HasEqualizer (Enriched.weightedEnd.leftMap X.toEnrichedFunctor Z.toEnrichedFunctor)
    (Enriched.weightedEnd.rightMap X.toEnrichedFunctor Z.toEnrichedFunctor)]

/-- The original represented presheaf isomorphism is natural in the entire target diagram map. -/
theorem endNatTransYonedaIso_post (g : Y ⟶ Z) :
    Functor.whiskerRight
        (yoneda.map (Enriched.weightedEnd.mapDiagram X.toEnrichedFunctor Y.toEnrichedFunctor
          Z.toEnrichedFunctor g))
        uliftFunctor.{max uA vV, vV} ≫
      (endNatTransYonedaIso X.toEnrichedFunctor Z.toEnrichedFunctor).hom =
    (endNatTransYonedaIso X.toEnrichedFunctor Y.toEnrichedFunctor).hom ≫
      Functor.whiskerRight
        ((centralGradedYonedaOfBraidedIso X.toEnrichedFunctor Y.toEnrichedFunctor).inv ≫
          Functor.whiskerLeft (Center.ofBraided V).op
            (EnrichedFunctorCat.centralGradedYonedaPostcomp (F := X) g) ≫
          (centralGradedYonedaOfBraidedIso X.toEnrichedFunctor Z.toEnrichedFunctor).hom)
        uliftFunctor.{max uA vV, max uA vV} := by
  apply NatTrans.ext
  funext K
  apply ConcreteCategory.hom_ext
  intro h
  change ULift.up (endToPositive X.toEnrichedFunctor Z.toEnrichedFunctor
      (h.down ≫ Enriched.weightedEnd.mapDiagram X.toEnrichedFunctor Y.toEnrichedFunctor
          Z.toEnrichedFunctor g)) =
    ULift.up (EnrichedFunctorCat.gradedPostcomp ((Center.ofBraided V).obj K.unop)
      (endToPositive X.toEnrichedFunctor Y.toEnrichedFunctor h.down) g)
  exact congrArg ULift.up
    (endToPositive_mapDiagram X.toEnrichedFunctor Y.toEnrichedFunctor Z.toEnrichedFunctor
      h.down g)

/-- The inverse original representation retains the complete covariant target square. -/
theorem endNatTransYonedaIso_post_inv (g : Y ⟶ Z) :
    Functor.whiskerRight
        ((centralGradedYonedaOfBraidedIso X.toEnrichedFunctor Y.toEnrichedFunctor).inv ≫
          Functor.whiskerLeft (Center.ofBraided V).op
            (EnrichedFunctorCat.centralGradedYonedaPostcomp (F := X) g) ≫
          (centralGradedYonedaOfBraidedIso X.toEnrichedFunctor Z.toEnrichedFunctor).hom)
        uliftFunctor.{max uA vV, max uA vV} ≫
      (endNatTransYonedaIso X.toEnrichedFunctor Z.toEnrichedFunctor).inv =
    (endNatTransYonedaIso X.toEnrichedFunctor Y.toEnrichedFunctor).inv ≫
      Functor.whiskerRight
        (yoneda.map (Enriched.weightedEnd.mapDiagram X.toEnrichedFunctor Y.toEnrichedFunctor
          Z.toEnrichedFunctor g))
        uliftFunctor.{max uA vV, vV} := by
  apply (cancel_epi (endNatTransYonedaIso X.toEnrichedFunctor Y.toEnrichedFunctor).hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun t => t ≫
      (endNatTransYonedaIso X.toEnrichedFunctor Z.toEnrichedFunctor).inv)
      (endNatTransYonedaIso_post X Y Z g).symm

end Target

end RepresentedInputs

end CategoryTheory.GradingConvention
