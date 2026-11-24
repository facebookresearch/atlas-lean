/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.LeftKanExtension
public import MathlibExt.CategoryTheory.Enriched.GradedRestriction
public import MathlibExt.CategoryTheory.Enriched.GradedCompositionActions
public import MathlibExt.CategoryTheory.Enriched.GradedComponentActions

/-!
# The actual left Kan action in every central grade

The graded action is the proved Lan inverse applied to the original target
unit. Full graded source and target actions and source-first tensor composition
use the supplied center grades and original enriched restriction.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uB uV vV
open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- Forward graded correspondence is actual source composition with the unit
after actual restriction. -/
theorem leftKanGradedHomEquiv_eta_restrict
    (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) :
    leftKanGradedHomEquiv j Γ X Y t =
      gradedPrecomp Γ (leftKanUnit j X) (GradedNatTrans.restrict j t) := by
  apply GradedNatTrans.ext
  funext a
  have h := gradedPrecomp_app Γ (leftKanUnit j X) (GradedNatTrans.restrict j t) a
  have hc := GradedNatTrans.restrict_app j t a
  have hu := leftKanUnit_component j X a
  have h' : (gradedPrecomp Γ (leftKanUnit j X) (GradedNatTrans.restrict j t)).app a =
      t.app (j.obj a) ≫ (MonoidalClosed.pre (leftKanUnitComponent j X a)).app
        (Y.toEnrichedFunctor.obj (j.obj a)) :=
    h.trans (congrArg₂ (fun p q => p ≫ q) hc
      (congrArg (fun p => (MonoidalClosed.pre p).app (Y.toEnrichedFunctor.obj (j.obj a))) hu))
  exact (leftKanGradedHomEquiv_app j Γ X Y t a).trans h'.symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- Left Kan extension acts on the original transformation in its complete central grade. -/
@[no_expose]
def leftKanGradedMap (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor (leftKanObject j X').toEnrichedFunctor :=
  (leftKanGradedHomEquiv j Γ X (leftKanObject j X')).symm
    (gradedPostcomp Γ t (leftKanUnit j X'))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanGradedMap_apply_private
    (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    leftKanGradedMap j Γ t =
      (leftKanGradedHomEquiv j Γ X (leftKanObject j X')).symm
        (gradedPostcomp Γ t (leftKanUnit j X')) := rfl

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
theorem leftKanGradedMap_apply
    (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    leftKanGradedMap j Γ t =
      (leftKanGradedHomEquiv j Γ X (leftKanObject j X')).symm
        (gradedPostcomp Γ t (leftKanUnit j X')) :=
  leftKanGradedMap_apply_private j Γ t

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The actual graded map is characterized by the original target unit. -/
theorem leftKanGradedMap_homEquiv
    (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    leftKanGradedHomEquiv j Γ X (leftKanObject j X') (leftKanGradedMap j Γ t) =
      gradedPostcomp Γ t (leftKanUnit j X') := by
  rw [leftKanGradedMap_apply, Equiv.apply_symm_apply]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- Unit naturality holds for every complete central-graded source transformation. -/
theorem leftKanGradedMap_eta
    (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    gradedPrecomp Γ (leftKanUnit j X) (GradedNatTrans.restrict j (leftKanGradedMap j Γ t)) =
      gradedPostcomp Γ t (leftKanUnit j X') :=
  (leftKanGradedHomEquiv_eta_restrict j Γ X (leftKanObject j X')
    (leftKanGradedMap j Γ t)).symm.trans
    (leftKanGradedMap_homEquiv j Γ t)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- Source-first full tensor composition of arbitrary grades is preserved by actual Lan. -/
theorem leftKanGradedMap_tensorComp
    {Γ Δ : Center V} {X X' X'' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor)
    (u : GradedNatTrans Δ X'.toEnrichedFunctor X''.toEnrichedFunctor) :
    leftKanGradedMap j (Γ ⊗ Δ) (GradedNatTrans.tensorComp t u) =
      GradedNatTrans.tensorComp (leftKanGradedMap j Γ t) (leftKanGradedMap j Δ u) := by
  apply (leftKanGradedHomEquiv j (Γ ⊗ Δ) X (leftKanObject j X'')).injective
  have h1 := leftKanGradedMap_homEquiv j (Γ ⊗ Δ) (GradedNatTrans.tensorComp t u)
  have h2 := tensorComp_gradedPostcomp t u (leftKanUnit j X'')
  have h3 := congrArg (fun q => GradedNatTrans.tensorComp t q) (leftKanGradedMap_eta j Δ u).symm
  have h4 := (tensorComp_gradedMiddle t (leftKanUnit j X')
    (GradedNatTrans.restrict j (leftKanGradedMap j Δ u))).symm
  have h5 := congrArg (fun q => GradedNatTrans.tensorComp q
    (GradedNatTrans.restrict j (leftKanGradedMap j Δ u))) (leftKanGradedMap_eta j Γ t).symm
  have h6 := (tensorComp_gradedPrecomp (leftKanUnit j X)
    (GradedNatTrans.restrict j (leftKanGradedMap j Γ t))
    (GradedNatTrans.restrict j (leftKanGradedMap j Δ u))).symm
  have h7 := congrArg (fun q => gradedPrecomp (Γ ⊗ Δ) (leftKanUnit j X) q)
    (GradedNatTrans.restrict_tensorComp j (leftKanGradedMap j Γ t) (leftKanGradedMap j Δ u)).symm
  have h8 := (leftKanGradedHomEquiv_eta_restrict j (Γ ⊗ Δ) X (leftKanObject j X'')
    (GradedNatTrans.tensorComp (leftKanGradedMap j Γ t) (leftKanGradedMap j Δ u))).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8))))))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- Every genuine central scalar map is preserved by actual graded Lan. -/
theorem leftKanGradedMap_regrade
    {Γ Δ : Center V} (h : Γ ⟶ Δ) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Δ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    leftKanGradedMap j Γ (GradedNatTrans.regrade h t) =
      GradedNatTrans.regrade h (leftKanGradedMap j Δ t) := by
  rw [leftKanGradedMap_apply, leftKanGradedMap_apply,
    gradedPostcomp_regrade, leftKanGradedHomEquiv_symm_regrade]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The complete source input naturality retains both central grades and actual Lan action. -/
theorem leftKanGradedHomEquiv_tensorComp_left
    {Γ Δ : Center V} {X' X : EnrichedFunctorCat V A} (Y : EnrichedFunctorCat V B)
    (s : GradedNatTrans Δ X'.toEnrichedFunctor X.toEnrichedFunctor)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) :
    leftKanGradedHomEquiv j (Δ ⊗ Γ) X' Y
        (GradedNatTrans.tensorComp (leftKanGradedMap j Δ s) t) =
      GradedNatTrans.tensorComp s (leftKanGradedHomEquiv j Γ X Y t) := by
  have h1 := leftKanGradedHomEquiv_eta_restrict j (Δ ⊗ Γ) X' Y
    (GradedNatTrans.tensorComp (leftKanGradedMap j Δ s) t)
  have h2 := congrArg (fun q => gradedPrecomp (Δ ⊗ Γ) (leftKanUnit j X') q)
    (GradedNatTrans.restrict_tensorComp j (leftKanGradedMap j Δ s) t)
  have h3 := tensorComp_gradedPrecomp (leftKanUnit j X')
    (GradedNatTrans.restrict j (leftKanGradedMap j Δ s)) (GradedNatTrans.restrict j t)
  have h4 := congrArg (fun q => GradedNatTrans.tensorComp q (GradedNatTrans.restrict j t))
    (leftKanGradedMap_eta j Δ s)
  have h5 := tensorComp_gradedMiddle s (leftKanUnit j X) (GradedNatTrans.restrict j t)
  have h6 := congrArg (fun q => GradedNatTrans.tensorComp s q)
    (leftKanGradedHomEquiv_eta_restrict j Γ X Y t).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The complete target input naturality retains both central grades and original restriction. -/
theorem leftKanGradedHomEquiv_tensorComp_right
    {Γ Δ : Center V} (X : EnrichedFunctorCat V A) {Y Y' : EnrichedFunctorCat V B}
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor)
    (u : GradedNatTrans Δ Y.toEnrichedFunctor Y'.toEnrichedFunctor) :
    leftKanGradedHomEquiv j (Γ ⊗ Δ) X Y' (GradedNatTrans.tensorComp t u) =
      GradedNatTrans.tensorComp (leftKanGradedHomEquiv j Γ X Y t)
        (GradedNatTrans.restrict j u) := by
  have h1 := leftKanGradedHomEquiv_eta_restrict j (Γ ⊗ Δ) X Y'
    (GradedNatTrans.tensorComp t u)
  have h2 := congrArg (fun q => gradedPrecomp (Γ ⊗ Δ) (leftKanUnit j X) q)
    (GradedNatTrans.restrict_tensorComp j t u)
  have h3 := tensorComp_gradedPrecomp (leftKanUnit j X)
    (GradedNatTrans.restrict j t) (GradedNatTrans.restrict j u)
  have h4 := congrArg (fun q => GradedNatTrans.tensorComp q (GradedNatTrans.restrict j u))
    (leftKanGradedHomEquiv_eta_restrict j Γ X Y t).symm
  exact h1.trans (h2.trans (h3.trans h4))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
theorem leftKanGradedHomEquiv_tensorComp_left_symm
    {Γ Δ : Center V} {X' X : EnrichedFunctorCat V A} (Y : EnrichedFunctorCat V B)
    (s : GradedNatTrans Δ X'.toEnrichedFunctor X.toEnrichedFunctor)
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor) :
    (leftKanGradedHomEquiv j (Δ ⊗ Γ) X' Y).symm (GradedNatTrans.tensorComp s f) =
      GradedNatTrans.tensorComp (leftKanGradedMap j Δ s)
        ((leftKanGradedHomEquiv j Γ X Y).symm f) := by
  apply (leftKanGradedHomEquiv j (Δ ⊗ Γ) X' Y).injective
  rw [Equiv.apply_symm_apply, leftKanGradedHomEquiv_tensorComp_left, Equiv.apply_symm_apply]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
theorem leftKanGradedHomEquiv_tensorComp_right_symm
    {Γ Δ : Center V} (X : EnrichedFunctorCat V A) {Y Y' : EnrichedFunctorCat V B}
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor)
    (u : GradedNatTrans Δ Y.toEnrichedFunctor Y'.toEnrichedFunctor) :
    (leftKanGradedHomEquiv j (Γ ⊗ Δ) X Y').symm
        (GradedNatTrans.tensorComp f (GradedNatTrans.restrict j u)) =
      GradedNatTrans.tensorComp ((leftKanGradedHomEquiv j Γ X Y).symm f) u := by
  apply (leftKanGradedHomEquiv j (Γ ⊗ Δ) X Y').injective
  rw [Equiv.apply_symm_apply, leftKanGradedHomEquiv_tensorComp_right, Equiv.apply_symm_apply]

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanHomEquiv_id_unit (X : EnrichedFunctorCat V A) :
    leftKanHomEquiv j X (leftKanObject j X) (𝟙 (leftKanObject j X)) = leftKanUnit j X := by
  apply hom_ext
  intro a
  have h1 := congrArg (fun q => component q a)
    (leftKanHomEquiv_apply j X (leftKanObject j X) (𝟙 (leftKanObject j X)))
  have h2 := leftKanHomToRestriction_component j X (leftKanObject j X) (𝟙 (leftKanObject j X)) a
  have h3 := congrArg (fun q => leftKanUnitComponent j X a ≫ q)
    (component_id (leftKanObject j X) (j.obj a))
  exact h1.trans (h2.trans (h3.trans ((Category.comp_id _).trans
    (leftKanUnit_component j X a).symm)))

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The exact canonical unit grade recovers the original ordinary Lan map. -/
theorem leftKanGradedMap_unit {X X' : EnrichedFunctorCat V A} (t : X ⟶ X') :
    leftKanGradedMap j ((Center.ofBraided V).obj (𝟙_ V)) t = (leftKan j).map t := by
  rw [leftKanGradedMap_apply, gradedPostcomp_unit, leftKanGradedHomEquiv_unit_symm_apply]
  apply (leftKanHomEquiv j X (leftKanObject j X')).injective
  rw [Equiv.apply_symm_apply]
  have hn := leftKanHomEquiv_naturality_left j (leftKanObject j X') t (𝟙 (leftKanObject j X'))
  have hc := congrArg (leftKanHomEquiv j X (leftKanObject j X'))
    (Category.comp_id ((leftKan j).map t))
  exact (congrArg (fun q => t ≫ q) (leftKanHomEquiv_id_unit j X')).symm.trans
    (hc.symm.trans hn).symm

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The actual graded Lan action preserves the genuine unit-graded identity. -/
theorem leftKanGradedMap_id (X : EnrichedFunctorCat V A) :
    leftKanGradedMap j ((Center.ofBraided V).obj (𝟙_ V)) (𝟙 X) = 𝟙 (leftKanObject j X) :=
  (leftKanGradedMap_unit j (𝟙 X)).trans ((leftKan j).map_id X)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
private theorem leftKanUnit_targetGenerator {Z : V}
    (X : EnrichedFunctorCat V A) (a : A) (b : B) (q : Z ⟶ X.toEnrichedFunctor.obj a) :
    ((j.obj a ⟶[V] b) ◁ (q ≫ leftKanUnitComponent j X a)) ≫
        (β_ (j.obj a ⟶[V] b) (leftKanCoendObject j X.toEnrichedFunctor (j.obj a))).hom ≫
        MonoidalClosed.uncurry (leftKanCoendMap j X.toEnrichedFunctor (j.obj a) b) =
      ((j.obj a ⟶[V] b) ◁ q) ≫
        Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a := by
  rw [leftKanCoendMap_uncurry]
  simp only [whiskerLeft_comp, Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun p => ((j.obj a ⟶[V] b) ◁ q) ≫ p) (leftKanUnitComponent_action j X a b)

set_option maxHeartbeats 200000 in
-- Retain the original budget for the full enriched Kan and graded tensor calculation.
/-- The original coend generator of the graded Lan action uses the inverse ambient weight braid. -/
theorem leftKanGradedMap_gradeFirstComponent_ι
    (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) (b : B) (a : A) :
    (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) ≫
        GradedNatTrans.gradeFirstComponent Γ (leftKanGradedMap j Γ t) b =
      (α_ Γ.1 (j.obj a ⟶[V] b) (X.toEnrichedFunctor.obj a)).inv ≫
        ((β_ (j.obj a ⟶[V] b) Γ.1).inv ▷ X.toEnrichedFunctor.obj a) ≫
        (α_ (j.obj a ⟶[V] b) Γ.1 (X.toEnrichedFunctor.obj a)).hom ≫
        ((j.obj a ⟶[V] b) ◁ GradedNatTrans.gradeFirstComponent Γ t a) ≫
        Enriched.weightedCoend.ι (leftKanWeight j b) X'.toEnrichedFunctor a := by
  let f := gradedPostcomp Γ t (leftKanUnit j X')
  let W := (j.obj a ⟶[V] b)
  let q := GradedNatTrans.gradeFirstComponent Γ t a
  let L := (leftKanObject j X').toEnrichedFunctor.obj (j.obj a)
  have hq : GradedNatTrans.gradeFirstComponent Γ f a = q ≫ leftKanUnitComponent j X' a :=
    (gradeFirstComponent_gradedPostcomp Γ t (leftKanUnit j X') a).trans
      (congrArg (fun p => q ≫ p) (leftKanUnit_component j X' a))
  have ht : (W ◁ GradedNatTrans.gradeFirstComponent Γ f a) ≫ (β_ W L).hom ≫
      MonoidalClosed.uncurry ((leftKanObject j X').toEnrichedFunctor.map (j.obj a) b) =
        (W ◁ q) ≫ Enriched.weightedCoend.ι (leftKanWeight j b) X'.toEnrichedFunctor a := by
    change (W ◁ GradedNatTrans.gradeFirstComponent Γ f a) ≫ (β_ W L).hom ≫
      MonoidalClosed.uncurry (leftKanCoendMap j X'.toEnrichedFunctor (j.obj a) b) = _
    have h0 := congrArg (fun p => (W ◁ p) ≫ (β_ W L).hom ≫
      MonoidalClosed.uncurry (leftKanCoendMap j X'.toEnrichedFunctor (j.obj a) b)) hq
    have h1 := leftKanUnit_targetGenerator j X' a b q
    exact h0.trans h1
  have h0 := congrArg (fun p =>
    (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) ≫
      GradedNatTrans.gradeFirstComponent Γ p b) (leftKanGradedMap_apply j Γ t)
  have h1 := leftKanGradedHomEquiv_symm_gradeFirstComponent_ι j Γ X (leftKanObject j X') f b a
  exact h0.trans (h1.trans (congrArg (fun p =>
    (α_ Γ.1 W (X.toEnrichedFunctor.obj a)).inv ≫
      ((β_ W Γ.1).inv ▷ X.toEnrichedFunctor.obj a) ≫
      (α_ W Γ.1 (X.toEnrichedFunctor.obj a)).hom ≫ p) ht))

end CategoryTheory.EnrichedFunctorCat
