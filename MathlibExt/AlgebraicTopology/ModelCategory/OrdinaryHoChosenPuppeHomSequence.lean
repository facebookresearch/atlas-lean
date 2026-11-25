/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeRotation
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoPuppeCofiberNull

/-!
# Contravariant Hom exactness of the actual chosen Puppe tower

Third exactness is derived from the weak next-cofiber comparison and the
constructed suspension reversal. The unbounded tower is obtained by
iterating the original target inclusion and chosen cofiber construction.
Every term, restriction, source Arrow action, target action, and signed
three-step suspension comparison is its original whole map.

The hypotheses on the chosen cone are cofibrancy of its insertions and
weakness of its actual zero contractions at cofibrant objects. Exactness
and shift comparisons are conclusions. Integer-indexed Omega-target
identifications and comparison with an original chosen fiber are separate
construction obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OrdinaryHoChosenPuppe OrdinaryHoChosenPuppeRotation

namespace HomotopicalAlgebra.OrdinaryHoChosenPuppeHomSequence

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  (Z : C) (hZ : IsZero Z)
  (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

/-- The third actual Puppe image is the original boundary-restriction kernel.
The image uses the unchanged unsigned suspension map; reversal is eliminated
through its constructed whole Iso. -/
theorem third_exact (F : Arrow C) [IsCofibrant F.right]
    [Cofibration (ι.app F.left)] [Cofibration (ι.app F.right)]
    (E : C) [IsFibrant E]
    (hCone : weakEquivalences C (toZero Z hZ (cone.obj F.right)))
    (g : ((weakEquivalences C).Q).obj (suspensionCone cone ι c Z hZ F.left).pt ⟶
      ((weakEquivalences C).Q).obj E) :
    (∃ h : ((weakEquivalences C).Q).obj (suspensionCone cone ι c Z hZ F.right).pt ⟶
        ((weakEquivalences C).Q).obj E,
      ((weakEquivalences C).Q).map (suspensionMap cone ι c hc Z hZ F.hom) ≫ h = g) ↔
      ((weakEquivalences C).Q).map (boundary cone ι c hc Z hZ F) ≫ g =
        OrdinaryHoCofiberKernel.nullHom (c F).pt E := by
  constructor
  · rintro ⟨h, rfl⟩
    exact boundary_suspension_post_null Z hZ cone ι c hc F E hCone h
  · intro hg
    let _ : Cofibration (c F).inr := cofiberTarget_cofibration cone ι c hc F
    let _ : IsCofibrant (c F).pt := isCofibrant_of_cofibration (c F).inr
    let _ : IsCofibrant (targetArrow cone ι c F).left := inferInstanceAs (IsCofibrant F.right)
    let _ : IsCofibrant (targetArrow cone ι c F).right := inferInstanceAs (IsCofibrant (c F).pt)
    let _ : Cofibration (ι.app (targetArrow cone ι c F).left) :=
      inferInstanceAs (Cofibration (ι.app F.right))
    let _ : IsIso (((weakEquivalences C).Q).map (rotationComparison cone ι c hc Z hZ F)) :=
      Localization.inverts ((weakEquivalences C).Q) (weakEquivalences C)
        (rotationComparison cone ι c hc Z hZ F)
        (rotationComparison_weak cone ι c hc Z hZ F hCone)
    have hKernel :
        ((weakEquivalences C).Q).map (nextCofiberCone cone ι c F).inr ≫
            (((weakEquivalences C).Q).map (rotationComparison cone ι c hc Z hZ F) ≫ g) =
          OrdinaryHoCofiberKernel.nullHom (c F).pt E := by
      rw [← Category.assoc, ← Functor.map_comp, rotationComparison_cofiber]
      exact hg
    obtain ⟨h, hh⟩ :=
      (second_exact Z hZ cone ι c hc (targetArrow cone ι c F) E
        (((weakEquivalences C).Q).map (rotationComparison cone ι c hc Z hZ F) ≫ g)).mpr
        hKernel
    refine ⟨(suspensionReversal cone ι c hc Z hZ F.right hCone).hom ≫ h, ?_⟩
    apply (cancel_epi
      (((weakEquivalences C).Q).map (rotationComparison cone ι c hc Z hZ F))).mp
    simpa only [Category.assoc] using
      (congrArg (fun t => t ≫ h) (rotationComparison_boundary cone ι c hc Z hZ F hCone)).trans hh

/-- Every finite iterate is the same actual target-inclusion functor.
The index is unbounded. -/
def stageFunctor : ℕ → Arrow C ⥤ Arrow C
  | 0 => 𝟭 (Arrow C)
  | n + 1 => stageFunctor n ⋙ targetArrowFunctor cone ι c hc

/-- Retain the full original Arrow at every stage of the actual Puppe tower. -/
abbrev stageArrow (n : ℕ) (F : Arrow C) := (stageFunctor cone ι c hc n).obj F

/-- The original carrier at every stage, before applying any Hom functor. -/
def term (n : ℕ) (F : Arrow C) : C := (stageArrow cone ι c hc n F).left

/-- The entire original map between consecutive actual carriers. -/
def termArrow (n : ℕ) (F : Arrow C) : term cone ι c hc n F ⟶ term cone ι c hc (n + 1) F :=
  (stageArrow cone ι c hc n F).hom

/-- Every original Arrow square acts on the whole carrier at every stage. -/
def termMap (n : ℕ) {F G : Arrow C} (q : F ⟶ G) :
    term cone ι c hc n F ⟶ term cone ι c hc n G :=
  ((stageFunctor cone ι c hc n).map q).left

omit Z hZ [ModelCategory C] [HasZeroObject C] in
/-- The first tower arrow is the unchanged original input arrow. -/
theorem termArrow_zero (F : Arrow C) : termArrow cone ι c hc 0 F = F.hom := rfl

omit Z hZ [ModelCategory C] [HasZeroObject C] in
/-- Every successor arrow is the original target leg of the selected stage cofiber. -/
theorem termArrow_succ (n : ℕ) (F : Arrow C) :
    termArrow cone ι c hc (n + 1) F = (c (stageArrow cone ι c hc n F)).inr := rfl

omit Z hZ [ModelCategory C] [HasZeroObject C] in
/-- All consecutive stage maps commute on both components of each original Arrow square. -/
theorem termArrow_naturality (n : ℕ) {F G : Arrow C} (q : F ⟶ G) :
    termMap cone ι c hc n q ≫ termArrow cone ι c hc n G =
      termArrow cone ι c hc n F ≫ termMap cone ι c hc (n + 1) q :=
  ((stageFunctor cone ι c hc n).map q).w

omit Z hZ [ModelCategory C] [HasZeroObject C] in
/-- The source action preserves every original identity at every stage. -/
theorem termMap_id (n : ℕ) (F : Arrow C) :
    termMap cone ι c hc n (𝟙 F) = 𝟙 (term cone ι c hc n F) := by
  unfold termMap
  rw [(stageFunctor cone ι c hc n).map_id]
  rfl

omit Z hZ [ModelCategory C] [HasZeroObject C] in
/-- The full source action preserves every original Arrow composition at every stage. -/
theorem termMap_comp (n : ℕ) {F G H : Arrow C} (q : F ⟶ G) (r : G ⟶ H) :
    termMap cone ι c hc n (q ≫ r) = termMap cone ι c hc n q ≫ termMap cone ι c hc n r := by
  unfold termMap
  rw [(stageFunctor cone ι c hc n).map_comp]
  rfl

/-- Ordinary-Ho tests of the original carrier at every stage. -/
abbrev homTerm (n : ℕ) (F : Arrow C) (E : C) :=
  ((weakEquivalences C).Q).obj (term cone ι c hc n F) ⟶ ((weakEquivalences C).Q).obj E

/-- The whole contravariant restriction uses the original consecutive stage arrow. -/
def restriction (n : ℕ) (F : Arrow C) (E : C) :
    homTerm cone ι c hc (n + 1) F E → homTerm cone ι c hc n F E :=
  OrdinaryHoPuppeCofiberNull.precomposition (termArrow cone ι c hc n F) E

/-- The full original Arrow induces the contravariant action on every Hom term. -/
def sourceAction (n : ℕ) {F G : Arrow C} (q : F ⟶ G) (E : C) :
    homTerm cone ι c hc n G E → homTerm cone ι c hc n F E :=
  OrdinaryHoPuppeCofiberNull.precomposition (termMap cone ι c hc n q) E

/-- Each whole target map acts covariantly at every stage. -/
def targetAction (n : ℕ) (F : Arrow C) {E E' : C} (p : E ⟶ E') :
    homTerm cone ι c hc n F E → homTerm cone ι c hc n F E' :=
  fun g => g ≫ ((weakEquivalences C).Q).map p

omit [HasZeroObject C] in
/-- The entire source identity acts as the identity on every Hom term. -/
theorem sourceAction_id (n : ℕ) (F : Arrow C) (E : C) :
    sourceAction cone ι c hc n (𝟙 F) E = id := by
  unfold sourceAction
  rw [termMap_id, OrdinaryHoPuppeCofiberNull.precomposition_id]

omit [HasZeroObject C] in
/-- All original source Arrow actions compose contravariantly on the whole Hom terms. -/
theorem sourceAction_comp (n : ℕ) {F G H : Arrow C} (q : F ⟶ G) (r : G ⟶ H) (E : C) :
    sourceAction cone ι c hc n (q ≫ r) E =
      sourceAction cone ι c hc n q E ∘ sourceAction cone ι c hc n r E := by
  unfold sourceAction
  rw [termMap_comp, OrdinaryHoPuppeCofiberNull.precomposition_comp]

omit [HasZeroObject C] in
/-- Every full target identity acts as the identity on all Hom terms. -/
theorem targetAction_id (n : ℕ) (F : Arrow C) (E : C) :
    targetAction cone ι c hc n F (𝟙 E) = id := by
  funext g
  change g ≫ ((weakEquivalences C).Q).map (𝟙 E) = g
  rw [((weakEquivalences C).Q).map_id, Category.comp_id]

omit [HasZeroObject C] in
/-- All whole target actions compose covariantly at every stage. -/
theorem targetAction_comp (n : ℕ) (F : Arrow C) {E E' E'' : C}
    (p : E ⟶ E') (r : E' ⟶ E'') :
    targetAction cone ι c hc n F (p ≫ r) =
      targetAction cone ι c hc n F r ∘ targetAction cone ι c hc n F p := by
  funext g
  change g ≫ ((weakEquivalences C).Q).map (p ≫ r) =
    (g ≫ ((weakEquivalences C).Q).map p) ≫ ((weakEquivalences C).Q).map r
  rw [Functor.map_comp, Category.assoc]

omit [HasZeroObject C] in
/-- Every entire source Arrow square commutes with every consecutive Hom restriction. -/
theorem restriction_source (n : ℕ) {F G : Arrow C} (q : F ⟶ G) (E : C) :
    restriction cone ι c hc n F E ∘ sourceAction cone ι c hc (n + 1) q E =
      sourceAction cone ι c hc n q E ∘ restriction cone ι c hc n G E := by
  funext g
  change ((weakEquivalences C).Q).map (termArrow cone ι c hc n F) ≫
      (((weakEquivalences C).Q).map (termMap cone ι c hc (n + 1) q) ≫ g) =
    ((weakEquivalences C).Q).map (termMap cone ι c hc n q) ≫
      (((weakEquivalences C).Q).map (termArrow cone ι c hc n G) ≫ g)
  rw [← Category.assoc, ← Functor.map_comp, ← termArrow_naturality,
    Functor.map_comp, Category.assoc]

omit [HasZeroObject C] in
/-- Every whole target map commutes with all consecutive restrictions. -/
theorem restriction_target (n : ℕ) (F : Arrow C) {E E' : C} (p : E ⟶ E') :
    restriction cone ι c hc n F E' ∘ targetAction cone ι c hc (n + 1) F p =
      targetAction cone ι c hc n F p ∘ restriction cone ι c hc n F E := by
  funext g
  exact (Category.assoc _ _ _).symm

/-- Each actual restriction retains the literal original null class. -/
theorem restriction_null (n : ℕ) (F : Arrow C) (E : C) :
    restriction cone ι c hc n F E
        (OrdinaryHoCofiberKernel.nullHom (term cone ι c hc (n + 1) F) E) =
      OrdinaryHoCofiberKernel.nullHom (term cone ι c hc n F) E :=
  OrdinaryHoPuppeCofiberNull.precomposition_null (termArrow cone ι c hc n F) E

omit [HasZeroObject C] in
/-- Both source and target actions commute on every entire Hom class. -/
theorem sourceAction_target (n : ℕ) {F G : Arrow C} (q : F ⟶ G) {E E' : C}
    (p : E ⟶ E') :
    sourceAction cone ι c hc n q E' ∘ targetAction cone ι c hc n G p =
      targetAction cone ι c hc n F p ∘ sourceAction cone ι c hc n q E := by
  funext g
  exact (Category.assoc _ _ _).symm

variable
  (hι : ∀ X : C, IsCofibrant X → cofibrations C (ι.app X))
  (hCone : ∀ X : C, IsCofibrant X → weakEquivalences C (toZero Z hZ (cone.obj X)))

omit Z hZ hCone [HasZeroObject C] in
include hι in
/-- Cofibrancy of both original endpoints propagates through the entire chosen tower. -/
theorem stageArrow_cofibrant (n : ℕ) (F : Arrow C)
    [IsCofibrant F.left] [IsCofibrant F.right] :
    IsCofibrant (stageArrow cone ι c hc n F).left ∧
      IsCofibrant (stageArrow cone ι c hc n F).right := by
  induction n with
  | zero =>
    change IsCofibrant F.left ∧ IsCofibrant F.right
    exact ⟨inferInstance, inferInstance⟩
  | succ n hn =>
    let _ : IsCofibrant (stageArrow cone ι c hc n F).left := hn.1
    let _ : IsCofibrant (stageArrow cone ι c hc n F).right := hn.2
    let _ : Cofibration (ι.app (stageArrow cone ι c hc n F).left) :=
      (cofibration_iff _).mpr (hι _ hn.1)
    let _ : Cofibration (c (stageArrow cone ι c hc n F)).inr :=
      cofiberTarget_cofibration cone ι c hc (stageArrow cone ι c hc n F)
    exact ⟨hn.2, isCofibrant_of_cofibration (c (stageArrow cone ι c hc n F)).inr⟩

include hι hCone in
/-- Image equals the actual null kernel at every stage of the unbounded contravariant tower. -/
theorem exact_at (n : ℕ) (F : Arrow C) [IsCofibrant F.left] [IsCofibrant F.right]
    (E : C) [IsFibrant E] (g : homTerm cone ι c hc (n + 1) F E) :
    (∃ h : homTerm cone ι c hc (n + 2) F E,
      restriction cone ι c hc (n + 1) F E h = g) ↔
      restriction cone ι c hc n F E g =
        OrdinaryHoCofiberKernel.nullHom (term cone ι c hc n F) E := by
  have hn := stageArrow_cofibrant cone ι c hc hι n F
  let _ : IsCofibrant (stageArrow cone ι c hc n F).left := hn.1
  let _ : IsCofibrant (stageArrow cone ι c hc n F).right := hn.2
  let _ : Cofibration (ι.app (stageArrow cone ι c hc n F).left) :=
    (cofibration_iff _).mpr (hι _ hn.1)
  exact first_exact Z hZ cone ι c hc (stageArrow cone ι c hc n F) E (hCone _ hn.1) g

/-- The actual three-step shift comparison retains the original chosen suspension carrier. -/
def shiftComparison (n : ℕ) (F : Arrow C) :
    term cone ι c hc (n + 3) F ⟶
      (suspensionCone cone ι c Z hZ (term cone ι c hc n F)).pt :=
  rotationComparison cone ι c hc Z hZ (stageArrow cone ι c hc n F)

omit [HasZeroObject C] in
include hι hCone in
/-- Every actual shift comparison is weak by its constructed next-cofiber pushout. -/
theorem shiftComparison_weak (n : ℕ) (F : Arrow C)
    [IsCofibrant F.left] [IsCofibrant F.right] :
    weakEquivalences C (shiftComparison Z hZ cone ι c hc n F) := by
  have hn := stageArrow_cofibrant cone ι c hc hι n F
  let _ : IsCofibrant (stageArrow cone ι c hc n F).right := hn.2
  let _ : Cofibration (ι.app (stageArrow cone ι c hc n F).left) :=
    (cofibration_iff _).mpr (hι _ hn.1)
  let _ : Cofibration (ι.app (stageArrow cone ι c hc n F).right) :=
    (cofibration_iff _).mpr (hι _ hn.2)
  exact rotationComparison_weak cone ι c hc Z hZ (stageArrow cone ι c hc n F)
    (hCone _ hn.2)

omit [ModelCategory C] [HasZeroObject C] in
/-- All original Arrow maps commute with every three-step shift comparison. -/
theorem shiftComparison_naturality (n : ℕ) {F G : Arrow C} (q : F ⟶ G) :
    termMap cone ι c hc (n + 3) q ≫ shiftComparison Z hZ cone ι c hc n G =
      shiftComparison Z hZ cone ι c hc n F ≫
        suspensionMap cone ι c hc Z hZ (termMap cone ι c hc n q) :=
  rotationComparison_naturality cone ι c hc Z hZ ((stageFunctor cone ι c hc n).map q)

/-- Reversal on every actual tower term is obtained from its two original double-cone collapses. -/
def termReversal (n : ℕ) (F : Arrow C) [IsCofibrant F.left] [IsCofibrant F.right] :
    ((weakEquivalences C).Q).obj (suspensionCone cone ι c Z hZ (term cone ι c hc n F)).pt ≅
      ((weakEquivalences C).Q).obj (suspensionCone cone ι c Z hZ (term cone ι c hc n F)).pt := by
  have hn := stageArrow_cofibrant cone ι c hc hι n F
  let _ : IsCofibrant (term cone ι c hc n F) := hn.1
  let _ : Cofibration (ι.app (term cone ι c hc n F)) := (cofibration_iff _).mpr (hι _ hn.1)
  exact suspensionReversal cone ι c hc Z hZ (term cone ι c hc n F) (hCone _ hn.1)

omit [HasZeroObject C] in
/-- The full shift square preserves the actual suspension reversal at every stage. -/
theorem signed_shift_square (n : ℕ) (F : Arrow C)
    [IsCofibrant F.left] [IsCofibrant F.right] :
    ((weakEquivalences C).Q).map (termArrow cone ι c hc (n + 3) F) ≫
        ((weakEquivalences C).Q).map (shiftComparison Z hZ cone ι c hc (n + 1) F) =
      ((weakEquivalences C).Q).map (shiftComparison Z hZ cone ι c hc n F) ≫
        ((weakEquivalences C).Q).map
          (suspensionMap cone ι c hc Z hZ (termArrow cone ι c hc n F)) ≫
        (termReversal Z hZ cone ι c hc hι hCone (n + 1) F).hom := by
  have hn := stageArrow_cofibrant cone ι c hc hι n F
  let _ : IsCofibrant (stageArrow cone ι c hc n F).right := hn.2
  let _ : Cofibration (ι.app (stageArrow cone ι c hc n F).right) :=
    (cofibration_iff _).mpr (hι _ hn.2)
  rw [← Functor.map_comp]
  change ((weakEquivalences C).Q).map
      ((nextCofiberCone cone ι c (targetArrow cone ι c (stageArrow cone ι c hc n F))).inr ≫
        rotationComparison cone ι c hc Z hZ (targetArrow cone ι c (stageArrow cone ι c hc n F))) = _
  rw [rotationComparison_cofiber]
  exact (rotationComparison_boundary cone ι c hc Z hZ (stageArrow cone ι c hc n F)
    (hCone _ hn.2)).symm

end HomotopicalAlgebra.OrdinaryHoChosenPuppeHomSequence
