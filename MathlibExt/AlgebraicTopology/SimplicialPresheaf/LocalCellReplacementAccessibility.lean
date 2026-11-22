/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellReplacement
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.MonomorphismGenerators
import MathlibExt.CategoryTheory.SmallObject.ConstructionComparison
import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentCardinalColimits
import MathlibExt.CategoryTheory.SmallObject.Iteration.Accessible
import MathlibExt.CategoryTheory.SmallObject.TerminalIteration
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Comma

/-!
# Accessibility of the same original local cell replacement

The original selected local-generator system supplies both absolute endpoint
ranks at its stored cardinal. The existing ordered carrier equivalence and
one-step attachment comparison transfer presheaf accessibility to the original
Arrow category. Iteration and terminal restriction use that same cardinal,
bottom, factorization and original replacement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i k ℓ

open CategoryTheory Limits MorphismProperty Opposite Cardinal
open HomotopicalAlgebra
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

private theorem selectedEndpointRanks (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    let d := originalLocalCellData S
    letI := d.regular
    letI := d.orderBot
    ∀ a : (originalLocalGenerators d.T).toSet,
      IsCardinalPresentable a.val.left d.κ ∧
        IsCardinalPresentable a.val.right d.κ := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : OrderBot d.κ.ord.ToType := d.orderBot
  change ∀ a : (originalLocalGenerators d.T).toSet,
    IsCardinalPresentable a.val.left d.κ ∧ IsCardinalPresentable a.val.right d.κ
  rcases d.properties with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hRanks, _, _, _, _, _, _, _, _, _⟩
  rintro ⟨⟨A, B, f⟩, hf⟩
  change originalLocalGenerators d.T f at hf
  rw [← localGeneratorFamily_ofHoms d.T] at hf
  rcases hf with ⟨a⟩
  exact hRanks a

/-- The same original one-step Arrow attachment preserves filtered colimits at
the stored cardinal, including both original source and target maps. -/
theorem originalLocalCellStep_isCardinalAccessible
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    let d := originalLocalCellData S
    letI := d.regular
    letI := d.orderBot
    letI := d.eligible
    letI := SmallObject.hasPushouts (originalLocalGenerators d.T) d.κ
    letI := SmallObject.hasColimitsOfShape_discrete (originalLocalGenerators d.T) d.κ
    (SmallObject.functor (originalLocalGenerators d.T).homFamily).IsCardinalAccessible d.κ := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : OrderBot d.κ.ord.ToType := d.orderBot
  let : (originalLocalGenerators d.T).IsCardinalForSmallObjectArgument d.κ := d.eligible
  let : LocallySmall.{u} (SimplicialPresheaf.{u} D) :=
    SmallObject.locallySmall (originalLocalGenerators d.T) d.κ
  let : HasPushouts (SimplicialPresheaf.{u} D) :=
    SmallObject.hasPushouts (originalLocalGenerators d.T) d.κ
  let := SmallObject.hasColimitsOfShape_discrete (originalLocalGenerators d.T) d.κ
  let J := originalLocalGenerators d.T
  let j := J.homFamily
  let : J.IsSmall.{u} := SmallObject.isSmall J d.κ
  let E := SmallModel.{u} D × SimplexCategory
  let e : SimplicialPresheaf.{u} D ≌ (Eᵒᵖ ⥤ Type u) :=
    normalizedTypePresheafEquivalence D
  let Φ := e.functor
  let jF := fun a : J.toSet => Φ.map (j a)
  have hr := selectedEndpointRanks S
  have hMono : J ≤ monomorphisms (SimplicialPresheaf.{u} D) :=
    d.properties.2.2.2.2.2.2.2.2.2.1
  let : ∀ a : J.toSet, Mono (j a) := fun a => hMono _ a.property
  let : ∀ a : J.toSet, Mono (jF a) := fun a => inferInstance
  let : ∀ a : J.toSet, IsCardinalPresentable (Φ.obj a.val.left) d.κ := fun a => by
    let : IsCardinalPresentable a.val.left d.κ := (hr a).1
    exact isCardinalPresentable_of_equivalence a.val.left d.κ e
  let : ∀ a : J.toSet, IsCardinalPresentable (Φ.obj a.val.right) d.κ := fun a => by
    let : IsCardinalPresentable a.val.right d.κ := (hr a).2
    exact isCardinalPresentable_of_equivalence a.val.right d.κ e
  let : (SmallObject.functor jF).IsCardinalAccessible d.κ :=
    SmallObject.presheafAttachment_isCardinalAccessible.{0, u} jF d.κ
  let eχ := SmallObject.functorMapIso.{u} j Φ
  refine ⟨fun K _ _ => ?_⟩
  let : PreservesColimitsOfShape K (SmallObject.functor jF) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ d.κ K
  let : PreservesColimitsOfShape K (Φ.mapArrow ⋙ SmallObject.functor jF) := inferInstance
  let : PreservesColimitsOfShape K (SmallObject.functor j ⋙ Φ.mapArrow) :=
    preservesColimitsOfShape_of_natIso eχ.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ Φ.mapArrow

/-- The whole original Arrow iteration is accessible at its same stored
cardinal and original ordinal, without constructing a second iteration. -/
theorem originalLocalCellIteration_isCardinalAccessible
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    let d := originalLocalCellData S
    letI := d.regular
    letI := d.orderBot
    letI := d.eligible
    (SmallObject.iteration (originalLocalGenerators d.T) d.κ).IsCardinalAccessible d.κ := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : OrderBot d.κ.ord.ToType := d.orderBot
  let : (originalLocalGenerators d.T).IsCardinalForSmallObjectArgument d.κ := d.eligible
  let := SmallObject.hasPushouts (originalLocalGenerators d.T) d.κ
  let := SmallObject.hasColimitsOfShape_discrete (originalLocalGenerators d.T) d.κ
  let : (SmallObject.functor (originalLocalGenerators d.T).homFamily).IsCardinalAccessible d.κ :=
    originalLocalCellStep_isCardinalAccessible S
  exact SmallObject.SuccStruct.isCardinalAccessible_iteration
    (J := d.κ.ord.ToType) (SmallObject.ε (originalLocalGenerators d.T).homFamily) d.κ

/-- The original replacement equals the canonical terminal restriction of the
same native iteration as a whole functor, including every original map. -/
theorem originalLocalCellReplacement_eq_terminalIteration
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    let d := originalLocalCellData S
    letI := d.regular
    letI := d.orderBot
    letI := d.eligible
    originalLocalCellReplacement S =
      SmallObject.terminalIteration (originalLocalGenerators d.T) d.κ := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : OrderBot d.κ.ord.ToType := d.orderBot
  let : (originalLocalGenerators d.T).IsCardinalForSmallObjectArgument d.κ := d.eligible
  change terminal.arrowFunctor (SimplicialPresheaf.{u} D) ⋙
      (originalLocalCellFactorization S).Z = _
  rw [originalLocalCellFactorization_eq S]
  exact SmallObject.canonical_terminal_middle_eq_terminalIteration
    (originalLocalGenerators d.T) d.κ

/-- The same original local replacement is accessible at the single cardinal
returned by its actual chosen local-generator system. -/
theorem originalLocalCellReplacement_isCardinalAccessible
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    let d := originalLocalCellData S
    letI := d.regular
    (originalLocalCellReplacement S).IsCardinalAccessible d.κ := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : OrderBot d.κ.ord.ToType := d.orderBot
  let : (originalLocalGenerators d.T).IsCardinalForSmallObjectArgument d.κ := d.eligible
  let : IsCardinalLocallyPresentable (SimplicialPresheaf.{u} D) d.κ :=
    d.properties.2.2.2.2.2.2.1
  let : (SmallObject.iteration (originalLocalGenerators d.T) d.κ).IsCardinalAccessible d.κ :=
    originalLocalCellIteration_isCardinalAccessible S
  rw [originalLocalCellReplacement_eq_terminalIteration S]
  exact SmallObject.terminalIteration_isCardinalAccessible (originalLocalGenerators d.T) d.κ d.κ

/-- Larger regular test ranks transfer accessibility of the same original R;
its original system, cardinal, ordinal and natural maps are not reselected. -/
theorem originalLocalCellReplacement_isCardinalAccessible_of_le
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ) :
    (originalLocalCellReplacement S).IsCardinalAccessible μ := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : (originalLocalCellReplacement S).IsCardinalAccessible d.κ :=
    originalLocalCellReplacement_isCardinalAccessible S
  exact Functor.isCardinalAccessible_of_le _ h

/-- A larger regular test rank preserves the same original one-step functor;
the original selected generator family and cardinal remain fixed. -/
theorem originalLocalCellStep_isCardinalAccessible_of_le
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ) :
    let d := originalLocalCellData S
    letI := d.regular
    letI := d.orderBot
    letI := d.eligible
    letI := SmallObject.hasPushouts (originalLocalGenerators d.T) d.κ
    letI := SmallObject.hasColimitsOfShape_discrete (originalLocalGenerators d.T) d.κ
    (SmallObject.functor (originalLocalGenerators d.T).homFamily).IsCardinalAccessible μ := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : OrderBot d.κ.ord.ToType := d.orderBot
  let : (originalLocalGenerators d.T).IsCardinalForSmallObjectArgument d.κ := d.eligible
  let := SmallObject.hasPushouts (originalLocalGenerators d.T) d.κ
  let := SmallObject.hasColimitsOfShape_discrete (originalLocalGenerators d.T) d.κ
  let : (SmallObject.functor (originalLocalGenerators d.T).homFamily).IsCardinalAccessible d.κ :=
    originalLocalCellStep_isCardinalAccessible S
  exact Functor.isCardinalAccessible_of_le _ h

/-- Every larger regular test rank applies to the original iteration at the
stored cardinal ordinal, rather than to an iteration at the new rank. -/
theorem originalLocalCellIteration_isCardinalAccessible_of_le
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ) :
    let d := originalLocalCellData S
    letI := d.regular
    letI := d.orderBot
    letI := d.eligible
    (SmallObject.iteration (originalLocalGenerators d.T) d.κ).IsCardinalAccessible μ := by
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  let : OrderBot d.κ.ord.ToType := d.orderBot
  let : (originalLocalGenerators d.T).IsCardinalForSmallObjectArgument d.κ := d.eligible
  let : (SmallObject.iteration (originalLocalGenerators d.T) d.κ).IsCardinalAccessible d.κ :=
    originalLocalCellIteration_isCardinalAccessible S
  exact Functor.isCardinalAccessible_of_le _ h

section Cocones

variable {K : Type k} [Category.{ℓ} K] [EssentiallySmall.{u} K]

/-- The same R sends each supplied original colimiting cocone of an essentially
small filtered diagram to its literal mapped colimiting cocone. -/
def originalLocalCellReplacementPreservesCocone
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ) [IsCardinalFiltered K μ]
    {F : K ⥤ SimplicialPresheaf.{u} D} (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((originalLocalCellReplacement S).mapCocone c) := by
  let : (originalLocalCellReplacement S).IsCardinalAccessible μ :=
    originalLocalCellReplacement_isCardinalAccessible_of_le S μ h
  let : PreservesColimitsOfShape K (originalLocalCellReplacement S) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall _ μ K
  exact isColimitOfPreserves _ hc

/-- The original Arrow functor preserves both components of every original
filtered Arrow cocone; its maps are literally R.map(left) and R.map(right). -/
def originalLocalCellReplacementPreservesArrowCocone
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ) [IsCardinalFiltered K μ]
    {F : K ⥤ Arrow (SimplicialPresheaf.{u} D)} (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((originalLocalCellReplacement S).mapArrow.mapCocone c) := by
  let : HasColimitsOfShape K (SimplicialPresheaf.{u} D) :=
    hasColimitsOfShape_of_equivalence (equivSmallModel.{u} K).symm
  apply Comma.fstSndJointlyReflectColimit
  · change IsColimit ((originalLocalCellReplacement S).mapCocone
      (Arrow.leftFunc.mapCocone c))
    exact originalLocalCellReplacementPreservesCocone S μ h _
      (isColimitOfPreserves Arrow.leftFunc hc)
  · change IsColimit ((originalLocalCellReplacement S).mapCocone
      (Arrow.rightFunc.mapCocone c))
    exact originalLocalCellReplacementPreservesCocone S μ h _
      (isColimitOfPreserves Arrow.rightFunc hc)

/-- The actual mapped original cocone and its derived universal property form
a native colimit cocone; no target colimit witness is a caller premise. -/
def originalLocalCellReplacementColimitCocone
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ) [IsCardinalFiltered K μ]
    {F : K ⥤ SimplicialPresheaf.{u} D} (c : Cocone F) (hc : IsColimit c) :
    ColimitCocone (F ⋙ originalLocalCellReplacement S) :=
  { cocone := (originalLocalCellReplacement S).mapCocone c
    isColimit := originalLocalCellReplacementPreservesCocone S μ h c hc }

/-- The native chosen target colimit is compared with the same R of the
original cocone vertex, through the actual preserved cocone. -/
def originalLocalCellReplacementColimitIso
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ) [IsCardinalFiltered K μ]
    {F : K ⥤ SimplicialPresheaf.{u} D} (c : Cocone F) (hc : IsColimit c) :
    letI : HasColimit (F ⋙ originalLocalCellReplacement S) :=
      ⟨⟨originalLocalCellReplacementColimitCocone S μ h c hc⟩⟩
    colimit (F ⋙ originalLocalCellReplacement S) ≅
      (originalLocalCellReplacement S).obj c.pt := by
  let : HasColimit (F ⋙ originalLocalCellReplacement S) :=
    ⟨⟨originalLocalCellReplacementColimitCocone S μ h c hc⟩⟩
  exact colimit.isoColimitCocone (originalLocalCellReplacementColimitCocone S μ h c hc)

/-- The forward comparison sends every original target colimit injection to
the literal R-map of the original source-cocone leg. -/
@[reassoc]
theorem originalLocalCellReplacement_colimitIso_hom_leg
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ) [IsCardinalFiltered K μ]
    {F : K ⥤ SimplicialPresheaf.{u} D} (c : Cocone F) (hc : IsColimit c) (a : K) :
    letI : HasColimit (F ⋙ originalLocalCellReplacement S) :=
      ⟨⟨originalLocalCellReplacementColimitCocone S μ h c hc⟩⟩
    colimit.ι (F ⋙ originalLocalCellReplacement S) a ≫
        (originalLocalCellReplacementColimitIso S μ h c hc).hom =
      (originalLocalCellReplacement S).map (c.ι.app a) := by
  let : HasColimit (F ⋙ originalLocalCellReplacement S) :=
    ⟨⟨originalLocalCellReplacementColimitCocone S μ h c hc⟩⟩
  exact colimit.isoColimitCocone_ι_hom
    (originalLocalCellReplacementColimitCocone S μ h c hc) a

/-- The inverse comparison recovers every same original colimit injection from
the R-map of that prescribed source leg. -/
@[reassoc]
theorem originalLocalCellReplacement_colimitIso_inv_leg
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ) [IsCardinalFiltered K μ]
    {F : K ⥤ SimplicialPresheaf.{u} D} (c : Cocone F) (hc : IsColimit c) (a : K) :
    letI : HasColimit (F ⋙ originalLocalCellReplacement S) :=
      ⟨⟨originalLocalCellReplacementColimitCocone S μ h c hc⟩⟩
    (originalLocalCellReplacement S).map (c.ι.app a) ≫
        (originalLocalCellReplacementColimitIso S μ h c hc).inv =
      colimit.ι (F ⋙ originalLocalCellReplacement S) a := by
  let : HasColimit (F ⋙ originalLocalCellReplacement S) :=
    ⟨⟨originalLocalCellReplacementColimitCocone S μ h c hc⟩⟩
  exact colimit.isoColimitCocone_ι_inv
    (originalLocalCellReplacementColimitCocone S μ h c hc) a

/-- The actual comparison commutes with every supplied original diagram map
and its compatible cocone-vertex map, without a chosen natural filler. -/
theorem originalLocalCellReplacement_colimitIso_naturality
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ) [IsCardinalFiltered K μ]
    {F G : K ⥤ SimplicialPresheaf.{u} D} (c : Cocone F) (hc : IsColimit c)
    (c' : Cocone G) (hc' : IsColimit c') (a : F ⟶ G) (v : c.pt ⟶ c'.pt)
    (hv : ∀ j, c.ι.app j ≫ v = a.app j ≫ c'.ι.app j) :
    letI : HasColimit (F ⋙ originalLocalCellReplacement S) :=
      ⟨⟨originalLocalCellReplacementColimitCocone S μ h c hc⟩⟩
    letI : HasColimit (G ⋙ originalLocalCellReplacement S) :=
      ⟨⟨originalLocalCellReplacementColimitCocone S μ h c' hc'⟩⟩
    colimMap (Functor.whiskerRight a (originalLocalCellReplacement S)) ≫
        (originalLocalCellReplacementColimitIso S μ h c' hc').hom =
      (originalLocalCellReplacementColimitIso S μ h c hc).hom ≫
        (originalLocalCellReplacement S).map v := by
  let : HasColimit (F ⋙ originalLocalCellReplacement S) :=
    ⟨⟨originalLocalCellReplacementColimitCocone S μ h c hc⟩⟩
  let : HasColimit (G ⋙ originalLocalCellReplacement S) :=
    ⟨⟨originalLocalCellReplacementColimitCocone S μ h c' hc'⟩⟩
  change colimMap (Functor.whiskerRight a (originalLocalCellReplacement S)) ≫
      (originalLocalCellReplacementColimitIso S μ h c' hc').hom =
    (originalLocalCellReplacementColimitIso S μ h c hc).hom ≫
      (originalLocalCellReplacement S).map v
  apply colimit.hom_ext
  intro j
  simp only [ι_colimMap_assoc, Functor.whiskerRight_app,
    originalLocalCellReplacement_colimitIso_hom_leg,
    originalLocalCellReplacement_colimitIso_hom_leg_assoc, ← Functor.map_comp]
  exact congrArg (fun f => (originalLocalCellReplacement S).map f) (hv j).symm

/-- The inverse comparison also commutes with the same original diagram and
cocone-vertex maps; neither map is assumed invertible. -/
theorem originalLocalCellReplacement_colimitIso_inv_naturality
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ) [IsCardinalFiltered K μ]
    {F G : K ⥤ SimplicialPresheaf.{u} D} (c : Cocone F) (hc : IsColimit c)
    (c' : Cocone G) (hc' : IsColimit c') (a : F ⟶ G) (v : c.pt ⟶ c'.pt)
    (hv : ∀ j, c.ι.app j ≫ v = a.app j ≫ c'.ι.app j) :
    letI : HasColimit (F ⋙ originalLocalCellReplacement S) :=
      ⟨⟨originalLocalCellReplacementColimitCocone S μ h c hc⟩⟩
    letI : HasColimit (G ⋙ originalLocalCellReplacement S) :=
      ⟨⟨originalLocalCellReplacementColimitCocone S μ h c' hc'⟩⟩
    (originalLocalCellReplacementColimitIso S μ h c hc).inv ≫
        colimMap (Functor.whiskerRight a (originalLocalCellReplacement S)) =
      (originalLocalCellReplacement S).map v ≫
        (originalLocalCellReplacementColimitIso S μ h c' hc').inv := by
  let : HasColimit (F ⋙ originalLocalCellReplacement S) :=
    ⟨⟨originalLocalCellReplacementColimitCocone S μ h c hc⟩⟩
  let : HasColimit (G ⋙ originalLocalCellReplacement S) :=
    ⟨⟨originalLocalCellReplacementColimitCocone S μ h c' hc'⟩⟩
  have hn := originalLocalCellReplacement_colimitIso_naturality S μ h c hc c' hc' a v hv
  let e := originalLocalCellReplacementColimitIso S μ h c hc
  let e' := originalLocalCellReplacementColimitIso S μ h c' hc'
  change e.inv ≫ colimMap (Functor.whiskerRight a (originalLocalCellReplacement S)) =
    (originalLocalCellReplacement S).map v ≫ e'.inv
  calc
    _ = e.inv ≫ (colimMap (Functor.whiskerRight a (originalLocalCellReplacement S)) ≫
        e'.hom) ≫ e'.inv := by simp
    _ = e.inv ≫ (e.hom ≫ (originalLocalCellReplacement S).map v) ≫ e'.inv := by rw [hn]
    _ = _ := by simp

end Cocones

end SimplicialPresheaf.InjectiveKan
