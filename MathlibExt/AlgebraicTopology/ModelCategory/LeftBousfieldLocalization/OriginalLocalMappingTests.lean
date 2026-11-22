/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex

import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.OriginalRelativeMapping
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Data
import MathlibExt.AlgebraicTopology.ModelCategory.InverseOrdinalInjectiveLimit
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits
import MathlibExt.AlgebraicTopology.ModelCategory.UnderOverProperQuillen
import MathlibExt.CategoryTheory.SmallObject.ContinuousApproximation
import MathlibExt.AlgebraicTopology.ModelCategory.UnderCofibrantlyGenerated

/-!
# Actual mapping tests and continuous source comparisons

The original model lifts prove projective cofibrancy on every well ordered
continuous cofibration diagram. The actual source factors and caller colimits
are retained in the weak source comparisons used by derived locality.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe w v u
open CategoryTheory Limits

namespace HomotopicalAlgebra.OriginalRelativeMapping

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

local instance shapeLocallySmall : LocallySmall.{w} J := locallySmall_of_thin

local instance shapeEssentiallySmall : EssentiallySmall.{w} J := by
  exact essentiallySmall_of_small_of_locallySmall J

/-- A genuine continuous cofibration diagram with cofibrant bottom is
cofibrant in the original source-constructed projective model. Compatible
diagonals use the actual successor maps and every original limit cocone. -/
theorem projective_cofibrant_of_continuous
    (F : J ⥤ C) [F.IsWellOrderContinuous] [IsCofibrant (F.obj ⊥)]
    (hstep : ∀ j : J, ¬IsMax j → Cofibration (F.map (homOfLE (Order.le_succ j)))) :
    letI : ModelCategory (J ⥤ C) :=
      FunctorProjective.modelCategory (J := J) d
    IsCofibrant F := by
  let _ : ModelCategory (J ⥤ C) :=
    FunctorProjective.modelCategory (J := J) d
  rw [isCofibrant_iff, cofibration_iff,
    FunctorProjective.cofibrations_eq_objectwise_llp d]
  intro E Z q hq
  constructor
  intro a b outer
  let _ : Fibration (q.app ⊥) := ((mem_trivialFibrations_iff _).mp (hq ⊥)).1
  let _ : WeakEquivalence (q.app ⊥) := ((mem_trivialFibrations_iff _).mp (hq ⊥)).2
  let bottomSq : CommSq (initial.to (E.obj ⊥)) (initial.to (F.obj ⊥))
      (q.app ⊥) (b.app ⊥) := ⟨initialIsInitial.hom_ext _ _⟩
  obtain ⟨l, hl, _⟩ :=
    InverseOrdinalInjectiveLimit.exists_natTrans_of_fixed_bot q b hstep hq
      bottomSq.lift bottomSq.fac_right
  exact CommSq.HasLift.mk' ⟨l, initialIsInitial.hom_ext _ _, hl⟩

include d in
/-- Original pointwise weak comparisons between continuous cofibrant
cofibration diagrams induce weak maps on every supplied pair of colimits.
The projective model and its three pointwise class equations are constructed
from the original combinatorial source. -/
theorem weak_of_continuous_cofibrant_isColimits
    {F G : J ⥤ C} [F.IsWellOrderContinuous] [G.IsWellOrderContinuous]
    [IsCofibrant (F.obj ⊥)] [IsCofibrant (G.obj ⊥)]
    (hF : ∀ j : J, ¬IsMax j → Cofibration (F.map (homOfLE (Order.le_succ j))))
    (hG : ∀ j : J, ¬IsMax j → Cofibration (G.map (homOfLE (Order.le_succ j))))
    (α : F ⟶ G) (hα : ∀ j : J, weakEquivalences C (α.app j))
    {cF : Cocone F} {cG : Cocone G} (hcF : IsColimit cF) (hcG : IsColimit cG)
    (t : cF.pt ⟶ cG.pt) (ht : ∀ j : J, cF.ι.app j ≫ t = α.app j ≫ cG.ι.app j) :
    WeakEquivalence t := by
  let _ : HasColimitsOfShape J C := d.hasColimitsOfShape
  let _ : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let _ : IsCofibrant F := projective_cofibrant_of_continuous d F hF
  let _ : IsCofibrant G := projective_cofibrant_of_continuous d G hG
  let _ : (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := by
    apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    · intro X Y p hp
      rw [FunctorProjective.fibrations_eq d]
      exact fun _ => hp
    · intro X Y p hp
      rw [FunctorProjective.trivialFibrations_eq d]
      exact fun _ => hp
  let _ : WeakEquivalence α := (weakEquivalence_iff _).mpr (by
    rw [FunctorProjective.weakEquivalences_eq d]
    exact hα)
  let _ : WeakEquivalence (colimMap α) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := colimConstAdj) α
  let eF := (colimit.isColimit F).coconePointUniqueUpToIso hcF
  let eG := (colimit.isColimit G).coconePointUniqueUpToIso hcG
  have commutation : eF.hom ≫ t = colimMap α ≫ eG.hom := by
    apply colimit.hom_ext
    intro j
    rw [← Category.assoc, colimit.comp_coconePointUniqueUpToIso_hom hcF j,
      ht, ι_colimMap_assoc, colimit.comp_coconePointUniqueUpToIso_hom hcG j]
  exact (weakEquivalence_iff _).mpr
    (((weakEquivalences C).arrow_mk_iso_iff (Arrow.isoMk eF eG commutation)).mp
      (mem_weakEquivalences (colimMap α)))

end HomotopicalAlgebra.OriginalRelativeMapping

namespace HomotopicalAlgebra.OriginalRelativeMapping

open GeneratedFunctorialReplacements

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The same original I factory starts at the actual Q counit and retains
the complete continuous approximation on the original ordinal. -/
def continuousSource (F : J ⥤ C) : J ⥤ C := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact OriginalContinuousApproximation.sourceDiagram F
    (Arrow.mk ((counit d).app (F.obj ⊥))) d.cofibrantFactorizationData rfl

/-- Every comparison component and every naturality square is the original
continuous approximation's source counit. -/
def continuousCounit (F : J ⥤ C) : continuousSource d F ⟶ F := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact OriginalContinuousApproximation.sourceCounit F
    (Arrow.mk ((counit d).app (F.obj ⊥))) d.cofibrantFactorizationData rfl

/-- The full actual source approximation is continuous at every original
successor-limit, with the original preceding colimit cocone. -/
theorem continuousSource_continuous (F : J ⥤ C) :
    (continuousSource d F).IsWellOrderContinuous := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact OriginalContinuousApproximation.sourceDiagram_continuous F
    (Arrow.mk ((counit d).app (F.obj ⊥))) d.cofibrantFactorizationData rfl

/-- The entire bottom comparison Arrow is exactly the original generated
Q counit, including its actual source and target. -/
theorem continuousCounit_bot_arrow (F : J ⥤ C) :
    Arrow.mk ((continuousCounit d F).app ⊥) = Arrow.mk ((counit d).app (F.obj ⊥)) := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  change Arrow.mk ((OriginalContinuousApproximation.sourceCounit F
    (Arrow.mk ((counit d).app (F.obj ⊥))) d.cofibrantFactorizationData rfl).app ⊥) = _
  rw [OriginalContinuousApproximation.sourceCounit_app]
  exact (Arrow.arrow_mk_comp_eqToHom _ _).trans
    (OriginalContinuousApproximation.fullDiagram_bottom F
      (Arrow.mk ((counit d).app (F.obj ⊥))) d.cofibrantFactorizationData rfl)

/-- The bottom source object is the same original generated Q object. -/
theorem continuousSource_bot (F : J ⥤ C) :
    (continuousSource d F).obj ⊥ = (Q d).obj (F.obj ⊥) := by
  have h := congrArg Arrow.left (continuousCounit_bot_arrow d F)
  exact h

/-- The bottom comparison is weak from the original generated Q factor. -/
theorem continuousCounit_bot_weak (F : J ⥤ C) :
    weakEquivalences C ((continuousCounit d F).app ⊥) := by
  have h := congrArg (fun q : Arrow C => (weakEquivalences C) q.hom)
    (continuousCounit_bot_arrow d F)
  exact h.mpr (counit_weak d (F.obj ⊥))

/-- Every source successor is the original I factory's cofibration. -/
theorem continuousSource_successor_cofibration (F : J ⥤ C) (j : J) (hj : ¬IsMax j) :
    Cofibration ((continuousSource d F).map (homOfLE (Order.le_succ j))) := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  apply (cofibration_iff _).mpr
  exact OriginalContinuousApproximation.sourceDiagram_successor_mem F
    (Arrow.mk ((counit d).app (F.obj ⊥))) d.cofibrantFactorizationData rfl j hj

/-- Every successor comparison is the same original I factory's actual
trivial fibration. No weakness at a limit is supplied. -/
theorem continuousCounit_successor_trivialFibration (F : J ⥤ C) (j : J) (hj : ¬IsMax j) :
    trivialFibrations C ((continuousCounit d F).app (Order.succ j)) := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact OriginalContinuousApproximation.sourceCounit_successor_mem F
    (Arrow.mk ((counit d).app (F.obj ⊥))) d.cofibrantFactorizationData rfl j hj

/-- All original source maps, including every limit transition, are
cofibrations by the original model WFS and actual source continuity. -/
theorem continuousSource_map_cofibration (F : J ⥤ C) {i j : J} (g : i ⟶ j) :
    Cofibration ((continuousSource d F).map g) := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  let _ : (continuousSource d F).IsWellOrderContinuous := continuousSource_continuous d F
  let _ : (cofibrations C).IsStableUnderTransfiniteComposition.{w} := by
    rw [← trivialFibrations_llp]
    infer_instance
  let c : (cofibrations C).TransfiniteCompositionOfShape J
      (colimit.ι (continuousSource d F) ⊥) := {
    F := continuousSource d F
    isoBot := Iso.refl _
    incl := (colimit.cocone (continuousSource d F)).ι
    isColimit := colimit.isColimit _
    fac := Category.id_comp _
    map_mem k hk := (cofibration_iff _).mp (continuousSource_successor_cofibration d F k hk) }
  exact (cofibration_iff _).mpr (c.mem_map g)

/-- Every actual source stage is cofibrant from the same original bottom Q
and the original continuous source maps. -/
theorem continuousSource_cofibrant (F : J ⥤ C) (j : J) :
    IsCofibrant ((continuousSource d F).obj j) := by
  let _ : IsCofibrant ((continuousSource d F).obj ⊥) := by
    rw [continuousSource_bot]
    exact Q_isCofibrant d (F.obj ⊥)
  let _ : Cofibration ((continuousSource d F).map (homOfLE bot_le : (⊥ : J) ⟶ j)) :=
    continuousSource_map_cofibration d F _
  exact isCofibrant_of_cofibration
    ((continuousSource d F).map (homOfLE bot_le : (⊥ : J) ⟶ j))

/-- Every original ordinal map retains the complete counit naturality equation. -/
@[reassoc]
theorem continuousCounit_naturality (F : J ⥤ C) {i j : J} (g : i ⟶ j) :
    (continuousSource d F).map g ≫ (continuousCounit d F).app j =
      (continuousCounit d F).app i ≫ F.map g :=
  (continuousCounit d F).naturality g

end HomotopicalAlgebra.OriginalRelativeMapping

namespace HomotopicalAlgebra.OriginalRelativeMapping

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- Regard every original transition from the bottom as an object of its
original Under category. Every original diagram map is retained. -/
def underBottom (F : J ⥤ C) : J ⥤ Under (F.obj ⊥) where
  obj j := Under.mk (F.map (homOfLE bot_le : (⊥ : J) ⟶ j))
  map {i j} g := Under.homMk
    (U := Under.mk (F.map (homOfLE bot_le : (⊥ : J) ⟶ i)))
    (V := Under.mk (F.map (homOfLE bot_le : (⊥ : J) ⟶ j)))
    (F.map g) (by simp only [Under.mk_hom]; rw [← F.map_comp]; rfl)
  map_id j := by ext; exact F.map_id j
  map_comp g h := by ext; exact F.map_comp g h

/-- The actual caller cocone is an Under cocone with its same bottom leg. -/
def underBottomCocone {F : J ⥤ C} (c : Cocone F) : Cocone (underBottom F) where
  pt := Under.mk (c.ι.app ⊥)
  ι := {
    app j := Under.homMk (U := (underBottom F).obj j) (V := Under.mk (c.ι.app ⊥))
      (c.ι.app j) (by
        change F.map (homOfLE bot_le : (⊥ : J) ⟶ j) ≫ c.ι.app j = c.ι.app ⊥
        exact c.w (homOfLE bot_le : (⊥ : J) ⟶ j))
    naturality i j g := by ext; exact c.ι.naturality g }

/-- Connected creation retains the full actual colimit universal property. -/
def underBottomIsColimit {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) :
    IsColimit (underBottomCocone c) := by
  let _ : IsConnected J := IsFiltered.isConnected J
  apply isColimitOfReflects (Under.forget (F.obj ⊥))
  change IsColimit c
  exact hc

omit [ModelCategory C] [SuccOrder J] [WellFoundedLT J] in
/-- All original continuous limit cocones remain colimiting in the Under
diagram. No cofibrancy of the original bottom object is required. -/
theorem underBottom_continuous (F : J ⥤ C) [F.IsWellOrderContinuous] :
    (underBottom F).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    let _ : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
    let _ : IsConnected (Set.Iio m) := IsFiltered.isConnected (Set.Iio m)
    apply isColimitOfReflects (Under.forget (F.obj ⊥))
    change IsColimit ((Set.principalSegIio m).cocone F)
    exact F.isColimitOfIsWellOrderContinuous m hm⟩

omit [SuccOrder J] [WellFoundedLT J] in
/-- The Under bottom is cofibrant because its structure map is the original
identity, even when the corresponding coefficient object is not cofibrant. -/
theorem underBottom_bot_cofibrant (F : J ⥤ C) :
    IsCofibrant ((underBottom F).obj ⊥) := by
  let i : Under.mk (𝟙 (F.obj ⊥)) ⟶ (underBottom F).obj ⊥ :=
    Under.homMk (U := Under.mk (𝟙 (F.obj ⊥))) (V := (underBottom F).obj ⊥)
      (F.map (homOfLE bot_le : (⊥ : J) ⟶ ⊥))
      (by change 𝟙 _ ≫ _ = _; exact Category.id_comp _)
  apply (isCofibrant_iff_of_isInitial i Under.mkIdInitial).mpr
  rw [cofibrations_under_iff]
  change Cofibration (F.map (homOfLE bot_le : (⊥ : J) ⟶ ⊥))
  have hid : (homOfLE bot_le : (⊥ : J) ⟶ ⊥) = 𝟙 _ := Subsingleton.elim _ _
  rw [hid, F.map_id]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The full original comparison determines its actual functorial pushout
descent in the original target-bottom Under category. -/
def underPushoutComparison {F G : J ⥤ C} (α : F ⟶ G) :
    underBottom F ⋙ Under.pushout (α.app ⊥) ⟶ underBottom G where
  app j := Under.homMk
    (U := (underBottom F ⋙ Under.pushout (α.app ⊥)).obj j)
    (V := (underBottom G).obj j)
    (pushout.desc (α.app j) (G.map (homOfLE bot_le : (⊥ : J) ⟶ j))
      (α.naturality (homOfLE bot_le : (⊥ : J) ⟶ j)))
    (by
      change pushout.inr (F.map (homOfLE bot_le : (⊥ : J) ⟶ j)) (α.app ⊥) ≫
        pushout.desc (α.app j) (G.map (homOfLE bot_le : (⊥ : J) ⟶ j)) _ =
        G.map (homOfLE bot_le : (⊥ : J) ⟶ j)
      exact pushout.inr_desc _ _ _)
  naturality i j g := by
    ext
    change pushout.desc (F.map g ≫ pushout.inl _ _) (pushout.inr _ _) _ ≫
        pushout.desc (α.app j) (G.map (homOfLE bot_le : (⊥ : J) ⟶ j)) _ =
      pushout.desc (α.app i) (G.map (homOfLE bot_le : (⊥ : J) ⟶ i)) _ ≫ G.map g
    dsimp only [underBottom, CategoryTheory.Under.mk_hom, CategoryTheory.Under.mk_right]
    apply pushout.hom_ext
    · simpa only [pushout.inl_desc_assoc, pushout.inl_desc, Category.assoc] using
        α.naturality g
    · have hg : (homOfLE bot_le : (⊥ : J) ⟶ i) ≫ g =
          (homOfLE bot_le : (⊥ : J) ⟶ j) := Subsingleton.elim _ _
      simpa only [pushout.inr_desc_assoc, pushout.inr_desc, Category.assoc, hg] using
        G.map_comp (homOfLE bot_le : (⊥ : J) ⟶ i) g

omit [SuccOrder J] [WellFoundedLT J] in
/-- Each source leg is the same original comparison component. -/
@[reassoc]
theorem underPushoutComparison_inl {F G : J ⥤ C} (α : F ⟶ G) (j : J) :
    pushout.inl (F.map (homOfLE bot_le : (⊥ : J) ⟶ j)) (α.app ⊥) ≫
        ((underPushoutComparison α).app j).right = α.app j :=
  pushout.inl_desc _ _ _

omit [SuccOrder J] [WellFoundedLT J] in
/-- Each target leg is the original target transition from the bottom. -/
@[reassoc]
theorem underPushoutComparison_inr {F G : J ⥤ C} (α : F ⟶ G) (j : J) :
    pushout.inr (F.map (homOfLE bot_le : (⊥ : J) ⟶ j)) (α.app ⊥) ≫
        ((underPushoutComparison α).app j).right =
      G.map (homOfLE bot_le : (⊥ : J) ⟶ j) :=
  Under.w ((underPushoutComparison α).app j)

end HomotopicalAlgebra.OriginalRelativeMapping

namespace HomotopicalAlgebra.OriginalRelativeMapping

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLeftProper C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

include d in
set_option backward.isDefEq.respectTransparency false in
/-- A pointwise original weak comparison between any two continuous
cofibration diagrams induces a weak map on the supplied colimits. Both
original bottom objects may be uncofibrant. The actual pushout of the bottom
comparison and the source-generated projective Under model prove the result. -/
theorem weak_of_continuous_isColimits
    {F G : J ⥤ C} [F.IsWellOrderContinuous] [G.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → Cofibration (F.map (homOfLE (Order.le_succ j))))
    (hG : ∀ j : J, ¬IsMax j → Cofibration (G.map (homOfLE (Order.le_succ j))))
    (α : F ⟶ G) (hα : ∀ j : J, weakEquivalences C (α.app j))
    {cF : Cocone F} {cG : Cocone G} (hcF : IsColimit cF) (hcG : IsColimit cG)
    (t : cF.pt ⟶ cG.pt) (ht : ∀ j : J, cF.ι.app j ≫ t = α.app j ≫ cG.ι.app j) :
    WeakEquivalence t := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  let _ : (cofibrations C).IsStableUnderTransfiniteComposition.{w} := by
    rw [← trivialFibrations_llp]
    infer_instance
  let c : (cofibrations C).TransfiniteCompositionOfShape J (cF.ι.app ⊥) := {
    F := F
    isoBot := Iso.refl _
    incl := cF.ι
    isColimit := hcF
    fac := Category.id_comp _
    map_mem j hj := (cofibration_iff _).mp (hF j hj) }
  let _ : WeakEquivalence (α.app ⊥) := (weakEquivalence_iff _).mpr (hα ⊥)
  let _ : Cofibration (cF.ι.app ⊥) :=
    (cofibration_iff _).mpr (c.mem_incl_app ⊥)
  let H : J ⥤ Under (G.obj ⊥) := underBottom F ⋙ Under.pushout (α.app ⊥)
  let U : J ⥤ Under (G.obj ⊥) := underBottom G
  let _ : (underBottom F).IsWellOrderContinuous := underBottom_continuous F
  let _ : U.IsWellOrderContinuous := underBottom_continuous G
  let _ : PreservesWellOrderContinuousOfShape J (Under.pushout (α.app ⊥)) :=
    { preservesColimitsOfShape _ _ := inferInstance }
  let _ : H.IsWellOrderContinuous := inferInstance
  let _ : (Under.mapPushoutAdj (α.app ⊥)).IsQuillenAdjunction :=
    Under.mapPushoutAdj_isQuillenAdjunction _
  let _ : IsCofibrant ((underBottom F).obj ⊥) := underBottom_bot_cofibrant F
  let _ : IsCofibrant (H.obj ⊥) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Under.mapPushoutAdj (α.app ⊥)) inferInstance
  let _ : IsCofibrant (U.obj ⊥) := underBottom_bot_cofibrant G
  have hH : ∀ j : J, ¬IsMax j → Cofibration (H.map (homOfLE (Order.le_succ j))) := by
    intro j hj
    let _ : Cofibration ((underBottom F).map (homOfLE (Order.le_succ j))) :=
      (cofibrations_under_iff (F.obj ⊥) _).mpr (hF j hj)
    let adjProof : (Under.mapPushoutAdj (α.app ⊥)).IsQuillenAdjunction := inferInstance
    exact (cofibration_iff _).mpr
      (adjProof.preservesCofibrations _ (mem_cofibrations _))
  have hU : ∀ j : J, ¬IsMax j → Cofibration (U.map (homOfLE (Order.le_succ j))) := by
    intro j hj
    exact (cofibrations_under_iff (G.obj ⊥) _).mpr (hG j hj)
  let β : H ⟶ U := underPushoutComparison α
  have hβ : ∀ j : J, weakEquivalences (Under (G.obj ⊥)) (β.app j) := by
    intro j
    let _ : Cofibration (F.map (homOfLE bot_le : (⊥ : J) ⟶ j)) :=
      (cofibration_iff _).mpr (c.mem_map (homOfLE bot_le : (⊥ : J) ⟶ j))
    let _ : WeakEquivalence
        (pushout.inl (F.map (homOfLE bot_le : (⊥ : J) ⟶ j)) (α.app ⊥)) :=
      IsLeftProper.weakEquivalence_of_isPushout
        (IsPushout.of_hasPushout (F.map (homOfLE bot_le : (⊥ : J) ⟶ j)) (α.app ⊥))
    let _ : WeakEquivalence (α.app j) := (weakEquivalence_iff _).mpr (hα j)
    let _ : WeakEquivalence ((β.app j).right) :=
      weakEquivalence_of_precomp_of_fac (underPushoutComparison_inl α j)
    exact (weakEquivalence_iff _).mp
      ((weakEquivalences_under_iff (G.obj ⊥) (β.app j)).mpr inferInstance)
  let cH : Cocone H := (Under.pushout (α.app ⊥)).mapCocone (underBottomCocone cF)
  let cU : Cocone U := underBottomCocone cG
  let hcH : IsColimit cH :=
    isColimitOfPreserves (Under.pushout (α.app ⊥)) (underBottomIsColimit hcF)
  let hcU : IsColimit cU := underBottomIsColimit hcG
  let p : pushout (cF.ι.app ⊥) (α.app ⊥) ⟶ cG.pt :=
    pushout.desc t (cG.ι.app ⊥) (ht ⊥)
  let pU : cH.pt ⟶ cU.pt := Under.homMk (U := cH.pt) (V := cU.pt) p
    (by change pushout.inr _ _ ≫ p = cG.ι.app ⊥; exact pushout.inr_desc _ _ _)
  have hpU : ∀ j : J, cH.ι.app j ≫ pU = β.app j ≫ cU.ι.app j := by
    intro j
    ext
    change pushout.desc (cF.ι.app j ≫ pushout.inl _ _) (pushout.inr _ _) _ ≫ p =
      ((underPushoutComparison α).app j).right ≫ cG.ι.app j
    dsimp only [underBottom, CategoryTheory.Under.mk_hom, CategoryTheory.Under.mk_right]
    apply pushout.hom_ext
    · simpa only [p, underPushoutComparison, Under.homMk_right,
        pushout.inl_desc_assoc, pushout.inl_desc, Category.assoc] using ht j
    · simpa only [p, underPushoutComparison, Under.homMk_right,
        pushout.inr_desc_assoc, pushout.inr_desc, Category.assoc] using
        (cG.w (homOfLE bot_le : (⊥ : J) ⟶ j)).symm
  let _ : HasCoproducts.{w} (Under (G.obj ⊥)) := inferInstance
  let dU : CofibrantGenerationData (Under (G.obj ⊥)) κ :=
    CofibrantGenerationData.under κ d (G.obj ⊥)
  let _ : WeakEquivalence pU :=
    weak_of_continuous_cofibrant_isColimits dU hH hU β hβ hcH hcU pU hpU
  let _ : WeakEquivalence p :=
    (weakEquivalences_under_iff (G.obj ⊥) pU).mp inferInstance
  let _ : WeakEquivalence (pushout.inl (cF.ι.app ⊥) (α.app ⊥)) :=
    IsLeftProper.weakEquivalence_of_isPushout
      (IsPushout.of_hasPushout (cF.ι.app ⊥) (α.app ⊥))
  have hcomp : weakEquivalences C (pushout.inl (cF.ι.app ⊥) (α.app ⊥) ≫ p) :=
    (weakEquivalences C).comp_mem _ _ (mem_weakEquivalences _) (mem_weakEquivalences _)
  rw [pushout.inl_desc] at hcomp
  exact (weakEquivalence_iff _).mpr hcomp

end HomotopicalAlgebra.OriginalRelativeMapping

namespace HomotopicalAlgebra.OriginalRelativeMapping

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLeftProper C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

set_option backward.isDefEq.respectTransparency false in
/-- The actual continuous source counit is weak at every original stage.
Successors use the same I right factor; every genuine limit uses the
preceding actual source and target colimit cocones and original left proper
continuous-cofibration comparison. No limit-stage weakness is assumed. -/
theorem continuousCounit_weak
    (F : J ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → Cofibration (F.map (homOfLE (Order.le_succ j))))
    (cF : Cocone F) (hcF : IsColimit cF) (j : J) :
    weakEquivalences C ((continuousCounit d F).app j) := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  let _ : (continuousSource d F).IsWellOrderContinuous := continuousSource_continuous d F
  let _ : (cofibrations C).IsStableUnderTransfiniteComposition.{w} := by
    rw [← trivialFibrations_llp]
    infer_instance
  let c : (cofibrations C).TransfiniteCompositionOfShape J (cF.ι.app ⊥) := {
    F := F
    isoBot := Iso.refl _
    incl := cF.ι
    isColimit := hcF
    fac := Category.id_comp _
    map_mem k hk := (cofibration_iff _).mp (hF k hk) }
  have hMaps {i k : J} (g : i ⟶ k) : Cofibration (F.map g) :=
    (cofibration_iff _).mpr (c.mem_map g)
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl : j = ⊥ := by simpa using hj
    exact continuousCounit_bot_weak d F
  | succ j hj _ih =>
    exact (continuousCounit_successor_trivialFibration d F j hj).2
  | isSuccLimit j hj ih =>
    let _ : OrderBot (Set.Iio j) := {
      bot := ⟨⊥, hj.bot_lt⟩
      bot_le _ := bot_le }
    let r : Set.Iio j ⥤ J := (Set.principalSegIio j).monotone.functor
    let S : Set.Iio j ⥤ C := r ⋙ continuousSource d F
    let T : Set.Iio j ⥤ C := r ⋙ F
    let r₀ : Set.Iio j ≤i J := Set.principalSegIio j
    let _ : S.IsWellOrderContinuous := inferInstanceAs
      ((r₀.monotone.functor ⋙ continuousSource d F).IsWellOrderContinuous)
    let _ : T.IsWellOrderContinuous := inferInstanceAs
      ((r₀.monotone.functor ⋙ F).IsWellOrderContinuous)
    have hS : ∀ k : Set.Iio j, ¬IsMax k →
        Cofibration (S.map (homOfLE (Order.le_succ k))) := by
      intro k _hk
      exact continuousSource_map_cofibration d F (r.map (homOfLE (Order.le_succ k)))
    have hT : ∀ k : Set.Iio j, ¬IsMax k →
        Cofibration (T.map (homOfLE (Order.le_succ k))) := by
      intro k _hk
      exact hMaps (r.map (homOfLE (Order.le_succ k)))
    let α : S ⟶ T := Functor.whiskerLeft r (continuousCounit d F)
    have hα : ∀ k : Set.Iio j, weakEquivalences C (α.app k) :=
      fun k => ih k.1 k.2
    let cS : Cocone S := (Set.principalSegIio j).cocone (continuousSource d F)
    let cT : Cocone T := (Set.principalSegIio j).cocone F
    let hcS : IsColimit cS := (continuousSource d F).isColimitOfIsWellOrderContinuous j hj
    let hcT : IsColimit cT := F.isColimitOfIsWellOrderContinuous j hj
    have hw : WeakEquivalence ((continuousCounit d F).app j) :=
      weak_of_continuous_isColimits d hS hT α hα hcS hcT
        ((continuousCounit d F).app j)
        (fun k => (continuousCounit d F).naturality (homOfLE k.2.le))
    exact (weakEquivalence_iff _).mp hw

set_option backward.isDefEq.respectTransparency false in
/-- The same actual counit is weak on every supplied source/target colimit
descent, retaining all original cocone legs and the entire endpoint map. -/
theorem continuousCounit_colimit_weak
    (F : J ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → Cofibration (F.map (homOfLE (Order.le_succ j))))
    (cQ : Cocone (continuousSource d F)) (hcQ : IsColimit cQ)
    (cF : Cocone F) (hcF : IsColimit cF)
    (t : cQ.pt ⟶ cF.pt)
    (ht : ∀ j : J, cQ.ι.app j ≫ t = (continuousCounit d F).app j ≫ cF.ι.app j) :
    WeakEquivalence t := by
  let _ : (continuousSource d F).IsWellOrderContinuous := continuousSource_continuous d F
  exact weak_of_continuous_isColimits d
    (continuousSource_successor_cofibration d F) hF (continuousCounit d F)
    (continuousCounit_weak d F hF cF hcF) hcQ hcF t ht

end HomotopicalAlgebra.OriginalRelativeMapping
