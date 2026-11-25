/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CellularSource
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits
public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.OriginalShapes
public import MathlibExt.CategoryTheory.SmallObject.CellularRetractsClosure
public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.TransfiniteAbsorption
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import MathlibExt.CategoryTheory.Limits.Preserves.Retract
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Common bounds for the original compact and small cellular sources

The original I and J families retain their own compactness and smallness
data. The common bounds are selected from those actual small families.
Applying the original J-source smallness retains every original regular
ordinal, continuous chain and caller-supplied colimit cocone, including its
actual source-Hom stage factorization and equality comparisons.

The larger regular bound does not replace the original cardinal used by
the given generated factorization factories.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.CellularLocalizationSmallness

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)

local instance : d.I.IsSmall.{w} := d.I_smallObject.isSmall
local instance : d.J.IsSmall.{w} := d.J_smallObject.isSmall

/-- Both compact original endpoints retain their own actual chosen bounds. -/
def compactBound (i : d.I.toSet) : Cardinal.{w} :=
  max (h.I_domains_compact i).choose (h.I_codomains_compact i).choose

/-- The common compactness bound is selected from the original small I family. -/
def commonCompactBound : Cardinal.{w} :=
  max Cardinal.aleph0
    (⨆ k : Shrink.{w} d.I.toSet, compactBound h ((equivShrink d.I.toSet).symm k))

/-- Every original generating endpoint bound lies below the same common bound. -/
theorem compactBound_le_common (i : d.I.toSet) :
    compactBound h i ≤ commonCompactBound h := by
  have hi := le_ciSup
    (f := fun k : Shrink.{w} d.I.toSet => compactBound h ((equivShrink d.I.toSet).symm k))
    Cardinal.bddAbove_of_small ((equivShrink d.I.toSet) i)
  simpa only [commonCompactBound, Equiv.symm_apply_apply] using hi.trans (le_max_right _ _)

/-- Original generating domains are compact at the same unchanged common bound. -/
theorem domain_compact (i : d.I.toSet) :
    IsCellularCompactAt d.I i.1.left (commonCompactBound h) :=
  (h.I_domains_compact i).choose_spec.mono
    ((le_max_left _ _).trans (compactBound_le_common h i))

/-- Original generating codomains have the same full compactness comparison. -/
theorem codomain_compact (i : d.I.toSet) :
    IsCellularCompactAt d.I i.1.right (commonCompactBound h) :=
  (h.I_codomains_compact i).choose_spec.mono
    ((le_max_right _ _).trans (compactBound_le_common h i))

/-- The bound is attached to the original actual J source. -/
def smallBound (j : d.J.toSet) : Cardinal.{w} := (h.J_domains_small j).choose

/-- Uniform smallness uses only the original small family of actual J sources. -/
def commonSmallBound : Cardinal.{w} :=
  max Cardinal.aleph0
    (⨆ k : Shrink.{w} d.J.toSet, smallBound h ((equivShrink d.J.toSet).symm k))

/-- Every actual original J source retains a bound below the same selected common bound. -/
theorem smallBound_le_common (j : d.J.toSet) : smallBound h j ≤ commonSmallBound h := by
  have hj := le_ciSup
    (f := fun k : Shrink.{w} d.J.toSet => smallBound h ((equivShrink d.J.toSet).symm k))
    Cardinal.bddAbove_of_small ((equivShrink d.J.toSet) j)
  simpa only [commonSmallBound, Equiv.symm_apply_apply] using hj.trans (le_max_right _ _)

/-- The original source Hom preserves the same complete supplied regular chain. -/
theorem preservesOriginalChain (j : d.J.toSet)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : commonSmallBound h < μ) (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ a : μ.ord.ToType, ¬ IsMax a →
      SmallObject.relativeCellMaps.{w} d.I (F.map (homOfLE (Order.le_succ a)))) :
    PreservesColimit F (coyoneda.obj (op j.1.left)) :=
  (h.J_domains_small j).choose_spec μ ((smallBound_le_common h j).trans_lt hμ) F hF

/-- The caller's original cocone remains colimiting after the same original source Hom. -/
def mappedOriginalCocone (j : d.J.toSet)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : commonSmallBound h < μ) (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ a : μ.ord.ToType, ¬ IsMax a →
      SmallObject.relativeCellMaps.{w} d.I (F.map (homOfLE (Order.le_succ a))))
    (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (op j.1.left)).mapCocone c) := by
  letI : PreservesColimit F (coyoneda.obj (op j.1.left)) :=
    preservesOriginalChain h j μ hμ F hF
  exact isColimitOfPreserves (coyoneda.obj (op j.1.left)) hc

/-- Every original source map into this actual endpoint factors through an original stage. -/
theorem existsOriginalStage (j : d.J.toSet)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : commonSmallBound h < μ) (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ a : μ.ord.ToType, ¬ IsMax a →
      SmallObject.relativeCellMaps.{w} d.I (F.map (homOfLE (Order.le_succ a))))
    (c : Cocone F) (hc : IsColimit c) (f : j.1.left ⟶ c.pt) :
    ∃ (a : μ.ord.ToType) (g : j.1.left ⟶ F.obj a), g ≫ c.ι.app a = f := by
  let _ : PreservesColimit F (coyoneda.obj (op j.1.left)) :=
    preservesOriginalChain h j μ hμ F hF
  exact exists_hom_of_preservesColimit_coyoneda hc f

/-- Equality at the caller's actual endpoint is witnessed at an original common later stage. -/
theorem existsOriginalStageEquality (j : d.J.toSet)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : commonSmallBound h < μ) (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ a : μ.ord.ToType, ¬ IsMax a →
      SmallObject.relativeCellMaps.{w} d.I (F.map (homOfLE (Order.le_succ a))))
    (c : Cocone F) (hc : IsColimit c) {a b : μ.ord.ToType}
    (f : j.1.left ⟶ F.obj a) (g : j.1.left ⟶ F.obj b)
    (hfg : f ≫ c.ι.app a = g ≫ c.ι.app b) :
    ∃ (e : μ.ord.ToType) (s : a ⟶ e) (t : b ⟶ e), f ≫ F.map s = g ≫ F.map t := by
  let _ : PreservesColimit F (coyoneda.obj (op j.1.left)) :=
    preservesOriginalChain h j μ hμ F hF
  exact exists_eq_of_preservesColimit_coyoneda hc f g hfg

/-- A common larger regular bound is constructed while retaining the original factory cardinal. -/
theorem existsCommonRegularBound (fixed : Type w) :
    ∃ μ : Cardinal.{w}, μ.IsRegular ∧ κ < μ ∧ commonCompactBound h < μ ∧
      commonSmallBound h < μ ∧ HasCardinalLT fixed μ := by
  let T := κ.ord.ToType ⊕ ((commonCompactBound h).ord.ToType ⊕
    ((commonSmallBound h).ord.ToType ⊕ fixed))
  obtain ⟨μ, hμ, hT⟩ := HasCardinalLT.exists_regular_cardinal.{w} T
  refine ⟨μ, hμ, ?_, ?_, ?_, ?_⟩
  · simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using
      hT.of_injective (Sum.inl : κ.ord.ToType → T) Sum.inl_injective
  · simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using
      hT.of_injective (fun a => (Sum.inr (Sum.inl a) : T))
        (Sum.inr_injective.comp Sum.inl_injective)
  · simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using
      hT.of_injective (fun a => (Sum.inr (Sum.inr (Sum.inl a)) : T))
        (Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inl_injective))
  · exact hT.of_injective (fun a => (Sum.inr (Sum.inr (Sum.inr a)) : T))
      (Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inr_injective))

end HomotopicalAlgebra.CellularLocalizationSmallness



namespace HomotopicalAlgebra.CellularLocalizationSmallness

/-- Fewer than a regular cardinal's own number of original stages have a
common bound in the same original ordinal. -/
theorem exists_regular_stage_bound {K : Type w}
    (μ : Cardinal.{w}) [Fact μ.IsRegular]
    (a : K → μ.ord.ToType) (hK : Cardinal.mk K < μ) :
    ∃ e : μ.ord.ToType, ∀ k : K, a k ≤ e := by
  have hcof : Order.cof μ.ord.ToType = μ :=
    (Ordinal.cof_toType μ.ord).trans (Fact.out : μ.IsRegular).cof_ord
  have hnot : ¬ IsCofinal (Set.range a) := by
    intro ha
    have hle := (Order.cof_le ha).trans (Cardinal.mk_range_le (f := a))
    rw [hcof] at hle
    exact (not_le_of_gt hK) hle
  obtain ⟨e, he⟩ := not_isCofinal_iff.mp hnot
  exact ⟨e, fun k => (he (a k) (Set.mem_range_self k)).le⟩

end HomotopicalAlgebra.CellularLocalizationSmallness


namespace HomotopicalAlgebra.IsCellularCompactAt

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  {A : C} {γ : Cardinal.{w}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Compactness captures boundedly many actual original cell occurrences.
Their actual stage maps then construct a factor through a single original
stage; no bounded-support or smallness conclusion is an input. -/
theorem exists_stage_of_cell_history (h : IsCellularCompactAt.{w} P A γ)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType] (hγ : γ < μ)
    (F : μ.ord.ToType ⥤ C) (s : Cocone F)
    {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X : C} {f : X ⟶ s.pt}
    (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)
    (r : X ⟶ F.obj ⊥) (hr : r ≫ s.ι.app ⊥ = f)
    (stage : c.Cells → μ.ord.ToType)
    (b : (a : c.Cells) → a.i.1.right ⟶ F.obj (stage a))
    (hb : ∀ a : c.Cells, b a ≫ s.ι.app (stage a) = a.ι)
    (hmono : ∀ e : μ.ord.ToType, Mono (s.ι.app e)) (g : A ⟶ s.pt) :
    ∃ (e : μ.ord.ToType) (k : A ⟶ F.obj e), k ≫ s.ι.app e = g := by
  obtain ⟨t, ht, k, hk⟩ := h O X s.pt f c g
  obtain ⟨e, he⟩ := CellularLocalizationSmallness.exists_regular_stage_bound μ
    (fun a : t.complex.Cells => stage (t.originalCell a)) (ht.trans_lt hγ)
  let : Mono (s.ι.app e) := hmono e
  let root : X ⟶ F.obj e := r ≫ F.map (homOfLE bot_le)
  have hroot : root ≫ s.ι.app e = t.hom ≫ t.inclusion := by
    dsimp only [root]
    rw [Category.assoc, s.w, hr]
    exact t.fac.symm
  let cells (a : t.complex.Cells) : a.i.1.right ⟶ F.obj e :=
    eqToHom (congrArg (fun z : P.toSet => z.1.right) (t.originalCell_label a)) ≫
      b (t.originalCell a) ≫ F.map (homOfLE (he a))
  have hcells (a : t.complex.Cells) :
      cells a ≫ s.ι.app e = a.ι ≫ t.inclusion := by
    dsimp only [cells]
    rw [Category.assoc, Category.assoc, s.w, hb]
    exact (t.originalCell_inclusion a).symm
  obtain ⟨m, hm⟩ := t.complex.exists_lift_through_mono
    t.inclusion (s.ι.app e) root hroot cells hcells
  exact ⟨e, k ≫ m, by rw [Category.assoc, hm, hk]⟩

end HomotopicalAlgebra.IsCellularCompactAt

namespace HomotopicalAlgebra.CellularLocalizationSmallness

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

variable {d} (h : CellularSource d)

include h in
/-- Every original cocone inclusion of an original relative I-cell chain
is monic, by the original model cofibrations and their effective-mono data. -/
theorem original_chain_mono
    {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    (F : O ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : O, ¬ IsMax j →
      SmallObject.relativeCellMaps.{w} d.I (F.map (homOfLE (Order.le_succ j))))
    (s : Cocone F) (hs : IsColimit s) (j : O) : Mono (s.ι.app j) := by
  let _ : MorphismProperty.IsStableUnderTransfiniteComposition.{w} (cofibrations C) := by
    rw [← trivialFibrations_llp]
    infer_instance
  let c : (cofibrations C).TransfiniteCompositionOfShape O (s.ι.app ⊥) :=
    { F := F
      isoBot := Iso.refl _
      incl := s.ι
      isColimit := hs
      map_mem j hj := relativeCellMaps_le_cofibrations d _ (hF j hj) }
  exact h.mono_of_cofibration _ (c.mem_incl_app j)

end HomotopicalAlgebra.CellularLocalizationSmallness

namespace HomotopicalAlgebra.CellularLocalizationSmallness

open CategoryTheory.SmallObject.CellularNormalization

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)
  {W : C} {γ : Cardinal.{w}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unchanged cocone of a chain with supplied original varying I-cell
histories is preserved by an original compact source at its exact bound.
The selected occurrences are bounded in the original outer ordinal. -/
def mappedOriginalHistoriesOfCompact
    (hW : IsCellularCompactAt.{w} d.I W γ)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType] (hγ : γ < μ)
    (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (s : Cocone F) (hs : IsColimit s)
    (K : μ.ord.ToType → Type w)
    [∀ j, LinearOrder (K j)] [∀ j, OrderBot (K j)]
    [∀ j, SuccOrder (K j)] [∀ j, WellFoundedLT (K j)]
    (c : ∀ j, RelativeCellComplex.{w} (fun _ : K j => d.I.homFamily)
      (F.map (homOfLE (Order.le_succ j))))
    (emptySource : Cofan (fun i : PEmpty.{w + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{w + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    IsColimit ((coyoneda.obj (op W)).mapCocone s) := by
  letI : WellFoundedLT (Index K) := lexWellFounded
  letI : SuccOrder (Index K) := flatSuccOrder
  let outer : TransfiniteCompositionOfShape μ.ord.ToType (s.ι.app ⊥) :=
    { F := F
      isoBot := Iso.refl _
      incl := s.ι
      isColimit := hs }
  let D : RelativeCellComplex.{w} (fun _ : Index K => d.I.homFamily) (s.ι.app ⊥) :=
    normalizeRelativeCells (fun _ : μ.ord.ToType => d.I.homFamily) outer c
      emptySource emptyTarget hSource hTarget
  let stage (a : D.Cells) : μ.ord.ToType := (ofLex (Order.succ a.j)).1
  let cells (a : D.Cells) : a.i.1.right ⟶ F.obj (Order.succ (stage a)) :=
    (D.attachCells a.j a.hj).cell a.k ≫
      (c (stage a)).incl.app (ofLex (Order.succ a.j)).2
  have hcells (a : D.Cells) : cells a ≫ s.ι.app (Order.succ (stage a)) = a.ι := by
    change (((D.attachCells a.j a.hj).cell a.k) ≫
      (c (stage a)).incl.app (ofLex (Order.succ a.j)).2) ≫
        s.ι.app (Order.succ (stage a)) =
      (D.attachCells a.j a.hj).cell a.k ≫
        ((c (stage a)).incl.app (ofLex (Order.succ a.j)).2 ≫
          s.ι.app (Order.succ (stage a)))
    exact Category.assoc _ _ _
  have hF (j : μ.ord.ToType) (_ : ¬ IsMax j) :
      SmallObject.relativeCellMaps.{w} d.I (F.map (homOfLE (Order.le_succ j))) :=
    SmallObject.relativeCellComplex_mem_relativeCellMaps d.I (c j)
  have hmono (j : μ.ord.ToType) : Mono (s.ι.app j) :=
    original_chain_mono h F hF s hs j
  refine Types.FilteredColimit.isColimitOf' _ _ (fun g => ?_) ?_
  · obtain ⟨e, k, hk⟩ := hW.exists_stage_of_cell_history μ hγ F s D
      (𝟙 (F.obj ⊥)) (Category.id_comp _) (fun a => Order.succ (stage a))
      cells hcells hmono g
    exact ⟨e, k, hk.symm⟩
  · intro j f g hfg
    let _ : Mono (s.ι.app j) := hmono j
    change f ≫ s.ι.app j = g ≫ s.ι.app j at hfg
    have heq : f = g := (cancel_mono (s.ι.app j)).1 hfg
    exact ⟨j, 𝟙 j, by rw [heq]⟩

include h in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Compactness alone supplies source-Hom preservation on every original
continuous relative-I chain at every regular cardinal larger than its bound. -/
theorem preserves_original_chain_of_compact
    (hW : IsCellularCompactAt.{w} d.I W γ)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType] (hγ : γ < μ)
    (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : μ.ord.ToType, ¬ IsMax j →
      SmallObject.relativeCellMaps.{w} d.I (F.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit F (coyoneda.obj (op W)) where
  preserves {s} hs := ⟨by
    classical
    let : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
    let : NoMaxOrder μ.ord.ToType := Cardinal.noMaxOrder (Fact.out : μ.IsRegular).aleph0_le
    have hHistories : ∀ j : μ.ord.ToType, ∃ S : OriginalInnerShape.{w},
        Nonempty (RelativeCellComplex.{w} (fun _ : S.carrier => d.I.homFamily)
          (F.map (homOfLE (Order.le_succ j)))) := by
      intro j
      obtain ⟨T, hlin, hsucc, hbot, hwf, ht⟩ :=
        (transfiniteCompositions_iff (coproducts.{w} d.I).pushouts _).mp
          (hF j (not_isMax j))
      let S : OriginalInnerShape.{w} :=
        { carrier := T
          linearOrder := hlin
          orderBot := hbot
          succOrder := hsucc
          wellFounded := hwf }
      let tc := Classical.choice ht
      refine ⟨S, ⟨{
        toTransfiniteCompositionOfShape := tc.toTransfiniteCompositionOfShape
        attachCells := fun a ha => ?_ }⟩⟩
      apply Classical.choice
      apply (nonempty_attachCells_iff d.I.homFamily _).mpr
      simpa only [ofHoms_homFamily] using tc.map_mem a ha
    choose K hK using hHistories
    let c := fun j => Classical.choice (hK j)
    let empty : Cofan (fun i : PEmpty.{w + 1} => (i.elim : C)) :=
      colimit.cocone (Discrete.functor (fun i : PEmpty.{w + 1} => (i.elim : C)))
    exact mappedOriginalHistoriesOfCompact h hW μ hγ F s hs
      (fun j => (K j).carrier) c empty empty
      (colimit.isColimit _) (colimit.isColimit _)⟩

include h in
/-- Hirschhorn's compactness-to-smallness comparison, with its exact original
bound: regular μ strictly above γ gives the original source-Hom colimit. -/
theorem uniformly_small_of_compactAt (hW : IsCellularCompactAt.{w} d.I W γ) :
    IsUniformlySmallRelativeTo.{w} d.I W := by
  refine ⟨γ, ?_⟩
  intro μ _ _ hμ F _ hF
  exact preserves_original_chain_of_compact h hW μ hμ F hF

include h in
/-- Every original compact object has genuine uniform relative-I smallness. -/
theorem uniformly_small_of_compact (hW : IsCellularCompact.{w} d.I W) :
    IsUniformlySmallRelativeTo.{w} d.I W :=
  uniformly_small_of_compactAt h hW.choose_spec

end HomotopicalAlgebra.CellularLocalizationSmallness

open CategoryTheory.SmallObject

namespace HomotopicalAlgebra.CellularCofibrationTransport

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

local instance : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject

/-- The original I right class determines the actual original cofibrations. -/
theorem originalLeftClass : d.I.rlp.llp = cofibrations C := by
  rw [d.I_rlp, trivialFibrations_llp]

section OriginalFactory

variable {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f)

/-- The specified original I factory is the actual cellular representative. -/
def originalFactoryCellMap : X ⟶ SmallObject.obj d.I κ f := by
  letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  exact SmallObject.ιObj d.I κ f

include hf in
/-- The original cofibration lifting property splits its original I factorization. -/
def originalFactoryRetract : RetractArrow f (originalFactoryCellMap d f) := by
  letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  have hleft : d.I.rlp.llp f := by
    rw [originalLeftClass d]
    exact hf
  have sq : CommSq (SmallObject.ιObj d.I κ f) f (SmallObject.πObj d.I κ f) (𝟙 Y) :=
    ⟨by simp⟩
  have := hleft _ (SmallObject.rlp_πObj d.I κ f)
  exact
    { i := Arrow.homMk (𝟙 X) sq.lift (by
        change 𝟙 X ≫ SmallObject.ιObj d.I κ f = f ≫ sq.lift
        rw [Category.id_comp]
        exact sq.fac_left.symm)
      r := Arrow.homMk (𝟙 X) (SmallObject.πObj d.I κ f) (by
        change 𝟙 X ≫ f = SmallObject.ιObj d.I κ f ≫ SmallObject.πObj d.I κ f
        rw [Category.id_comp, SmallObject.ιObj_πObj])
      retract := by
        ext
        · exact Category.id_comp _
        · exact sq.fac_right }

/-- That same factory arrow retains its actual original I-cell presentation. -/
theorem originalFactoryCellMap_mem :
    SmallObject.relativeCellMaps.{w} d.I (originalFactoryCellMap d f) := by
  let _ : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  exact SmallObject.relativeCellComplex_mem_relativeCellMaps d.I
    (SmallObject.relativeCellComplexιObj d.I κ f)

end OriginalFactory

section OriginalChain

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  (F : J ⥤ C) [F.IsWellOrderContinuous]
  (hF : ∀ j : J, ¬ IsMax j → cofibrations C (F.map (homOfLE (Order.le_succ j))))

include hF in
/-- The entire section is constructed from original factory representatives and lifts. -/
def originalSection :
    (CoherentRetracts.prefixSplitFunctor (SmallObject.relativeCellMaps.{w} d.I) F).sections := by
  letI : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact CoherentRetracts.ChosenStages.chosenSection
    (SmallObject.relativeCellMaps.{w} d.I) F
    (fun a : {j : J // ¬ IsMax j} =>
      originalFactoryCellMap d (F.map (homOfLE (Order.le_succ a.1))))
    (fun a => originalFactoryRetract d _ (hF a.1 a.2))
    (fun a => originalFactoryCellMap_mem d _)

/-- The constructed original splitting diagram has exactly the caller's whole order. -/
def originalSplitDiagram : J ⥤ CoherentRetracts.SplitObject C :=
  CoherentRetracts.PrefixSplitGlue.wholeDiagram
    (SmallObject.relativeCellMaps.{w} d.I) F (originalSection d F hF)

/-- The actual cellular replacement remains on the same caller's well order. -/
def originalTargetDiagram : J ⥤ C :=
  originalSplitDiagram d F hF ⋙ CoherentRetracts.SplitObject.targetFunctor

/-- Its source projection retains every original point and original map. -/
theorem originalSourceDiagram :
    originalSplitDiagram d F hF ⋙ CoherentRetracts.SplitObject.sourceFunctor = F :=
  CoherentRetracts.PrefixSplitGlue.wholeDiagram_source
    (SmallObject.relativeCellMaps.{w} d.I) F (originalSection d F hF)

/-- The actual generated cellular chain is continuous at each original limit. -/
theorem originalTargetContinuous : (originalTargetDiagram d F hF).IsWellOrderContinuous where
  nonempty_isColimit := CoherentRetracts.PrefixSplitGlue.wholeDiagram_continuous
    (SmallObject.relativeCellMaps.{w} d.I) F (originalSection d F hF)

/-- Each original auxiliary successor is a genuine cobase change of an original I history. -/
theorem originalTargetSuccessor (j : J) (hj : ¬ IsMax j) :
    SmallObject.relativeCellMaps.{w} d.I
      ((originalTargetDiagram d F hF).map (homOfLE (Order.le_succ j))) := by
  let _ : (SmallObject.relativeCellMaps.{w} d.I).IsStableUnderCobaseChange :=
    CellularRetractsClosure.cellularIsStableUnderCobaseChange d.I
  exact MorphismProperty.pushouts_le (P := SmallObject.relativeCellMaps.{w} d.I) _
    (CoherentRetracts.PrefixSplitGlue.wholeDiagram_map_mem
      (SmallObject.relativeCellMaps.{w} d.I) F (originalSection d F hF) j hj)

/-- Every original stage inclusion is the actual constructed splitting component. -/
def originalInclusion : F ⟶ originalTargetDiagram d F hF :=
  eqToHom (originalSourceDiagram d F hF).symm ≫
    CoherentRetracts.SplitObject.inclusionNatTrans (originalSplitDiagram d F hF)

/-- Every original stage retraction is the actual constructed splitting component. -/
def originalRetraction : originalTargetDiagram d F hF ⟶ F :=
  CoherentRetracts.SplitObject.retractionNatTrans (originalSplitDiagram d F hF) ≫
    eqToHom (originalSourceDiagram d F hF)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed full maps split the original chain pointwise and naturally. -/
theorem originalSplitting : originalInclusion d F hF ≫ originalRetraction d F hF = 𝟙 F := by
  apply NatTrans.ext
  funext j
  simp only [originalInclusion, originalRetraction, NatTrans.comp_app,
    NatTrans.id_app, eqToHom_app,
    CoherentRetracts.SplitObject.inclusionNatTrans,
    CoherentRetracts.SplitObject.retractionNatTrans]
  rw [Category.assoc, ← Category.assoc (originalSplitDiagram d F hF |>.obj j).inclusion,
    (originalSplitDiagram d F hF |>.obj j).splitting, Category.id_comp,
    eqToHom_trans, eqToHom_refl]

end OriginalChain

section SourceHomSplitting

variable {J : Type w} [Category.{w} J] [IsFiltered J]
  {F G : J ⥤ C} {W : C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Two actual original colimit cocones transfer source Hom along a natural splitting. -/
def mappedCoconeOfSplitting (c : Cocone F) (cG : Cocone G)
    (hc : IsColimit c) (hcG : IsColimit cG)
    (i : F ⟶ G) (r : G ⟶ F) (hir : i ≫ r = 𝟙 F)
    [PreservesColimit G (coyoneda.obj (op W))] :
    IsColimit ((coyoneda.obj (op W)).mapCocone c) := by
  let R := CoherentRetracts.retractOfColimitCocones c cG hc hcG i r hir
  have hsplit (a : J) : i.app a ≫ r.app a = 𝟙 (F.obj a) :=
    NatTrans.congr_app hir a
  refine Types.FilteredColimit.isColimitOf _ _ (fun f => ?_) ?_
  · obtain ⟨a, g, hg⟩ := exists_hom_of_preservesColimit_coyoneda hcG (f ≫ R.i)
    refine ⟨a, g ≫ r.app a, ?_⟩
    change f = (g ≫ r.app a) ≫ c.ι.app a
    symm
    calc
      (g ≫ r.app a) ≫ c.ι.app a = g ≫ (r.app a ≫ c.ι.app a) := Category.assoc _ _ _
      _ = g ≫ (cG.ι.app a ≫ R.r) :=
        congrArg (fun z => g ≫ z) (hcG.ι_map c r a).symm
      _ = (g ≫ cG.ι.app a) ≫ R.r := (Category.assoc _ _ _).symm
      _ = (f ≫ R.i) ≫ R.r := congrArg (fun z => z ≫ R.r) hg
      _ = f := by rw [Category.assoc, R.retract, Category.comp_id]
  · intro a b f g hfg
    change f ≫ c.ι.app a = g ≫ c.ι.app b at hfg
    have hi : (f ≫ i.app a) ≫ cG.ι.app a = (g ≫ i.app b) ≫ cG.ι.app b := by
      calc
        (f ≫ i.app a) ≫ cG.ι.app a = f ≫ (i.app a ≫ cG.ι.app a) :=
          Category.assoc _ _ _
        _ = f ≫ (c.ι.app a ≫ R.i) :=
          congrArg (fun z => f ≫ z) (hc.ι_map cG i a).symm
        _ = (f ≫ c.ι.app a) ≫ R.i := (Category.assoc _ _ _).symm
        _ = (g ≫ c.ι.app b) ≫ R.i := congrArg (fun z => z ≫ R.i) hfg
        _ = g ≫ (c.ι.app b ≫ R.i) := Category.assoc _ _ _
        _ = g ≫ (i.app b ≫ cG.ι.app b) :=
          congrArg (fun z => g ≫ z) (hc.ι_map cG i b)
        _ = (g ≫ i.app b) ≫ cG.ι.app b := (Category.assoc _ _ _).symm
    obtain ⟨e, s, t, heq⟩ := exists_eq_of_preservesColimit_coyoneda hcG
      (f ≫ i.app a) (g ≫ i.app b) hi
    have cancelStage {a e : J} (m : W ⟶ F.obj a) (s : a ⟶ e) :
        ((m ≫ i.app a) ≫ G.map s) ≫ r.app e = m ≫ F.map s := by
      rw [Category.assoc, Category.assoc, r.naturality s,
        ← Category.assoc (i.app a), hsplit a, Category.id_comp]
    refine ⟨e, s, t, ?_⟩
    exact (cancelStage f s).symm.trans
      ((congrArg (fun z => z ≫ r.app e) heq).trans (cancelStage g t))

end SourceHomSplitting

section UniformSource

variable {W : C} (hW : IsUniformlySmallRelativeTo.{w} d.I W)

/-- The selected bound belongs to the unchanged original source object. -/
def originalSourceBound : Cardinal.{w} := hW.choose

variable (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
  (hμ : originalSourceBound d hW < μ)
  (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
  (hF : ∀ a : μ.ord.ToType, ¬ IsMax a →
    cofibrations C (F.map (homOfLE (Order.le_succ a))))

/-- The actual caller's cocone remains colimiting after its original source Hom. -/
def mappedOriginalCofibrationCocone (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (op W)).mapCocone c) := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  let G := originalTargetDiagram d F hF
  let _ : G.IsWellOrderContinuous := originalTargetContinuous d F hF
  let _ : PreservesColimit G (coyoneda.obj (op W)) :=
    hW.choose_spec μ hμ G (originalTargetSuccessor d F hF)
  exact mappedCoconeOfSplitting c (colimit.cocone G) hc (colimit.isColimit G)
    (originalInclusion d F hF) (originalRetraction d F hF) (originalSplitting d F hF)

include d hW hμ hF

/-- Source Hom preserves the complete original caller's cofibration chain. -/
theorem preservesOriginalCofibrationChain : PreservesColimit F (coyoneda.obj (op W)) where
  preserves := fun {c} hc => ⟨mappedOriginalCofibrationCocone d hW μ hμ F hF c hc⟩

/-- Every original source map factors through a stage of the exact original cocone. -/
theorem existsOriginalCofibrationStage (c : Cocone F) (hc : IsColimit c) (f : W ⟶ c.pt) :
    ∃ (a : μ.ord.ToType) (g : W ⟶ F.obj a), g ≫ c.ι.app a = f := by
  let _ : PreservesColimit F (coyoneda.obj (op W)) :=
    preservesOriginalCofibrationChain d hW μ hμ F hF
  exact exists_hom_of_preservesColimit_coyoneda hc f

/-- Endpoint equality is witnessed at an actual original common later cofibration stage. -/
theorem existsOriginalCofibrationStageEquality (c : Cocone F) (hc : IsColimit c)
    {a b : μ.ord.ToType} (f : W ⟶ F.obj a) (g : W ⟶ F.obj b)
    (hfg : f ≫ c.ι.app a = g ≫ c.ι.app b) :
    ∃ (e : μ.ord.ToType) (s : a ⟶ e) (t : b ⟶ e), f ≫ F.map s = g ≫ F.map t := by
  let _ : PreservesColimit F (coyoneda.obj (op W)) :=
    preservesOriginalCofibrationChain d hW μ hμ F hF
  exact exists_eq_of_preservesColimit_coyoneda hc f g hfg

end UniformSource

section UniformConclusion

variable {W : C} (hW : IsUniformlySmallRelativeTo.{w} d.I W)

include d hW in
/-- The original relative-I bound is a uniform bound on all original cofibration chains. -/
theorem uniformOriginalCofibrationChains :
    ∃ β : Cardinal.{w},
      ∀ (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType], β < μ →
        ∀ (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous],
          (∀ a : μ.ord.ToType, ¬ IsMax a →
            cofibrations C (F.map (homOfLE (Order.le_succ a)))) →
          PreservesColimit F (coyoneda.obj (op W)) := by
  refine ⟨originalSourceBound d hW, ?_⟩
  intro μ _ _ hμ F _ hF
  exact preservesOriginalCofibrationChain d hW μ hμ F hF

end UniformConclusion

end HomotopicalAlgebra.CellularCofibrationTransport

namespace HomotopicalAlgebra.IsUniformlySmallRelativeTo

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  {A B : C}

/-- Retracts keep the original uniform relative-cell source bound and the
actual source-Hom cocones. -/
theorem of_retract (h : IsUniformlySmallRelativeTo.{w} P A) (R : Retract B A) :
    IsUniformlySmallRelativeTo.{w} P B := by
  refine ⟨h.choose, ?_⟩
  intro μ _ _ hμ F _ hF
  let _ : PreservesColimit F (coyoneda.obj (op A)) := h.choose_spec μ hμ F hF
  exact preservesColimit_of_retract (R.op.map coyoneda)

end HomotopicalAlgebra.IsUniformlySmallRelativeTo

namespace HomotopicalAlgebra.CellularLocalizationSmallness

section Initial

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C) {X : C}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual initial object is uniformly small on every original nonempty
relative-cell chain, with no source or generator hypothesis. -/
theorem initial_uniformly_small (hX : IsInitial X) :
    IsUniformlySmallRelativeTo.{w} P X := by
  refine ⟨0, ?_⟩
  intro μ _ _ _ F _ _
  refine ⟨fun {s} _ => ⟨?_⟩⟩
  refine Types.FilteredColimit.isColimitOf' _ _ (fun f => ?_) ?_
  · exact ⟨⊥, hX.to (F.obj ⊥), hX.hom_ext _ _⟩
  · intro j f g _
    refine ⟨j, 𝟙 j, ?_⟩
    exact hX.hom_ext _ _

end Initial

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)
  {W : C} {γ : Cardinal.{w}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Compactness at γ preserves the caller's original cofibration cocone
whenever γ < μ; the original I factory supplies the whole splitting. -/
def mappedOriginalCofibrationCoconeOfCompact
    (hW : IsCellularCompactAt.{w} d.I W γ)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType] (hγ : γ < μ)
    (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : μ.ord.ToType, ¬ IsMax j →
      cofibrations C (F.map (homOfLE (Order.le_succ j))))
    (s : Cocone F) (hs : IsColimit s) :
    IsColimit ((coyoneda.obj (op W)).mapCocone s) := by
  letI : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  let G := CellularCofibrationTransport.originalTargetDiagram d F hF
  letI : G.IsWellOrderContinuous := CellularCofibrationTransport.originalTargetContinuous d F hF
  letI : PreservesColimit G (coyoneda.obj (op W)) :=
    preserves_original_chain_of_compact h hW μ hγ G
      (CellularCofibrationTransport.originalTargetSuccessor d F hF)
  exact CellularCofibrationTransport.mappedCoconeOfSplitting s (colimit.cocone G)
    hs (colimit.isColimit G)
    (CellularCofibrationTransport.originalInclusion d F hF)
    (CellularCofibrationTransport.originalRetraction d F hF)
    (CellularCofibrationTransport.originalSplitting d F hF)

include h in
/-- The exact compactness rank controls all original cofibration chains. -/
theorem preserves_original_cofibration_chain_of_compact
    (hW : IsCellularCompactAt.{w} d.I W γ)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType] (hγ : γ < μ)
    (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : μ.ord.ToType, ¬ IsMax j →
      cofibrations C (F.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit F (coyoneda.obj (op W)) where
  preserves := fun {s} hs =>
    ⟨mappedOriginalCofibrationCoconeOfCompact h hW μ hγ F hF s hs⟩

include h in
/-- All regular ordinals strictly above γ use the original compact source,
the original cofibrations, and their original whole source-Hom comparison. -/
theorem uniform_cofibration_chains_of_compactAt
    (hW : IsCellularCompactAt.{w} d.I W γ) :
    ∃ β : Cardinal.{w},
      ∀ (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType], β < μ →
        ∀ (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous],
          (∀ j : μ.ord.ToType, ¬ IsMax j →
            cofibrations C (F.map (homOfLE (Order.le_succ j)))) →
          PreservesColimit F (coyoneda.obj (op W)) := by
  refine ⟨γ, ?_⟩
  intro μ _ _ hμ F _ hF
  exact preserves_original_cofibration_chain_of_compact h hW μ hμ F hF

include h in
/-- All original cofibration cocone inclusions are monic, at their actual
unchanged endpoints. -/
theorem cofibration_chain_mono
    {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    (F : O ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : O, ¬ IsMax j → cofibrations C (F.map (homOfLE (Order.le_succ j))))
    (s : Cocone F) (hs : IsColimit s) (j : O) : Mono (s.ι.app j) := by
  let _ : MorphismProperty.IsStableUnderTransfiniteComposition.{w} (cofibrations C) := by
    rw [← trivialFibrations_llp]
    infer_instance
  let c : (cofibrations C).TransfiniteCompositionOfShape O (s.ι.app ⊥) :=
    { F := F
      isoBot := Iso.refl _
      incl := s.ι
      isColimit := hs
      map_mem := hF }
  exact h.mono_of_cofibration _ (c.mem_incl_app j)

section CellEndpoint

variable {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (hX : IsUniformlySmallRelativeTo.{w} d.I X)
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)

/-- The actual root smallness, original cell size and actual cell cardinal
give one bound for this original presented relative I-cell endpoint. -/
def cellEndpointSourceBound : Cardinal.{w} :=
  max (CellularCofibrationTransport.originalSourceBound d hX)
    (max (commonCompactBound h) (Cardinal.mk c.Cells))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An original I-cell endpoint with an I-small root preserves the exact
original cofibration cocone above its source-and-cell bound. -/
def mappedCellEndpointCofibrationCocone
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : cellEndpointSourceBound h hX c < μ)
    (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : μ.ord.ToType, ¬ IsMax j →
      cofibrations C (F.map (homOfLE (Order.le_succ j))))
    (s : Cocone F) (hs : IsColimit s) :
    IsColimit ((coyoneda.obj (op Y)).mapCocone s) := by
  have hβ : CellularCofibrationTransport.originalSourceBound d hX < μ :=
    (le_max_left _ _).trans_lt hμ
  have hγ : commonCompactBound h < μ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hμ
  have hτ : Cardinal.mk c.Cells < μ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hμ
  letI : PreservesColimit F (coyoneda.obj (op X)) :=
    CellularCofibrationTransport.preservesOriginalCofibrationChain d hX μ hβ F hF
  refine Types.FilteredColimit.isColimitOf' _ _ (fun g => ?_) ?_
  · obtain ⟨j₀, r, hr⟩ := exists_hom_of_preservesColimit_coyoneda hs (f ≫ g)
    have hCells : ∀ a : c.Cells, ∃ (j : μ.ord.ToType) (b : a.i.1.right ⟶ F.obj j),
        b ≫ s.ι.app j = a.ι ≫ g := by
      intro a
      let _ : PreservesColimit F (coyoneda.obj (op a.i.1.right)) :=
        preserves_original_cofibration_chain_of_compact h (codomain_compact h a.i) μ hγ F hF
      exact exists_hom_of_preservesColimit_coyoneda hs (a.ι ≫ g)
    choose stage cells hcells using hCells
    obtain ⟨e, he⟩ := exists_regular_stage_bound μ stage hτ
    let k := max e j₀
    let _ : Mono (s.ι.app k) := cofibration_chain_mono h F hF s hs k
    let root : X ⟶ F.obj k := r ≫ F.map (homOfLE (le_max_right e j₀))
    have hroot : root ≫ s.ι.app k = f ≫ g := by
      dsimp only [root]
      rw [Category.assoc, s.w, hr]
    let b (a : c.Cells) : a.i.1.right ⟶ F.obj k :=
      cells a ≫ F.map (homOfLE ((he a).trans (le_max_left e j₀)))
    have hb (a : c.Cells) : b a ≫ s.ι.app k = a.ι ≫ g := by
      dsimp only [b]
      rw [Category.assoc, s.w, hcells]
    obtain ⟨m, hm⟩ := c.exists_lift_through_mono g (s.ι.app k) root hroot b hb
    exact ⟨k, m, hm.symm⟩
  · intro j g g' hgg'
    let _ : Mono (s.ι.app j) := cofibration_chain_mono h F hF s hs j
    change g ≫ s.ι.app j = g' ≫ s.ι.app j at hgg'
    have heq : g = g' := (cancel_mono (s.ι.app j)).1 hgg'
    exact ⟨j, 𝟙 j, by rw [heq]⟩

include h hX c in
/-- The root's original smallness and the actual original cell count
control source Hom on every original cofibration chain. -/
theorem cell_endpoint_preserves_cofibration_chain
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : cellEndpointSourceBound h hX c < μ)
    (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : μ.ord.ToType, ¬ IsMax j →
      cofibrations C (F.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit F (coyoneda.obj (op Y)) where
  preserves := fun {s} hs => ⟨mappedCellEndpointCofibrationCocone h hX c μ hμ F hF s hs⟩

include h hX c in
/-- A presented original I-cell complex over an I-small root is genuinely
uniformly I-small at the bound computed from that exact root and history. -/
theorem cell_endpoint_uniformly_small : IsUniformlySmallRelativeTo.{w} d.I Y := by
  refine ⟨cellEndpointSourceBound h hX c, ?_⟩
  intro μ _ _ hμ F _ hF
  exact cell_endpoint_preserves_cofibration_chain h hX c μ hμ F
    (fun j hj => relativeCellMaps_le_cofibrations d _ (hF j hj))

end CellEndpoint

section CofibrationCodomain

local instance : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject

include h in
/-- The codomain of any original cofibration with an I-small source is
I-small, using the actual I factorization and its actual arrow retract. -/
theorem cofibration_codomain_uniformly_small {X Y : C} (f : X ⟶ Y)
    (hf : cofibrations C f) (hX : IsUniformlySmallRelativeTo.{w} d.I X) :
    IsUniformlySmallRelativeTo.{w} d.I Y := by
  have hZ := cell_endpoint_uniformly_small h hX (SmallObject.relativeCellComplexιObj d.I κ f)
  exact hZ.of_retract (CellularCofibrationTransport.originalFactoryRetract d f hf).right

include h in
/-- Every original cofibrant object is uniformly small relative to the
original I family, via its original I-cell replacement and object retract. -/
theorem cofibrant_uniformly_small (W : C) [IsCofibrant W] :
    IsUniformlySmallRelativeTo.{w} d.I W :=
  cofibration_codomain_uniformly_small h (initial.to W) (mem_cofibrations _)
    (initial_uniformly_small d.I initialIsInitial)

include h in
/-- Every original cofibrant object is uniformly small on all actual
original cofibration chains, with their full source-Hom comparison. -/
theorem cofibrant_uniform_cofibration_chains (W : C) [IsCofibrant W] :
    ∃ β : Cardinal.{w},
      ∀ (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType], β < μ →
        ∀ (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous],
          (∀ j : μ.ord.ToType, ¬ IsMax j →
            cofibrations C (F.map (homOfLE (Order.le_succ j)))) →
          PreservesColimit F (coyoneda.obj (op W)) :=
  CellularCofibrationTransport.uniformOriginalCofibrationChains d (cofibrant_uniformly_small h W)

include h in
/-- Both original J endpoints are I-small; the original domain is used
with its given smallness, without a compactness or cofibrancy assumption. -/
theorem J_codomain_uniformly_small (j : d.J.toSet) :
    IsUniformlySmallRelativeTo.{w} d.I j.1.right := by
  have hJ : d.J ≤ cofibrations C := by
    have heq : d.J.rlp.llp = trivialCofibrations C := by
      rw [d.J_rlp, fibrations_llp]
    exact d.J.le_llp_rlp.trans (heq ▸ trivialCofibrations_sub_cofibrations C)
  exact cofibration_codomain_uniformly_small h j.1.hom (hJ _ j.2) (h.J_domains_small j)

end CofibrationCodomain

section OriginalJ

local instance : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject

/-- Relative original J histories are original trivial cofibrations, hence
original cofibrations at the same endpoints. -/
theorem relative_J_maps_le_cofibrations :
    SmallObject.relativeCellMaps.{w} d.J ≤ cofibrations C := by
  have heq : d.J.rlp.llp = trivialCofibrations C := by
    rw [d.J_rlp, fibrations_llp]
  exact d.J.transfiniteCompositions_pushouts_coproducts_le_llp_rlp.trans
    (heq ▸ trivialCofibrations_sub_cofibrations C)

/-- Every unchanged original J arrow is an original cofibration. -/
theorem original_J_cofibration (j : d.J.toSet) : cofibrations C j.1.hom := by
  have heq : d.J.rlp.llp = trivialCofibrations C := by
    rw [d.J_rlp, fibrations_llp]
  exact (trivialCofibrations_sub_cofibrations C) _
    (heq ▸ d.J.le_llp_rlp _ j.2)

/-- The original J-domain bound controls the actual original cofibration
cocone; it is the given smallness bound of that actual J source. -/
def mappedJDomainCofibrationCocone (j : d.J.toSet)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : commonSmallBound h < μ)
    (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ a : μ.ord.ToType, ¬ IsMax a →
      cofibrations C (F.map (homOfLE (Order.le_succ a))))
    (s : Cocone F) (hs : IsColimit s) :
    IsColimit ((coyoneda.obj (op j.1.left)).mapCocone s) :=
  CellularCofibrationTransport.mappedOriginalCofibrationCocone d (h.J_domains_small j)
    μ ((smallBound_le_common h j).trans_lt hμ) F hF s hs

/-- The actual I factory history on the original J arrow gives the
codomain bound, using the original noncofibrant J source's given smallness. -/
def jCodomainSourceBound (j : d.J.toSet) : Cardinal.{w} :=
  cellEndpointSourceBound h (h.J_domains_small j)
    (SmallObject.relativeCellComplexιObj d.I κ j.1.hom)

/-- The actual original J codomain preserves the exact original cofibration
cocone above the bound of its original I factory history. -/
def mappedJCodomainCofibrationCocone (j : d.J.toSet)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : jCodomainSourceBound h j < μ)
    (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ a : μ.ord.ToType, ¬ IsMax a →
      cofibrations C (F.map (homOfLE (Order.le_succ a))))
    (s : Cocone F) (hs : IsColimit s) :
    IsColimit ((coyoneda.obj (op j.1.right)).mapCocone s) := by
  letI : PreservesColimit F (coyoneda.obj (op (SmallObject.obj d.I κ j.1.hom))) :=
    cell_endpoint_preserves_cofibration_chain h (h.J_domains_small j)
      (SmallObject.relativeCellComplexιObj d.I κ j.1.hom) μ hμ F hF
  let R := (CellularCofibrationTransport.originalFactoryRetract d j.1.hom
    (original_J_cofibration j)).right
  letI : PreservesColimit F (coyoneda.obj (op j.1.right)) :=
    preservesColimit_of_retract (R.op.map coyoneda)
  exact isColimitOfPreserves (coyoneda.obj (op j.1.right)) hs

include h in
/-- Original J domains retain genuine uniform smallness relative to J,
derived from their original I-smallness and all-cofibration transport. -/
theorem J_domain_uniformly_small_relative_J (j : d.J.toSet) :
    IsUniformlySmallRelativeTo.{w} d.J j.1.left := by
  refine ⟨smallBound h j, ?_⟩
  intro μ _ _ hμ F _ hF
  exact CellularCofibrationTransport.preservesOriginalCofibrationChain d (h.J_domains_small j)
    μ hμ F (fun a ha => relative_J_maps_le_cofibrations _ (hF a ha))

include h in
/-- Original J codomains are uniformly J-small at the bound computed from
their actual original I-cell factory history and its actual retract. -/
theorem J_codomain_uniformly_small_relative_J (j : d.J.toSet) :
    IsUniformlySmallRelativeTo.{w} d.J j.1.right := by
  refine ⟨jCodomainSourceBound h j, ?_⟩
  intro μ _ _ hμ F _ hF
  exact
    { preserves := fun {s} hs =>
        ⟨mappedJCodomainCofibrationCocone h j μ hμ F
          (fun a ha => relative_J_maps_le_cofibrations _ (hF a ha)) s hs⟩ }

end OriginalJ

end HomotopicalAlgebra.CellularLocalizationSmallness

universe vD

namespace HomotopicalAlgebra.CellularLocalizationSmallness

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)

include h in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The exact original colimit of compact objects is compact, with bound
the sum of the actual original component bounds. -/
theorem colimit_compactAt_bounds {D : Type w} [Category.{vD} D]
    (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s) (γ : D → Cardinal.{w})
    (hF : ∀ i : D, IsCellularCompactAt.{w} d.I (F.obj i) (γ i)) :
    IsCellularCompactAt.{w} d.I s.pt (Cardinal.sum γ) := by
  intro O _ _ _ _ X Y f c g
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  have ht : ∀ i : D, ∃ t : CellularSubcomplex c,
      Cardinal.mk t.complex.Cells ≤ γ i ∧ ∃ k : F.obj i ⟶ t.endpoint,
        k ≫ t.inclusion = s.ι.app i ≫ g := fun i => hF i O X Y f c (s.ι.app i ≫ g)
  choose t ht k hk using ht
  let U := CellularUnion.unionSubcomplex t h
  let _ : Mono U.inclusion := h.mono_of_cofibration _
    (CellularSubcomplexExtension.inclusionCofibration d c h U)
  let m (i : D) : F.obj i ⟶ U.endpoint := k i ≫ CellularUnion.inclusion t i none
  have hm (i : D) : m i ≫ U.inclusion = s.ι.app i ≫ g := by
    dsimp only [m, U]
    rw [Category.assoc, CellularUnion.inclusion_comparison, hk]
  let z : Cocone F :=
    { pt := U.endpoint
      ι :=
        { app := m
          naturality i j a := by
            change F.map a ≫ m j = m i ≫ 𝟙 U.endpoint
            rw [Category.comp_id]
            apply (cancel_mono U.inclusion).1
            simp only [Category.assoc, hm]
            rw [← Category.assoc, s.w] } }
  let q := hs.desc z
  have hq : q ≫ U.inclusion = g := by
    apply hs.hom_ext
    intro i
    rw [← Category.assoc, hs.fac]
    exact hm i
  have hU : Cardinal.mk U.complex.Cells ≤ Cardinal.sum γ :=
    (CellularUnion.union_cells_cardinal_le t h).trans (Cardinal.sum_le_sum _ _ ht)
  exact ⟨U, hU, q, hq⟩

include h in
/-- Small colimits preserve genuine relative-I compactness, using actual
original cocones and original component compactness witnesses. -/
theorem colimit_compact {D : Type w} [Category.{vD} D]
    (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s)
    (hF : ∀ i : D, IsCellularCompact.{w} d.I (F.obj i)) :
    IsCellularCompact.{w} d.I s.pt :=
  ⟨_, colimit_compactAt_bounds h F s hs (fun i => (hF i).choose)
    (fun i => (hF i).choose_spec)⟩

include h in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An actual original I-cell complex on an initial root is compact at
the common original cell bound times its actual original cell count. -/
theorem cell_complex_compactAt
    {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y} (hX : IsInitial X)
    (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f) :
    IsCellularCompactAt.{w} d.I Y (commonCompactBound h * Cardinal.mk c.Cells) := by
  intro T _ _ _ _ A B g q k
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  have ht : ∀ a : c.Cells, ∃ t : CellularSubcomplex q,
      Cardinal.mk t.complex.Cells ≤ commonCompactBound h ∧
        ∃ z : a.i.1.right ⟶ t.endpoint, z ≫ t.inclusion = a.ι ≫ k :=
    fun a => codomain_compact h a.i T A B g q (a.ι ≫ k)
  choose t ht z hz using ht
  let U := CellularUnion.unionSubcomplex t h
  let _ : Mono U.inclusion := h.mono_of_cofibration _
    (CellularSubcomplexExtension.inclusionCofibration d q h U)
  let r : X ⟶ U.endpoint := hX.to _
  have hr : r ≫ U.inclusion = f ≫ k := hX.hom_ext _ _
  let cells (a : c.Cells) : a.i.1.right ⟶ U.endpoint :=
    z a ≫ CellularUnion.inclusion t a none
  have hc (a : c.Cells) : cells a ≫ U.inclusion = a.ι ≫ k := by
    dsimp only [cells, U]
    rw [Category.assoc, CellularUnion.inclusion_comparison, hz]
  obtain ⟨m, hm⟩ := c.exists_lift_through_mono k U.inclusion r hr cells hc
  have hU : Cardinal.mk U.complex.Cells ≤ commonCompactBound h * Cardinal.mk c.Cells := by
    have he := (CellularUnion.union_cells_cardinal_le t h).trans (Cardinal.sum_le_sum _ _ ht)
    simpa only [U, Cardinal.sum_const', mul_comm] using he
  exact ⟨U, hU, m, hm⟩

include h in
/-- Every actual original cell complex has genuine relative-I compactness
from the original cell data and unchanged presented history. -/
theorem cell_complex_compact
    {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y} (hX : IsInitial X)
    (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f) :
    IsCellularCompact.{w} d.I Y := ⟨_, cell_complex_compactAt h hX c⟩

local instance : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject

include h in
/-- Every original cofibrant object is compact, using its actual original
I factory cell history and the object retract supplied by original lifting. -/
theorem cofibrant_compact (Y : C) [IsCofibrant Y] : IsCellularCompact.{w} d.I Y := by
  have hc := cell_complex_compactAt h initialIsInitial
    (SmallObject.relativeCellComplexιObj d.I κ (initial.to Y))
  let R := (CellularCofibrationTransport.originalFactoryRetract d (initial.to Y)
    (mem_cofibrations _)).right
  exact ⟨_, hc.of_retract R.i R.r R.retract⟩

end HomotopicalAlgebra.CellularLocalizationSmallness

namespace HomotopicalAlgebra.CellularLocalizationSmallness

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)

include h in
/-- A uniform original component bound controls the same original colimit
by the cardinal of its actual original object index. -/
theorem colimit_compactAt {D : Type w} [Category.{vD} D]
    (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s) (γ : Cardinal.{w})
    (hF : ∀ i : D, IsCellularCompactAt.{w} d.I (F.obj i) γ) :
    IsCellularCompactAt.{w} d.I s.pt (γ * Cardinal.mk D) := by
  simpa only [Cardinal.sum_const', mul_comm] using colimit_compactAt_bounds h F s hs (fun _ => γ) hF

local instance : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject

/-- The exact original I factory history determines this source's compactness bound. -/
def cofibrantCompactBound (Y : C) : Cardinal.{w} :=
  commonCompactBound h
    * Cardinal.mk (SmallObject.relativeCellComplexιObj d.I κ (initial.to Y)).Cells

include h in
/-- Every original cofibrant object is compact at the bound of its actual
original I factory history, through the original factory's object retract. -/
theorem cofibrant_compactAt (Y : C) [IsCofibrant Y] :
    IsCellularCompactAt.{w} d.I Y (cofibrantCompactBound h Y) := by
  have hc := cell_complex_compactAt h initialIsInitial
    (SmallObject.relativeCellComplexιObj d.I κ (initial.to Y))
  let R := (CellularCofibrationTransport.originalFactoryRetract d (initial.to Y)
    (mem_cofibrations _)).right
  exact hc.of_retract R.i R.r R.retract

end HomotopicalAlgebra.CellularLocalizationSmallness

section ColimitUniformSmallnessPromotion

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.CellularLocalizationSmallness

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)

/-- The original component smallness bounds and actual object-index cardinal
control the same original colimit, without a bound on the diagram's Hom universe. -/
def colimitSourceBound {D : Type w} [Category.{vD} D] (F : D ⥤ C)
    (hF : ∀ i : D, IsUniformlySmallRelativeTo.{w} d.I (F.obj i)) : Cardinal.{w} :=
  max (Cardinal.mk D) (⨆ i : D, CellularCofibrationTransport.originalSourceBound d (hF i))

/-- Every actual component retains its own original source smallness bound. -/
theorem colimitSourceBound_component_le {D : Type w} [Category.{vD} D]
    (F : D ⥤ C) (hF : ∀ i : D, IsUniformlySmallRelativeTo.{w} d.I (F.obj i)) (i : D) :
    CellularCofibrationTransport.originalSourceBound d (hF i) ≤ colimitSourceBound F hF :=
  (le_ciSup (f := fun i : D => CellularCofibrationTransport.originalSourceBound d (hF i))
    Cardinal.bddAbove_of_small i).trans (le_max_right _ _)

/-- Only the actual object index is needed to choose a common original stage. -/
theorem colimitSourceBound_objects_le {D : Type w} [Category.{vD} D]
    (F : D ⥤ C) (hF : ∀ i : D, IsUniformlySmallRelativeTo.{w} d.I (F.obj i)) :
    Cardinal.mk D ≤ colimitSourceBound F hF := le_max_left _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Source Hom of the actual original colimit preserves the caller's exact
original cofibration cocone. Component factors meet at one original stage;
monicity of the original cocone supplies their naturality and equality. -/
def mappedColimitCofibrationCocone {D : Type w} [Category.{vD} D]
    (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s)
    (hF : ∀ i : D, IsUniformlySmallRelativeTo.{w} d.I (F.obj i))
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : colimitSourceBound F hF < μ)
    (G : μ.ord.ToType ⥤ C) [G.IsWellOrderContinuous]
    (hG : ∀ j : μ.ord.ToType, ¬ IsMax j →
      cofibrations C (G.map (homOfLE (Order.le_succ j))))
    (t : Cocone G) (ht : IsColimit t) :
    IsColimit ((coyoneda.obj (op s.pt)).mapCocone t) := by
  refine Types.FilteredColimit.isColimitOf' _ _ (fun g => ?_) ?_
  · have hi : ∀ i : D, ∃ (j : μ.ord.ToType) (b : F.obj i ⟶ G.obj j),
        b ≫ t.ι.app j = s.ι.app i ≫ g := by
      intro i
      exact CellularCofibrationTransport.existsOriginalCofibrationStage d (hF i)
        μ ((colimitSourceBound_component_le F hF i).trans_lt hμ) G hG t ht (s.ι.app i ≫ g)
    choose stage b hb using hi
    obtain ⟨e, he⟩ := exists_regular_stage_bound μ stage
      ((colimitSourceBound_objects_le F hF).trans_lt hμ)
    let _ : Mono (t.ι.app e) := cofibration_chain_mono h G hG t ht e
    let m (i : D) : F.obj i ⟶ G.obj e := b i ≫ G.map (homOfLE (he i))
    have hm (i : D) : m i ≫ t.ι.app e = s.ι.app i ≫ g := by
      dsimp only [m]
      rw [Category.assoc, t.w, hb]
    let z : Cocone F :=
      { pt := G.obj e
        ι :=
          { app := m
            naturality i j a := by
              change F.map a ≫ m j = m i ≫ 𝟙 (G.obj e)
              rw [Category.comp_id]
              apply (cancel_mono (t.ι.app e)).1
              simp only [Category.assoc, hm]
              rw [← Category.assoc, s.w] } }
    have hm' : hs.desc z ≫ t.ι.app e = g := by
      apply hs.hom_ext
      intro i
      rw [← Category.assoc, hs.fac]
      exact hm i
    exact ⟨e, hs.desc z, hm'.symm⟩
  · intro j g g' hgg'
    let _ : Mono (t.ι.app j) := cofibration_chain_mono h G hG t ht j
    change g ≫ t.ι.app j = g' ≫ t.ι.app j at hgg'
    have heq : g = g' := (cancel_mono (t.ι.app j)).1 hgg'
    exact ⟨j, 𝟙 j, by rw [heq]⟩

include h in
/-- The original colimit source preserves every original cofibration chain
above the original component and actual object-index bound. -/
theorem colimit_preserves_cofibration_chain {D : Type w} [Category.{vD} D]
    (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s)
    (hF : ∀ i : D, IsUniformlySmallRelativeTo.{w} d.I (F.obj i))
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : colimitSourceBound F hF < μ)
    (G : μ.ord.ToType ⥤ C) [G.IsWellOrderContinuous]
    (hG : ∀ j : μ.ord.ToType, ¬ IsMax j →
      cofibrations C (G.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit G (coyoneda.obj (op s.pt)) where
  preserves := fun {t} ht => ⟨mappedColimitCofibrationCocone h F s hs hF μ hμ G hG t ht⟩

include h in
/-- Actual colimits of original I-small objects are I-small, including the
finite latching and pushout sources built from noncofibrant original J endpoints. -/
theorem colimit_uniformly_small {D : Type w} [Category.{vD} D]
    (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s)
    (hF : ∀ i : D, IsUniformlySmallRelativeTo.{w} d.I (F.obj i)) :
    IsUniformlySmallRelativeTo.{w} d.I s.pt := by
  refine ⟨colimitSourceBound F hF, ?_⟩
  intro μ _ _ hμ G _ hG
  exact colimit_preserves_cofibration_chain h F s hs hF μ hμ G
    (fun j hj => relativeCellMaps_le_cofibrations d _ (hG j hj))

include h in
/-- The actual colimit source is uniformly small on all original cofibration
chains at the same original component and object-index bound. -/
theorem colimit_uniform_cofibration_chains {D : Type w} [Category.{vD} D]
    (F : D ⥤ C) (s : Cocone F) (hs : IsColimit s)
    (hF : ∀ i : D, IsUniformlySmallRelativeTo.{w} d.I (F.obj i)) :
    ∃ β : Cardinal.{w},
      ∀ (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType], β < μ →
        ∀ (G : μ.ord.ToType ⥤ C) [G.IsWellOrderContinuous],
          (∀ j : μ.ord.ToType, ¬ IsMax j →
            cofibrations C (G.map (homOfLE (Order.le_succ j)))) →
          PreservesColimit G (coyoneda.obj (op s.pt)) :=
  ⟨colimitSourceBound F hF, fun μ _ _ hμ G _ hG =>
    colimit_preserves_cofibration_chain h F s hs hF μ hμ G hG⟩

end HomotopicalAlgebra.CellularLocalizationSmallness

end ColimitUniformSmallnessPromotion
