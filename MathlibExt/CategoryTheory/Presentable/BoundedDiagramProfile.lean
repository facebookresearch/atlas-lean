/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.FunctorPresentability
public import MathlibExt.CategoryTheory.Presentable.DiagramCompactnessCardinal
public import MathlibExt.CategoryTheory.SmallObject.EndpointProfile

/-!
# A common compactness profile on the original diagram category

The actual LP rank and the supplied generation cardinal remain distinct.
The result retains the same original I/J arrows, ordinary index equivalence,
cofree values and Hom-power values. Endpoint ranks, base and diagram local
presentability, power accessibility and the whole component criterion are
proved internally.

Essential index data bounds the representative arrow type and every original
Hom type. An all-original arrow bound requires its actual additional size data.
No factorization is reselected at the resulting compactness rank.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w uM vM uD vD

namespace CategoryTheory.Presentable.BoundedDiagramProfile

open Limits Opposite

variable (M : Type uM) [Category.{vM} M] (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable M κLP]
  {D : Type uD} [Category.{vD} D] (s : Functor.EssentialIndexData.{w} D M)

/-- The complete bounded profile returns actual properties of the original data.
The cofree and power values still use the input LP rank κLP. -/
structure Profile (κ : Cardinal.{w}) (I J : MorphismProperty M)
    (χ : Cardinal.{w}) [Fact χ.IsRegular] : Prop where
  lp_le : κLP ≤ χ
  generation_le : κ ≤ χ
  uncountable : Cardinal.aleph0 < χ
  objects : HasCardinalLT s.index χ
  arrows : HasCardinalLT (Arrow s.index) χ
  sourceI : ∀ i : I.toSet, IsCardinalPresentable i.1.left χ
  targetI : ∀ i : I.toSet, IsCardinalPresentable i.1.right χ
  sourceJ : ∀ j : J.toSet, IsCardinalPresentable j.1.left χ
  targetJ : ∀ j : J.toSet, IsCardinalPresentable j.1.right χ
  baseLocallyPresentable : IsCardinalLocallyPresentable M χ
  diagramLocallyPresentable : IsCardinalLocallyPresentable (D ⥤ M) χ
  baseAccessible : IsCardinalAccessibleCategory M χ
  diagramAccessible : IsCardinalAccessibleCategory (D ⥤ M) χ
  originalHom : ∀ d e : D, HasCardinalLT (e ⟶ d) χ
  cofreeAccessible : ∀ d : D, (Completeness.cofree M κLP s d).IsCardinalAccessible χ
  powerAccessible : ∀ d e : D,
    (Completeness.homPower M κLP s d e).IsCardinalAccessible χ
  evaluationAccessible : ∀ d : D, ((evaluation D M).obj d).IsCardinalAccessible χ
  criterion : ∀ F : D ⥤ M,
    IsCardinalPresentable F χ ↔ ∀ d : D, IsCardinalPresentable (F.obj d) χ

/-- Honest sufficient conditions at a supplied rank prove the full original profile.
Neither power accessibility nor the whole-diagram criterion is a premise. -/
theorem of_bounds (κ : Cardinal.{w}) (I J : MorphismProperty M)
    (χ : Cardinal.{w}) [Fact χ.IsRegular]
    (hLP : κLP ≤ χ) (hκ : κ ≤ χ) (hω : Cardinal.aleph0 < χ)
    (hArrow : HasCardinalLT (Arrow s.index) χ)
    (hI : ∀ i : I.toSet, IsCardinalPresentable i.1.left χ ∧
      IsCardinalPresentable i.1.right χ)
    (hJ : ∀ j : J.toSet, IsCardinalPresentable j.1.left χ ∧
      IsCardinalPresentable j.1.right χ) :
    Profile M κLP s κ I J χ := by
  have hHom := HomPowerAccessibility.hom_bound_of_representative_arrows M s χ hArrow
  let : IsCardinalLocallyPresentable (D ⥤ M) κLP :=
    HomPowerAccessibility.diagramLocallyPresentable M κLP s
  let : IsCardinalLocallyPresentable M χ :=
    IsCardinalLocallyPresentable.of_le M hLP
  let : IsCardinalLocallyPresentable (D ⥤ M) χ :=
    IsCardinalLocallyPresentable.of_le (D ⥤ M) hLP
  refine
    { lp_le := hLP
      generation_le := hκ
      uncountable := hω
      objects := hArrow.of_injective (fun d : s.index ↦ Arrow.mk (𝟙 d))
        (fun _ _ h ↦ congr($(h).left))
      arrows := hArrow
      sourceI := fun i ↦ (hI i).1
      targetI := fun i ↦ (hI i).2
      sourceJ := fun j ↦ (hJ j).1
      targetJ := fun j ↦ (hJ j).2
      baseLocallyPresentable := inferInstance
      diagramLocallyPresentable := inferInstance
      baseAccessible := inferInstance
      diagramAccessible := inferInstance
      originalHom := hHom
      cofreeAccessible := fun d ↦
        HomPowerAccessibility.cofree_isCardinalAccessible_of_hom_bounds M κLP s d χ hLP
          (hHom d)
      powerAccessible := fun d e ↦
        HomPowerAccessibility.homPower_isCardinalAccessible_of_hom_bound M κLP s d e χ hLP
          (hHom d e)
      evaluationAccessible := ?_
      criterion := FunctorPresentability.presentable_iff_components M κLP s χ hLP hArrow }
  intro d
  let : PreservesColimitsOfSize.{w, w} ((evaluation D M).obj d) :=
    HomPowerAccessibility.evaluation_preservesColimits M κLP d
  infer_instance

/-- Both genuine small original endpoint families internally provide one common rank.
The supplied generation cardinal and every original functor value are retained. -/
theorem exists_profile (κ : Cardinal.{w}) (I J : MorphismProperty M)
    [I.IsSmall.{w}] [J.IsSmall.{w}] :
    ∃ (χ : Cardinal.{w}) (_ : Fact χ.IsRegular), Profile M κLP s κ I J χ := by
  obtain ⟨χ, hχ, hLP, hκ, hω, hArrow, hI, hJ⟩ :=
    DiagramCompactnessCardinal.endpoint_rank M κLP s κ I J
  let : Fact χ.IsRegular := hχ
  exact ⟨χ, hχ, of_bounds M κLP s κ I J χ hLP hκ hω hArrow hI hJ⟩

/-- The actual input generation rank is retained precisely under these real bounds.
This theorem does not transport fixed small-object eligibility to a different rank. -/
theorem profile_at_generation_rank (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (I J : MorphismProperty M) (hLP : κLP ≤ κ) (hω : Cardinal.aleph0 < κ)
    (hArrow : HasCardinalLT (Arrow s.index) κ)
    (hI : ∀ i : I.toSet, IsCardinalPresentable i.1.left κ ∧
      IsCardinalPresentable i.1.right κ)
    (hJ : ∀ j : J.toSet, IsCardinalPresentable j.1.left κ ∧
      IsCardinalPresentable j.1.right κ) :
    Profile M κLP s κ I J κ :=
  of_bounds M κLP s κ I J κ hLP le_rfl hω hArrow hI hJ

/-- The stronger eligible-family route uses the existing original endpoint theorem
at the SAME fixed κ. It synchronizes the two actual endpoint ranks, and then proves
the SAME profile with the same κLP cofree/power values. -/
theorem exists_profile_of_eligible (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType] (I J : MorphismProperty M)
    [I.IsCardinalForSmallObjectArgument κ] [J.IsCardinalForSmallObjectArgument κ] :
    ∃ (χ : Cardinal.{w}) (_ : Fact χ.IsRegular), Profile M κLP s κ I J χ := by
  let : IsAccessibleCategory.{w} M := ⟨κLP, inferInstance, inferInstance⟩
  let Fixed := κLP.ord.ToType ⊕ (κ.ord.ToType ⊕ Arrow s.index)
  obtain ⟨μI, hRegularI, hωI, hFixedI, hEndpointsI⟩ :=
    SmallObject.original_endpoints_have_common_presentability_cardinal I κ Fixed
  obtain ⟨μJ, hRegularJ, _hωJ, _hFixedJ, hEndpointsJ⟩ :=
    SmallObject.original_endpoints_have_common_presentability_cardinal J κ Fixed
  let : Fact μI.IsRegular := hRegularI
  let : Fact μJ.IsRegular := hRegularJ
  let Upper := μI.ord.ToType ⊕ μJ.ord.ToType
  obtain ⟨χ, hRegular, hUpper⟩ := HasCardinalLT.exists_regular_cardinal Upper
  let : Fact χ.IsRegular := ⟨hRegular⟩
  have hμI : μI < χ := by
    have h := hUpper.of_injective (Sum.inl : μI.ord.ToType → Upper) Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hμJ : μJ < χ := by
    have h := hUpper.of_injective (Sum.inr : μJ.ord.ToType → Upper) Sum.inr_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hFixed : HasCardinalLT Fixed χ := hFixedI.of_le hμI.le
  have hLP : κLP < χ := by
    have h := hFixed.of_injective (Sum.inl : κLP.ord.ToType → Fixed) Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hκ : κ < χ := by
    have h := hFixed.of_injective
      (fun x : κ.ord.ToType ↦ (Sum.inr (Sum.inl x) : Fixed))
      (Sum.inr_injective.comp Sum.inl_injective)
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hArrow : HasCardinalLT (Arrow s.index) χ :=
    hFixed.of_injective
      (fun x : Arrow s.index ↦ (Sum.inr (Sum.inr x) : Fixed))
      (Sum.inr_injective.comp Sum.inr_injective)
  have hI (i : I.toSet) :
      IsCardinalPresentable i.1.left χ ∧ IsCardinalPresentable i.1.right χ := by
    let : IsCardinalPresentable i.1.left μI := (hEndpointsI i).1
    let : IsCardinalPresentable i.1.right μI := (hEndpointsI i).2
    exact ⟨isCardinalPresentable_of_le _ hμI.le, isCardinalPresentable_of_le _ hμI.le⟩
  have hJ (j : J.toSet) :
      IsCardinalPresentable j.1.left χ ∧ IsCardinalPresentable j.1.right χ := by
    let : IsCardinalPresentable j.1.left μJ := (hEndpointsJ j).1
    let : IsCardinalPresentable j.1.right μJ := (hEndpointsJ j).2
    exact ⟨isCardinalPresentable_of_le _ hμJ.le, isCardinalPresentable_of_le _ hμJ.le⟩
  exact ⟨χ, inferInstance, of_bounds M κLP s κ I J χ hLP.le hκ.le
    (hωI.trans hμI) hArrow hI hJ⟩

end CategoryTheory.Presentable.BoundedDiagramProfile
