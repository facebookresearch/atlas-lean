/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellUniformWeakStep
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.CompleteLattice.Basic

/-!
# Before-ambient regular budgets for the original weak ladder

The input budget at each original ordinal dominates every earlier output
budget. Actual uniform steps and original union bounds remain available at
those budgets, without a self-image bound or any colimit assertion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits Cardinal
open SimplicialPresheaf.KanWeakInterpolation

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

private abbrev StepProperty
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ ν : Cardinal.{u}) (hν : Fact ν.IsRegular) :
    Prop :=
  letI : Fact ν.IsRegular := hν
  ∀ {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y),
      originalLocalEquivalences S f → ∀ s : cardinalSubarrowIndex f μ,
      ∃ (b : Subdiagram ((originalLocalCellReplacement S).map f))
        (t : cardinalSubarrowIndex f ν) (hst : s.val ≤ t.val)
        (p : (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val) ⟶
          Subdiagram.arrow ((originalLocalCellReplacement S).map f) b)
        (q : Subdiagram.arrow ((originalLocalCellReplacement S).map f) b ⟶
          (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f t.val)),
        SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ
            (Subdiagram.hom ((originalLocalCellReplacement S).map f) b) ∧
          originalArrowPointBound ν
            (Subdiagram.arrow ((originalLocalCellReplacement S).map f) b) ∧
          IsCardinalPresentable
            (Subdiagram.arrow ((originalLocalCellReplacement S).map f) b).left ν ∧
          IsCardinalPresentable
            (Subdiagram.arrow ((originalLocalCellReplacement S).map f) b).right ν ∧
          originalArrowPointBound ν
            ((originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val)) ∧
          IsCardinalPresentable
            ((originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val)).left ν ∧
          IsCardinalPresentable
            ((originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val)).right ν ∧
          p ≫ q = (originalLocalCellReplacement S).mapArrow.map (Subdiagram.map f hst) ∧
          p ≫ Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b =
            (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f s.val) ∧
          q ≫ (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f t.val) =
            Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b ∧
          p.left ≫ q.left = (originalLocalCellReplacement S).map (Subdiagram.map f hst).left ∧
          p.right ≫ q.right = (originalLocalCellReplacement S).map (Subdiagram.map f hst).right ∧
          p.left ≫ (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).left =
            (originalLocalCellReplacement S).map (Subdiagram.leftInclusion f s.val) ∧
          p.right ≫ (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).right =
            (originalLocalCellReplacement S).map (Subdiagram.rightInclusion f s.val) ∧
          q.left ≫ (originalLocalCellReplacement S).map (Subdiagram.leftInclusion f t.val) =
            (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).left ∧
          q.right ≫ (originalLocalCellReplacement S).map (Subdiagram.rightInclusion f t.val) =
            (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).right

private structure BudgetStage
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (a : Arrow (SimplicialPresheaf.{u} D)) (ρ lower : Cardinal.{u}) where
  μ : Cardinal.{u}
  ν : Cardinal.{u}
  regularInput : Fact μ.IsRegular
  regularOutput : Fact ν.IsRegular
  lower_lt : lower < μ
  index_lt : ρ < μ
  input_lt_output : μ < ν
  originalPoints : originalArrowPointBound μ a
  originalRanks :
    letI : Fact μ.IsRegular := regularInput
    IsCardinalPresentable a.left μ ∧ IsCardinalPresentable a.right μ
  step : StepProperty S μ ν regularOutput

private theorem existsStage
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (a : Arrow (SimplicialPresheaf.{u} D)) (ρ lower : Cardinal.{u})
    (α : ρ.ord.ToType) (prev : ∀ β : ρ.ord.ToType, β < α → BudgetStage S a ρ lower) :
    Nonempty {b : BudgetStage S a ρ lower //
      ∀ (β : ρ.ord.ToType) (h : β < α), (prev β h).ν < b.μ} := by
  let Prefix := {β : ρ.ord.ToType // β < α}
  let Fixed := (originalTotalPoints a.left ⊕ originalTotalPoints a.right) ⊕
    ((lower.ord.ToType ⊕ ρ.ord.ToType) ⊕
      (Σ β : Prefix, (prev β.val β.property).ν.ord.ToType))
  let F : PUnit.{u + 1} → Arrow (SimplicialPresheaf.{u} D) := fun _ => a
  obtain ⟨μ, hμ, hBound, _, _, hFixed, _, hRanks⟩ :=
    exists_regular_cardinal_for_family F (ρ ⊔ lower) Fixed
  let : Fact μ.IsRegular := hμ
  have hρ : ρ < μ := le_sup_left.trans_lt hBound
  have hLower : lower < μ := le_sup_right.trans_lt hBound
  have hPoints : originalArrowPointBound μ a :=
    ⟨hFixed.of_injective (fun x => (Sum.inl (Sum.inl x) : Fixed))
        (Sum.inl_injective.comp Sum.inl_injective),
      hFixed.of_injective (fun x => (Sum.inl (Sum.inr x) : Fixed))
        (Sum.inl_injective.comp Sum.inr_injective)⟩
  obtain ⟨ν, hν, _, hμν, _, all⟩ := exists_originalLocalUniformWeakStep S μ (ρ ⊔ lower)
  let : Fact ν.IsRegular := hν
  have hStep : StepProperty S μ ν hν := by
    intro X Y f hf s
    obtain ⟨b, t, hst, p, q, hw, hBL, hBR, hRL, hRR, hAL, hAR, hKL, hKR,
      hpq, hp, hq, hplq, hprq, hpl, hpr, hql, hqr⟩ := all f hf s
    exact ⟨b, t, hst, p, q, hw, ⟨hBL, hBR⟩, hRL, hRR, ⟨hAL, hAR⟩,
      hKL, hKR, hpq, hp, hq, hplq, hprq, hpl, hpr, hql, hqr⟩
  let b : BudgetStage S a ρ lower :=
    ⟨μ, ν, hμ, hν, hLower, hρ, hμν, hPoints, hRanks PUnit.unit, hStep⟩
  refine ⟨⟨b, ?_⟩⟩
  intro β h
  have hp := hFixed.of_injective
    (fun x : (prev β h).ν.ord.ToType =>
      (Sum.inr (Sum.inr (⟨⟨β, h⟩, x⟩)) : Fixed))
    (Sum.inr_injective.comp (Sum.inr_injective.comp sigma_mk_injective))
  simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using hp

private def chooseStage
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (a : Arrow (SimplicialPresheaf.{u} D)) (ρ lower : Cardinal.{u})
    (α : ρ.ord.ToType) (prev : ∀ β : ρ.ord.ToType, β < α → BudgetStage S a ρ lower) :
    {b : BudgetStage S a ρ lower // ∀ (β : ρ.ord.ToType) (h : β < α), (prev β h).ν < b.μ} :=
  Classical.choice (existsStage S a ρ lower α prev)

private def stageFamily
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (a : Arrow (SimplicialPresheaf.{u} D)) (ρ lower : Cardinal.{u}) :
    ρ.ord.ToType → BudgetStage S a ρ lower :=
  WellFounded.fix (inferInstance : WellFoundedRelation ρ.ord.ToType).wf
    (fun α prev => (chooseStage S a ρ lower α prev).val)

private theorem stageFamily_eq
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (a : Arrow (SimplicialPresheaf.{u} D)) (ρ lower : Cardinal.{u}) (α : ρ.ord.ToType) :
    stageFamily S a ρ lower α =
      (chooseStage S a ρ lower α (fun β _ => stageFamily S a ρ lower β)).val :=
  WellFounded.fix_eq _ _ _

private theorem stageFamily_predecessor
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (a : Arrow (SimplicialPresheaf.{u} D)) (ρ lower : Cardinal.{u})
    (β α : ρ.ord.ToType) (h : β < α) :
    (stageFamily S a ρ lower β).ν < (stageFamily S a ρ lower α).μ := by
  rw [stageFamily_eq S a ρ lower α]
  exact (chooseStage S a ρ lower α (fun β _ => stageFamily S a ρ lower β)).property β h

private theorem ordinalPoints_lt (ρ τ : Cardinal.{u}) (h : ρ < τ) :
    HasCardinalLT ρ.ord.ToType τ := by
  simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem originalUnion_lt
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    (τ : Cardinal.{u}) [Fact τ.IsRegular] {J : Type u}
    (s : J → Subdiagram f) (hJ : HasCardinalLT J τ)
    (hs : ∀ j, originalArrowPointBound τ (Subdiagram.arrow f (s j))) :
    originalArrowPointBound τ (Subdiagram.arrow f (Subdiagram.indexedUnion f s)) := by
  let : Small.{u} J := hJ.small
  let inputs : J → cardinalSubarrowIndex f τ := fun j => ⟨s j, hs j⟩
  let U := cardinalSubarrowUnion f τ inputs hJ
  have hU : U.val = Subdiagram.indexedUnion f s := by
    change Subdiagram.indexedUnion f
      (fun j : Shrink.{u} J => s ((equivShrink.{u} J).symm j)) = Subdiagram.indexedUnion f s
    apply Subdiagram.ext
    funext d
    apply Subtype.ext
    apply Prod.ext
    · change (⨆ j : Shrink.{u} J, ((s ((equivShrink.{u} J).symm j)).row d).left (f.app d)) =
        ⨆ j : J, ((s j).row d).left (f.app d)
      exact (equivShrink.{u} J).symm.iSup_comp
        (g := fun j : J => (((s j).row d).left (f.app d) : (X.obj d).Subcomplex))
    · change (⨆ j : Shrink.{u} J, ((s ((equivShrink.{u} J).symm j)).row d).right (f.app d)) =
        ⨆ j : J, ((s j).row d).right (f.app d)
      exact (equivShrink.{u} J).symm.iSup_comp
        (g := fun j : J => (((s j).row d).right (f.app d) : (Y.obj d).Subcomplex))
  rw [← hU]
  exact U.property

/-- Regular original input/output budgets dominate all predecessors and support
each actual weak step and both original prefix and final point unions.
The SAME original ordinal index is genuinely ρ-cardinal-filtered. -/
theorem exists_originalLocalWeakLadderBudgets
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (a : Arrow (SimplicialPresheaf.{u} D)) (ρ : Cardinal.{u}) [Fact ρ.IsRegular]
    (hκ : (originalLocalCellData S).κ ≤ ρ) (lower : Cardinal.{u}) :
    ∃ (μ ν : ρ.ord.ToType → Cardinal.{u})
      (hμ : ∀ α, Fact (μ α).IsRegular) (hν : ∀ α, Fact (ν α).IsRegular)
      (γ : Cardinal.{u}) (_hγ : Fact γ.IsRegular),
      lower < γ ∧ ρ < γ ∧ (originalLocalCellData S).κ < γ ∧
        HasCardinalLT ρ.ord.ToType γ ∧
        IsCardinalFiltered ρ.ord.ToType ρ ∧
        (∀ α, lower < μ α ∧ ρ < μ α ∧ (originalLocalCellData S).κ < μ α ∧
          μ α < ν α ∧ ν α < γ ∧ originalArrowPointBound (μ α) a ∧
          (letI : Fact (μ α).IsRegular := hμ α
           IsCardinalPresentable a.left (μ α) ∧ IsCardinalPresentable a.right (μ α))) ∧
        (∀ (β α : ρ.ord.ToType), β < α → ν β < μ α) ∧
        (∀ α, letI : Fact (ν α).IsRegular := hν α
          ∀ {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y),
      originalLocalEquivalences S f → ∀ s : cardinalSubarrowIndex f (μ α),
      ∃ (b : Subdiagram ((originalLocalCellReplacement S).map f))
        (t : cardinalSubarrowIndex f (ν α)) (hst : s.val ≤ t.val)
        (p : (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val) ⟶
          Subdiagram.arrow ((originalLocalCellReplacement S).map f) b)
        (q : Subdiagram.arrow ((originalLocalCellReplacement S).map f) b ⟶
          (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f t.val)),
        SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ
            (Subdiagram.hom ((originalLocalCellReplacement S).map f) b) ∧
          originalArrowPointBound (ν α)
            (Subdiagram.arrow ((originalLocalCellReplacement S).map f) b) ∧
          IsCardinalPresentable
            (Subdiagram.arrow ((originalLocalCellReplacement S).map f) b).left (ν α) ∧
          IsCardinalPresentable
            (Subdiagram.arrow ((originalLocalCellReplacement S).map f) b).right (ν α) ∧
          originalArrowPointBound (ν α)
            ((originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val)) ∧
          IsCardinalPresentable
            ((originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val)).left (ν α) ∧
          IsCardinalPresentable
            ((originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val)).right (ν α) ∧
          p ≫ q = (originalLocalCellReplacement S).mapArrow.map (Subdiagram.map f hst) ∧
          p ≫ Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b =
            (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f s.val) ∧
          q ≫ (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f t.val) =
            Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b ∧
          p.left ≫ q.left = (originalLocalCellReplacement S).map (Subdiagram.map f hst).left ∧
          p.right ≫ q.right = (originalLocalCellReplacement S).map (Subdiagram.map f hst).right ∧
          p.left ≫ (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).left =
            (originalLocalCellReplacement S).map (Subdiagram.leftInclusion f s.val) ∧
          p.right ≫ (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).right =
            (originalLocalCellReplacement S).map (Subdiagram.rightInclusion f s.val) ∧
          q.left ≫ (originalLocalCellReplacement S).map (Subdiagram.leftInclusion f t.val) =
            (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).left ∧
          q.right ≫ (originalLocalCellReplacement S).map (Subdiagram.rightInclusion f t.val) =
            (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).right) ∧
        (∀ (α : ρ.ord.ToType) {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
          (s : {β : ρ.ord.ToType // β < α} → Subdiagram f),
          (∀ β, originalArrowPointBound (ν β.val) (Subdiagram.arrow f (s β))) →
          originalArrowPointBound (μ α) (Subdiagram.arrow f (Subdiagram.indexedUnion f s))) ∧
        (∀ {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
          (s : ρ.ord.ToType → Subdiagram f),
          (∀ α, originalArrowPointBound (ν α) (Subdiagram.arrow f (s α))) →
          originalArrowPointBound γ (Subdiagram.arrow f (Subdiagram.indexedUnion f s))) := by
  let b := stageFamily S a ρ lower
  let μ : ρ.ord.ToType → Cardinal.{u} := fun α => (b α).μ
  let ν : ρ.ord.ToType → Cardinal.{u} := fun α => (b α).ν
  let hμ : ∀ α, Fact (μ α).IsRegular := fun α => (b α).regularInput
  let hν : ∀ α, Fact (ν α).IsRegular := fun α => (b α).regularOutput
  let Fixed := (lower.ord.ToType ⊕ ρ.ord.ToType) ⊕
    (Σ α : ρ.ord.ToType, (ν α).ord.ToType)
  obtain ⟨γ, hγ, hFixed⟩ := HasCardinalLT.exists_regular_cardinal.{u} Fixed
  let : Fact γ.IsRegular := ⟨hγ⟩
  have hLower : lower < γ := by
    have h := hFixed.of_injective (fun x : lower.ord.ToType =>
      (Sum.inl (Sum.inl x) : Fixed)) (Sum.inl_injective.comp Sum.inl_injective)
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hρ : ρ < γ := by
    have h := hFixed.of_injective (fun x : ρ.ord.ToType =>
      (Sum.inl (Sum.inr x) : Fixed)) (Sum.inl_injective.comp Sum.inr_injective)
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hνγ (α : ρ.ord.ToType) : ν α < γ := by
    have h := hFixed.of_injective (fun x : (ν α).ord.ToType =>
      (Sum.inr (⟨α, x⟩) : Fixed)) (Sum.inr_injective.comp sigma_mk_injective)
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hPred (β α : ρ.ord.ToType) (h : β < α) : ν β < μ α :=
    stageFamily_predecessor S a ρ lower β α h
  refine ⟨μ, ν, hμ, hν, γ, inferInstance, hLower, hρ, hκ.trans_lt hρ,
    ordinalPoints_lt ρ γ hρ, (inferInstance : IsCardinalFiltered ρ.ord.ToType ρ),
    ?_, hPred, ?_, ?_, ?_⟩
  · intro α
    exact ⟨(b α).lower_lt, (b α).index_lt, hκ.trans_lt (b α).index_lt,
      (b α).input_lt_output, hνγ α, (b α).originalPoints, (b α).originalRanks⟩
  · intro α
    exact (b α).step
  · intro α X Y f s hs
    let : Fact (μ α).IsRegular := hμ α
    have hIndex : HasCardinalLT {β : ρ.ord.ToType // β < α} (μ α) :=
      (ordinalPoints_lt ρ (μ α) (b α).index_lt).of_injective Subtype.val Subtype.val_injective
    apply originalUnion_lt f (μ α) s hIndex
    intro β
    exact ⟨(hs β).1.of_le (hPred β.val α β.property).le,
      (hs β).2.of_le (hPred β.val α β.property).le⟩
  · intro X Y f s hs
    apply originalUnion_lt f γ s (ordinalPoints_lt ρ γ hρ)
    intro α
    exact ⟨(hs α).1.of_le (hνγ α).le, (hs α).2.of_le (hνγ α).le⟩

end SimplicialPresheaf.InjectiveKan
