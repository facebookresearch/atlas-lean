/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellWeakLadder
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalWeakLadderColimitComparison
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellWeakDetector
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalArrowImageEnvelope
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.Presentable
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakFilteredColimits
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Original locally weak subarrows with uniform point and endpoint bounds

The actual original coherent ladder and its literal union colimits produce
the weak subarrow. Both cardinal bounds are selected before the ambient arrow
and incoming square, using original bounded-arrow representatives.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Cardinal
open SimplicialPresheaf.KanWeakInterpolation
open scoped SSet.modelCategoryQuillen
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem weak_original_chain_union
    {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y)
    {J : Type u} [LinearOrder J] [IsFiltered J]
    (γ : Cardinal.{u}) (b : J → cardinalSubarrowIndex g γ) (hb : Monotone b)
    (hw : ∀ j, SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ
      (Subdiagram.hom g (b j).val)) :
    SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ
      (Subdiagram.hom g (Subdiagram.indexedUnion g (fun j => (b j).val))) := by
  let : MorphismProperty.IsStableUnderFilteredColimits.{u, u}
      (SSet.realizationWeakEquivalences : MorphismProperty SSet.{u}) :=
    SSet.realizationWeakEquivalences_stableUnderFilteredColimits
  let F := hb.functor ⋙ cardinalSubarrowDiagram g γ
  let c := cardinalSubarrowChainCocone g γ b hb
  let t : F ⋙ Arrow.leftFunc ⟶ F ⋙ Arrow.rightFunc :=
    Functor.whiskerLeft F Arrow.leftToRight
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (F ⋙ Arrow.leftFunc) (F ⋙ Arrow.rightFunc)
    (Arrow.leftFunc.mapCocone c) (Arrow.rightFunc.mapCocone c)
    (cardinalSubarrowChainLeftIsColimit g γ b hb)
    (cardinalSubarrowChainRightIsColimit g γ b hb)
    t hw (Subdiagram.hom g (Subdiagram.indexedUnion g (fun j => (b j).val)))
    (fun j => (c.ι.app j).w)

/-- Uniform regular bounds, chosen before every original ambient weak arrow and
incoming square, contain that square in an actual original locally weak
subdiagram with both endpoint point bounds and absolute presentability ranks. -/
theorem exists_originalLocalWeakSubarrow
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (a : Arrow (SimplicialPresheaf.{u} D)) (ρ : Cardinal.{u}) [Fact ρ.IsRegular]
    (hκ : (originalLocalCellData S).κ ≤ ρ) (lower : Cardinal.{u}) :
    ∃ (γ δ : Cardinal.{u}) (hγ : Fact γ.IsRegular) (hδ : Fact δ.IsRegular),
      letI : Fact γ.IsRegular := hγ
      letI : Fact δ.IsRegular := hδ
      lower < γ ∧ ρ < γ ∧ (originalLocalCellData S).κ < γ ∧ γ < δ ∧
      ∀ {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y),
        originalLocalEquivalences S f → ∀ β : a ⟶ Arrow.mk f,
        ∃ (s : Subdiagram f) (α : a ⟶ Subdiagram.arrow f s),
          originalLocalEquivalences S (Subdiagram.hom f s) ∧
          HasCardinalLT (originalTotalPoints (Subdiagram.arrow f s).left) γ ∧
          HasCardinalLT (originalTotalPoints (Subdiagram.arrow f s).right) γ ∧
          IsCardinalPresentable (Subdiagram.arrow f s).left δ ∧
          IsCardinalPresentable (Subdiagram.arrow f s).right δ ∧
          α ≫ Subdiagram.inclusion f s = β ∧
          α.left ≫ (Subdiagram.inclusion f s).left = β.left ∧
          α.right ≫ (Subdiagram.inclusion f s).right = β.right := by
  let : Nonempty ρ.ord.ToType := by
    simpa using (show ρ.IsRegular from Fact.out).ne_zero
  let : OrderBot ρ.ord.ToType := WellFoundedLT.toOrderBot ρ.ord.ToType
  have hΩρ : ℵ₀ < ρ := (originalLocalCellData S).properties.1.trans_le hκ
  let : NoMaxOrder ρ.ord.ToType := Cardinal.noMaxOrder hΩρ.le
  obtain ⟨μ, ν, hμ, hν, γ, hγ, hLower, hργ, hκγ, hIndex, hFiltered,
    numeric, _predecessor, ladders⟩ := exists_originalLocalWeakLadder S a ρ hκ lower
  let : Fact γ.IsRegular := hγ
  let : IsCardinalFiltered ρ.ord.ToType ρ := hFiltered
  let : IsFiltered ρ.ord.ToType := isFiltered_of_isCardinalFiltered _ ρ
  obtain ⟨J, K, _hK, cover⟩ := exists_originalArrowPointBound_representatives (D := D) γ
  obtain ⟨δ, hδ, hγδ, _hΩδ, _hJδ, _hFixedδ, _hLPδ, ranks⟩ :=
    SimplicialPresheaf.exists_regular_cardinal_for_family K γ PUnit
  let : Fact δ.IsRegular := hδ
  have uniformRanks (b : Arrow (SimplicialPresheaf.{u} D))
      (hb : originalArrowPointBound γ b) :
      IsCardinalPresentable b.left δ ∧ IsCardinalPresentable b.right δ := by
    obtain ⟨j, ⟨e⟩⟩ := cover b hb
    let : IsCardinalPresentable (K j).left δ := (ranks j).1
    let : IsCardinalPresentable (K j).right δ := (ranks j).2
    let eL : (K j).left ≅ b.left := Arrow.leftFunc.mapIso e.symm
    let eR : (K j).right ≅ b.right := Arrow.rightFunc.mapIso e.symm
    exact ⟨isCardinalPresentable_of_iso eL δ, isCardinalPresentable_of_iso eR δ⟩
  refine ⟨γ, δ, hγ, hδ, hLower, hργ, hκγ, hγδ, ?_⟩
  intro X Y f hf β
  let R := originalLocalCellReplacement S
  obtain ⟨A, B, hA, hB, p, q, _hZero, _hLimit, hWeakB, stageBounds,
    hAfin, _hBfin, mixed, _mixedAll, natural, successor, _identities,
    _compositions, _ambient, j, jfac, _jnatural⟩ := ladders f hf β
  have aPoints (α : ρ.ord.ToType) :
      originalArrowPointBound γ (Subdiagram.arrow f (A α)) := by
    let : Fact (ν α).IsRegular := hν α
    obtain ⟨_, _, _, hμν, hνγ, _, _⟩ := numeric α
    have h := (stageBounds α).1
    exact ⟨h.1.of_le (hμν.le.trans hνγ.le), h.2.of_le (hμν.le.trans hνγ.le)⟩
  have bPoints (α : ρ.ord.ToType) :
      originalArrowPointBound γ (Subdiagram.arrow (R.map f) (B α)) := by
    let : Fact (ν α).IsRegular := hν α
    obtain ⟨_, _, _, _, hνγ, _, _⟩ := numeric α
    have h := (stageBounds α).2.1
    exact ⟨h.1.of_le hνγ.le, h.2.of_le hνγ.le⟩
  let aBar : ρ.ord.ToType → cardinalSubarrowIndex f γ := fun α => ⟨A α, aPoints α⟩
  let bBar : ρ.ord.ToType → cardinalSubarrowIndex (R.map f) γ :=
    fun α => ⟨B α, bPoints α⟩
  have haBar : Monotone aBar := fun _ _ h => hA h
  have hbBar : Monotone bBar := fun _ _ h => hB h
  let P : (haBar.functor ⋙ cardinalSubarrowDiagram f γ) ⋙ R.mapArrow ⟶
      hbBar.functor ⋙ cardinalSubarrowDiagram (R.map f) γ :=
    { app := p
      naturality := by
        intro α ζ h
        exact (natural α ζ (leOfHom h)).1 }
  let Q : hbBar.functor ⋙ cardinalSubarrowDiagram (R.map f) γ ⟶
      Order.succ_mono.functor ⋙ (haBar.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
        R.mapArrow :=
    { app := q
      naturality := by
        intro α ζ h
        exact (natural α ζ (leOfHom h)).2.1 }
  have hPQ : ∀ α, P.app α ≫ Q.app α =
      ((haBar.functor ⋙ cardinalSubarrowDiagram f γ) ⋙ R.mapArrow).map
        (homOfLE (Order.le_succ α)) := fun α => (mixed α).1
  have hQP : ∀ α, Q.app α ≫ P.app (Order.succ α) =
      (hbBar.functor ⋙ cardinalSubarrowDiagram (R.map f) γ).map
        (homOfLE (Order.le_succ α)) := fun α => (successor α).1.symm
  let s := Subdiagram.indexedUnion f A
  have hsPoints : originalArrowPointBound γ (Subdiagram.arrow f s) := hAfin
  have hsRanks := uniformRanks (Subdiagram.arrow f s) hsPoints
  have hWB : SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ
      (Subdiagram.hom (R.map f) (Subdiagram.indexedUnion (R.map f) B)) :=
    weak_original_chain_union (R.map f) γ bBar hbBar hWeakB
  let e := originalLocalLadderColimitIso S ρ hκ f γ aBar haBar bBar hbBar P Q hPQ hQP
  have hWR : SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ
      (R.map (Subdiagram.hom f s)) :=
    ((SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ).arrow_iso_iff e).mpr hWB
  have hBase : weakEquivalences (SimplicialPresheaf.{u} D)
      (R.map (Subdiagram.hom f s)) := by
    change (data D).model.categoryWithWeakEquivalences.weakEquivalences _
    rw [(data D).weakEquivalences_eq]
    exact hWR
  have hsWeak : originalLocalEquivalences S (Subdiagram.hom f s) :=
    (originalLocalEquivalence_iff_weak_originalLocalCellReplacement S _).mpr hBase
  let α : a ⟶ Subdiagram.arrow f s :=
    j ⊥ ≫ Subdiagram.map f (Subdiagram.le_indexedUnion f A ⊥)
  have hfactor : α ≫ Subdiagram.inclusion f s = β := by
    have hu : Subdiagram.map f (Subdiagram.le_indexedUnion f A ⊥) ≫
        Subdiagram.inclusion f s = Subdiagram.inclusion f (A ⊥) := by
      ext d n x <;> rfl
    dsimp only [α]
    rw [Category.assoc, hu]
    exact (jfac ⊥).1
  exact ⟨s, α, hsWeak, hsPoints.1, hsPoints.2, hsRanks.1, hsRanks.2,
    hfactor, congrArg Arrow.Hom.left hfactor, congrArg Arrow.Hom.right hfactor⟩

end SimplicialPresheaf.InjectiveKan
