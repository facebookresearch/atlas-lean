/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellReplacementAccessibility
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CardinalSubarrowPresentation
import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Strict support in original small subarrows

Both presentable endpoints of an original square factor through the same
original small subarrow after applying the fixed local replacement. The
endpoint inclusions and the whole square remain strict.
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

private theorem originalLocalCellSupport_profile
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u})
    (h : (originalLocalCellData S).κ ≤ μ) :
    ℵ₀ < μ ∧ HasCardinalLT (cardinalSubarrowWidth D) μ := by
  let d := originalLocalCellData S
  let := d.regular
  let := d.orderBot
  rcases d.properties with ⟨hω, _, hD, hOp, hDelta, _⟩
  have hWidth : HasCardinalLT (cardinalSubarrowWidth D) d.κ :=
    (hasCardinalLT_sum_iff _ _ _ hω.le).mpr
      ⟨hD, (hasCardinalLT_sum_iff _ _ _ hω.le).mpr ⟨hOp, hDelta⟩⟩
  exact ⟨hω.trans_le h, hWidth.of_le h⟩

/-- An original square with both endpoints presentable factors strictly
through the same replacement of an actual original small subarrow. -/
theorem exists_originalLocalCellSupport
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ)
    (b : Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    [IsCardinalPresentable b.left μ] [IsCardinalPresentable b.right μ]
    (β : b ⟶ (originalLocalCellReplacement S).mapArrow.obj (Arrow.mk f)) :
    ∃ (s : cardinalSubarrowIndex f μ)
      (α : b ⟶ (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val)),
      α ≫ (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f s.val) = β ∧
      α.left ≫ (originalLocalCellReplacement S).map (Subdiagram.leftInclusion f s.val) =
        β.left ∧
      α.right ≫ (originalLocalCellReplacement S).map (Subdiagram.rightInclusion f s.val) =
        β.right ∧
      α.left ≫ (originalLocalCellReplacement S).map (Subdiagram.hom f s.val) =
        b.hom ≫ α.right := by
  let R := originalLocalCellReplacement S
  obtain ⟨hΩ, hWidth⟩ := originalLocalCellSupport_profile S μ h
  let := cardinalSubarrowIndex_isCardinalFiltered f μ
  let A := cardinalSubarrowDiagram f μ
  let cL : Cocone (A ⋙ Arrow.leftFunc ⋙ R) :=
    R.mapCocone (cardinalSubarrowLeftCocone f μ)
  let cR : Cocone (A ⋙ Arrow.rightFunc ⋙ R) :=
    R.mapCocone (cardinalSubarrowRightCocone f μ)
  have hcL : IsColimit cL := originalLocalCellReplacementPreservesCocone S μ h _
    (cardinalSubarrowLeftIsColimit f μ hΩ hWidth)
  have hcR : IsColimit cR := originalLocalCellReplacementPreservesCocone S μ h _
    (cardinalSubarrowRightIsColimit f μ hΩ hWidth)
  let τ : (A ⋙ Arrow.leftFunc ⋙ R) ⟶ (A ⋙ Arrow.rightFunc ⋙ R) :=
    Functor.whiskerRight (Functor.whiskerLeft A Arrow.leftToRight) R
  have hτ (s : cardinalSubarrowIndex f μ) :
      cL.ι.app s ≫ R.map f = τ.app s ≫ cR.ι.app s := by
    change R.map (Subdiagram.leftInclusion f s.val) ≫ R.map f =
      R.map (Subdiagram.hom f s.val) ≫ R.map (Subdiagram.rightInclusion f s.val)
    rw [← R.map_comp, ← R.map_comp]
    exact congrArg R.map (Subdiagram.inclusion f s.val).w
  have sq : CommSq b.hom β.left β.right (R.map f) := ⟨β.w.symm⟩
  obtain ⟨s, l, r, hl, hr, hsq⟩ := IsCardinalPresentable.exists_commSq_of_isColimit
    μ τ hcL hcR (R.map f) hτ sq
  let α : b ⟶ R.mapArrow.obj (Subdiagram.arrow f s.val) :=
    Arrow.homMk l r hsq.w.symm
  have hwhole : α ≫ R.mapArrow.map (Subdiagram.inclusion f s.val) = β := by
    apply Arrow.hom_ext
    · exact hl
    · exact hr
  exact ⟨s, α, hwhole, hl, hr, α.w⟩

/-- The same strict support can absorb any prescribed original small seed. -/
theorem exists_originalLocalCellSupport_above
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (h : (originalLocalCellData S).κ ≤ μ)
    (b : Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    [IsCardinalPresentable b.left μ] [IsCardinalPresentable b.right μ]
    (β : b ⟶ (originalLocalCellReplacement S).mapArrow.obj (Arrow.mk f))
    (s₀ : cardinalSubarrowIndex f μ) :
    ∃ (s : cardinalSubarrowIndex f μ)
      (α : b ⟶ (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val)),
      s₀ ≤ s ∧
      α ≫ (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f s.val) = β ∧
      α.left ≫ (originalLocalCellReplacement S).map (Subdiagram.leftInclusion f s.val) =
        β.left ∧
      α.right ≫ (originalLocalCellReplacement S).map (Subdiagram.rightInclusion f s.val) =
        β.right ∧
      α.left ≫ (originalLocalCellReplacement S).map (Subdiagram.hom f s.val) =
        b.hom ≫ α.right := by
  let R := originalLocalCellReplacement S
  obtain ⟨hΩ, _⟩ := originalLocalCellSupport_profile S μ h
  obtain ⟨s, α, hwhole, _, _, _⟩ := exists_originalLocalCellSupport S μ h b f β
  let family : Fin 2 → cardinalSubarrowIndex f μ := fun n => if n = 0 then s else s₀
  have hFinite : HasCardinalLT (Fin 2) μ := hasCardinalLT_of_finite _ _ hΩ.le
  let t := cardinalSubarrowUnion f μ family hFinite
  have hs : s ≤ t := by
    simpa only [family, ite_eq_left rfl] using le_cardinalSubarrowUnion f μ family hFinite 0
  have hseed : s₀ ≤ t := by
    simpa only [family, ite_eq_right (one_ne_zero : (1 : Fin 2) ≠ 0)] using
      le_cardinalSubarrowUnion f μ family hFinite 1
  let α' : b ⟶ R.mapArrow.obj (Subdiagram.arrow f t.val) :=
    α ≫ R.mapArrow.map (Subdiagram.map f hs)
  have hwhole' : α' ≫ R.mapArrow.map (Subdiagram.inclusion f t.val) = β := by
    dsimp only [α']
    rw [Category.assoc, ← R.mapArrow.map_comp, Subdiagram.map_inclusion, hwhole]
  exact ⟨t, α', hseed, hwhole', congrArg Arrow.Hom.left hwhole',
    congrArg Arrow.Hom.right hwhole', α'.w⟩

end SimplicialPresheaf.InjectiveKan
