/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalBoundaryComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverInitialMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterMonomorphisms
import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationData

/-!
# Actual marked slice trivial-fibration sections are strong deformations

The full native relative boundary corner is monic through its actual
scalar product comparison. The original mono-right map therefore lifts
that whole boundary with the given section cylinder kept stationary.
The original strict retraction, both complete endpoints and the full
original base triangle are retained. No marked adhesivity, Kan base or
marked model hypothesis is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.Precylinder

namespace SSet.Marked

/-- The complete original fixed-base interval boundary corner of every marked mono is genuinely monic. -/
theorem relativeIntervalBoundaryCorner_mono {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) [Mono f] :
    Mono ((relativeIntervalCylinder Z).boundaryCorner f) := by
  let _ : Mono relativeIntervalWholeBoundary.{u} := relativeIntervalWholeBoundary_mono
  let _ : Mono (overParameterPushoutProduct relativeIntervalWholeBoundary.{u} f) :=
    overParameterPushoutProduct_mono _ f
  exact ((monomorphisms (Over Z)).arrow_iso_iff (relativeIntervalBoundaryCornerIso f)).mp
    (show Mono (overParameterPushoutProduct relativeIntervalWholeBoundary.{u} f) from
      overParameterPushoutProduct_mono _ f)

/-- Every given section of an original mono-right map has the whole native relative strong deformation with
  the same retraction and base map. -/
theorem relativeIntervalStrongDeformation_of_section {Z : Marked.{u}} {X Y : Over Z}
    (p : X ⟶ Y) (hp : (monomorphisms (Over Z)).rlp p) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) :
    ∃ D : (relativeIntervalCylinder Z).StrongDeformationData s,
      D.retraction = p ∧ D.homotopy.h ≫ p = ((relativeIntervalCylinder Z).app X).π ≫ p := by
  let P := relativeIntervalCylinder Z
  let _ : P.IsExact.{u} := relativeIntervalCylinder_isExact Z
  have : Mono s := (SplitEpi.splitMono (⟨s, hs⟩ : SplitEpi p)).mono
  have overlap : coprod.map s s ≫ coprod.desc (𝟙 X) (p ≫ s) =
      (P.app Y).i ≫ ((P.app Y).π ≫ s) := by
    apply coprod.hom_ext
    · calc
        coprod.inl ≫ (coprod.map s s ≫ coprod.desc (𝟙 X) (p ≫ s)) = s := by
          rw [coprod.inl_map_assoc, coprod.inl_desc, Category.comp_id]
        _ = coprod.inl ≫ ((P.app Y).i ≫ ((P.app Y).π ≫ s)) := by
          rw [← Category.assoc, (P.app Y).inl_i, ← Category.assoc,
            (P.app Y).i₀_π, Category.id_comp]
    · calc
        coprod.inr ≫ (coprod.map s s ≫ coprod.desc (𝟙 X) (p ≫ s)) = s := by
          rw [coprod.inr_map_assoc, coprod.inr_desc, ← Category.assoc, hs, Category.id_comp]
        _ = coprod.inr ≫ ((P.app Y).i ≫ ((P.app Y).π ≫ s)) := by
          rw [← Category.assoc, (P.app Y).inr_i, ← Category.assoc,
            (P.app Y).i₁_π, Category.id_comp]
  let top := pushout.desc (coprod.desc (𝟙 X) (p ≫ s)) ((P.app Y).π ≫ s) overlap
  let bottom := (P.app X).π ≫ p
  have sq : CommSq top (P.boundaryCorner s) p bottom := by
    constructor
    apply pushout.hom_ext
    · rw [← Category.assoc (pushout.inl (coprod.map s s) (P.app Y).i) top p]
      rw [show pushout.inl (coprod.map s s) (P.app Y).i ≫ top =
        coprod.desc (𝟙 X) (p ≫ s) from pushout.inl_desc ..]
      rw [inl_boundaryCorner_assoc]
      apply coprod.hom_ext
      · calc
          coprod.inl ≫ (coprod.desc (𝟙 X) (p ≫ s) ≫ p) = p := by
            rw [coprod.inl_desc_assoc, Category.id_comp]
          _ = coprod.inl ≫ ((P.app X).i ≫ bottom) := by
            dsimp only [bottom]
            rw [← Category.assoc, (P.app X).inl_i, ← Category.assoc,
              (P.app X).i₀_π, Category.id_comp]
      · calc
          coprod.inr ≫ (coprod.desc (𝟙 X) (p ≫ s) ≫ p) = p := by
            rw [coprod.inr_desc_assoc, Category.assoc, hs, Category.comp_id]
          _ = coprod.inr ≫ ((P.app X).i ≫ bottom) := by
            dsimp only [bottom]
            rw [← Category.assoc, (P.app X).inr_i, ← Category.assoc,
              (P.app X).i₁_π, Category.id_comp]
    · rw [← Category.assoc (pushout.inr (coprod.map s s) (P.app Y).i) top p]
      rw [show pushout.inr (coprod.map s s) (P.app Y).i ≫ top =
        (P.app Y).π ≫ s from pushout.inr_desc ..]
      rw [inr_boundaryCorner_assoc]
      change ((P.app Y).π ≫ s) ≫ p = P.I.map s ≫ ((P.app X).π ≫ p)
      simpa only [Functor.id_map, Category.assoc] using
        congrArg (· ≫ p) (P.π.naturality s).symm
  have : HasLiftingProperty (P.boundaryCorner s) p := hp _ (relativeIntervalBoundaryCorner_mono s)
  have boundary_eq : (P.app X).i ≫ sq.lift = coprod.desc (𝟙 X) (p ≫ s) := by
    have h := congrArg (pushout.inl (coprod.map s s) (P.app Y).i ≫ ·) sq.fac_left
    simpa only [inl_boundaryCorner_assoc, top, pushout.inl_desc] using h
  have stationary : P.I.map s ≫ sq.lift = (P.app Y).π ≫ s := by
    have h := congrArg (pushout.inr (coprod.map s s) (P.app Y).i ≫ ·) sq.fac_left
    simpa only [inr_boundaryCorner_assoc, top, pushout.inr_desc] using h
  refine ⟨{ retraction := p, retract := hs, homotopy :=
    { h := sq.lift, h₀ := ?_, h₁ := ?_, stationary := ?_ } }, rfl, sq.fac_right⟩
  · have h := congrArg ((coprod.inl : X ⟶ X ⨿ X) ≫ ·) boundary_eq
    simpa only [← Category.assoc, (P.app X).inl_i, coprod.inl_desc] using h
  · have h := congrArg ((coprod.inr : X ⟶ X ⨿ X) ≫ ·) boundary_eq
    simpa only [← Category.assoc, (P.app X).inr_i, coprod.inr_desc] using h
  · simpa only [Category.comp_id] using stationary

end SSet.Marked
