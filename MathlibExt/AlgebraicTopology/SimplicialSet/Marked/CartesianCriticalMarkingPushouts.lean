/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SelectedEdgeMarkingPushout

/-!
# Both original critical source and target marking pushouts

The complete original terminal horn and standard simplex gain the same
original final edge. Their actual marking pushouts retain that edge's
whole Yoneda map, all original degeneracies and the entire original horn
inclusion between the two cocones. No native image or weak class is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The marked target's selected edge is the actual image of the original critical horn edge. -/
def cartesianCriticalImageEdge (n : ℕ) : (Δ[n + 2] : SSet.{u}) _⦋1⦌ :=
  (horn (n + 2) (Fin.last (n + 2))).ι.app (op ⦋1⦌) (rightHornEdgeSimplex n)

/-- The original critical source gains its edge by the whole marked interval leg. -/
def cartesianCriticalSourceSharpLeg (n : ℕ) :
    max (Δ[1] : SSet.{u}) ⟶ cartesianCriticalSource n :=
  selectedEdgeSharpLeg (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (rightHornEdgeSimplex n)

/-- The same full horn carrier is the source's original minimal marking leg. -/
def cartesianCriticalSourceMinimalLeg (n : ℕ) :
    min (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ cartesianCriticalSource n :=
  selectedEdgeMinimalLeg (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (rightHornEdgeSimplex n)

/-- The actual image critical edge gives the complete sharp leg into the original target. -/
def cartesianCriticalTargetSharpLeg (n : ℕ) :
    max (Δ[1] : SSet.{u}) ⟶ cartesianCriticalTarget n :=
  selectedEdgeSharpLeg (Δ[n + 2] : SSet.{u}) (cartesianCriticalImageEdge n)

/-- The entire original simplex is the target's exact minimal marking leg. -/
def cartesianCriticalTargetMinimalLeg (n : ℕ) :
    min (Δ[n + 2] : SSet.{u}) ⟶ cartesianCriticalTarget n :=
  selectedEdgeMinimalLeg (Δ[n + 2] : SSet.{u}) (cartesianCriticalImageEdge n)

/-- The whole original critical horn has its actual selected-edge marking pushout cocone. -/
def cartesianCriticalSourceMarkingCocone (n : ℕ) :
    PushoutCocone edgeMarkCell
      (selectedEdgeMinimalMap (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (rightHornEdgeSimplex n)) :=
  selectedEdgeMarkingCocone (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (rightHornEdgeSimplex n)

/-- The complete ORIGINAL marked critical source is the genuine full marking pushout. -/
def cartesianCriticalSourceMarkingIsColimit (n : ℕ) :
    IsColimit (cartesianCriticalSourceMarkingCocone.{u} n) :=
  selectedEdgeMarkingIsColimit (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (rightHornEdgeSimplex n)

/-- The whole original critical target has the marking pushout of the SAME original edge image. -/
def cartesianCriticalTargetMarkingCocone (n : ℕ) :
    PushoutCocone edgeMarkCell
      (selectedEdgeMinimalMap (Δ[n + 2] : SSet.{u}) (cartesianCriticalImageEdge n)) :=
  selectedEdgeMarkingCocone (Δ[n + 2] : SSet.{u}) (cartesianCriticalImageEdge n)

/-- The complete ORIGINAL marked critical target is its actual full marking pushout. -/
def cartesianCriticalTargetMarkingIsColimit (n : ℕ) :
    IsColimit (cartesianCriticalTargetMarkingCocone.{u} n) :=
  selectedEdgeMarkingIsColimit (Δ[n + 2] : SSet.{u}) (cartesianCriticalImageEdge n)

/-- The sharp source and target legs retain the SAME original critical edge through the full horn inclusion. -/
theorem cartesianCriticalSharpLeg_cell (n : ℕ) :
    cartesianCriticalSourceSharpLeg n ≫ cartesianCriticalCell n =
      cartesianCriticalTargetSharpLeg.{u} n := by
  apply Hom.ext
  change SSet.yonedaEquiv.symm (rightHornEdgeSimplex n) ≫
    (horn (n + 2) (Fin.last (n + 2))).ι = SSet.yonedaEquiv.symm (cartesianCriticalImageEdge n)
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- Both full minimal carriers retain the actual original critical horn inclusion. -/
theorem cartesianCriticalMinimalLeg_cell (n : ℕ) :
    cartesianCriticalSourceMinimalLeg n ≫ cartesianCriticalCell n =
      minimal.map (horn (n + 2) (Fin.last (n + 2))).ι ≫
        cartesianCriticalTargetMinimalLeg.{u} n := by
  apply Hom.ext
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The entire original minimal edge maps commute with the same whole horn inclusion. -/
theorem cartesianCriticalMinimalEdge_cell (n : ℕ) :
    selectedEdgeMinimalMap (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (rightHornEdgeSimplex n) ≫
      minimal.map (horn (n + 2) (Fin.last (n + 2))).ι =
        selectedEdgeMinimalMap (Δ[n + 2] : SSet.{u}) (cartesianCriticalImageEdge n) := by
  apply Hom.ext
  have h := congrArg Hom.hom (cartesianCriticalSharpLeg_cell.{u} n)
  exact h

end SSet.Marked
