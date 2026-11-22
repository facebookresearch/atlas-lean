/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.CancellationHorn
import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeSpecialOuterHornOpposite

/-!
# Cancellation after a cocartesian edge over an equivalence

The original left outer cancellation horn has an equivalence as its
critical base edge. The existing base filler and the intrinsic cocartesian
lift produce the same identity face in the original homotopy category.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CocartesianEdge

/-- An endomorphism acting trivially after this cocartesian edge is the identity in Ho. -/
theorem toHoHom_eq_id_of_compStruct {X B : SSet.{u}} (p : X ⟶ B) [Quasicategory B]
    {x y : X _⦋0⦌} (e : Edge x y) (he : IsPCocartesian p (yonedaEquiv.symm e.edge))
    (heB : (e.map p).IsEquivalence) (h : Edge y y) (H : Edge.CompStruct e h e) :
    h.toHoHom = 𝟙 (HomotopyCategory.mk y : hoFunctor.obj X) := by
  let σ₀ := cancellationHorn H
  have hc : (leftHornEdge σ₀).edge = e.edge := cancellationHorn_edge H
  have hcB : (leftHornEdge (σ₀ ≫ p)).edge = (e.map p).edge := by
    rw [leftHornEdge_edge, comp_app, Edge.map_edge]
    exact congrArg (p.app (op ⦋1⦌)) hc
  have hbEq : (leftHornEdge (σ₀ ≫ p)).IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq hcB).mpr heB
  obtain ⟨b, hb⟩ := exists_fill_horn_left_of_isEquivalence (σ₀ ≫ p) hbEq
  have hp₀ : IsPCocartesian p (yonedaEquiv.symm (leftHornEdge σ₀).edge) :=
    (congrArg yonedaEquiv.symm hc).symm ▸ he
  obtain ⟨T, hT, -⟩ := exists_fill_leftHorn_of_isPCocartesian σ₀ b hb hp₀
  exact toHoHom_eq_id_of_cancellationHorn_fill H T hT

end SSet.CocartesianEdge
