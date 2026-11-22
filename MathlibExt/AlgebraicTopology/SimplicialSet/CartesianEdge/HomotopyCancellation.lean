/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.CancellationHorn
import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeSpecialOuterHornOpposite

/-!
# Homotopy cancellation through a Cartesian edge over an equivalence

The three original triangles form a right outer three-horn. The existing
special outer-horn theorem fills its actual base horn because the critical
base edge is an equivalence. The Cartesian critical-edge theorem lifts
that same prescribed simplex. Its final face is the required homotopy to
the original identity.
-/

noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CartesianEdge

/-- A specified endomorphism acting trivially before this Cartesian edge is the identity in Ho. -/
theorem toHoHom_eq_id_of_compStruct {X B : SSet.{u}} (p : X ⟶ B) [Quasicategory B]
    {x y : X _⦋0⦌} (e : Edge x y) (he : IsPCartesian p (yonedaEquiv.symm e.edge))
    (heB : (e.map p).IsEquivalence) (h : Edge x x) (H : Edge.CompStruct h e e) :
    h.toHoHom = 𝟙 (HomotopyCategory.mk x : hoFunctor.obj X) := by
  let σ₀ := cancellationHorn H
  have hc : (rightHornEdge σ₀).edge = e.edge := cancellationHorn_edge H
  have hcB : (rightHornEdge (σ₀ ≫ p)).edge = (e.map p).edge := by
    rw [rightHornEdge_edge, comp_app, Edge.map_edge]
    exact congrArg (p.app (op ⦋1⦌)) hc
  have hbEq : (rightHornEdge (σ₀ ≫ p)).IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq hcB).mpr heB
  obtain ⟨b, hb⟩ := exists_fill_horn_right_of_isEquivalence (σ₀ ≫ p) hbEq
  have hp₀ : IsPCartesian p (yonedaEquiv.symm (rightHornEdge σ₀).edge) :=
    (congrArg yonedaEquiv.symm hc).symm ▸ he
  obtain ⟨T, hT, -⟩ := exists_fill_rightHorn_of_isPCartesian σ₀ b hb hp₀
  exact toHoHom_eq_id_of_cancellationHorn_fill H T hT

end SSet.CartesianEdge
