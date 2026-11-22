/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalPointFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverFibrationCells
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.StandardEndpointFibrations

/-!
# Original interval endpoints in the auxiliary marked-cell right classes

The fully marked source endpoint is the native Cartesian fibration over
the ordered interval, and its target endpoint is the dual cocartesian
fibration. Every original point-source edge is degenerate, so its maximal
marking is exactly the intrinsic relative marking. The actual cell-right
criteria put these original maps in the auxiliary right classes over the
point. This does not assert that they are genuine marked model fibrations.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem point_edge_degenerate (e : (Δ[0] : SSet.{u}) _⦋1⦌) :
    ∃ x : (Δ[0] : SSet.{u}) _⦋0⦌, (Δ[0] : SSet.{u}).σ (0 : Fin 1) x = e := by
  refine ⟨(Δ[0] : SSet.{u}).δ (1 : Fin 2) e, ?_⟩
  apply SSet.yonedaEquiv.symm.injective
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The same fully marked source endpoint lies in the actual Cartesian marked-cell right class. -/
theorem pointSourceEndpoint_cartesianCellRight :
    cartesianCells.{u}.rlp (maximal.map (SSet.stdSimplex.{u}.δ (1 : Fin 2))) := by
  let p : max (Δ[0] : SSet.{u}) ⟶ max (Δ[1] : SSet.{u}) := maximal.map (SSet.stdSimplex.δ 1)
  let _ : CartesianFibration p.hom := SSet.stdSimplex.sourceEndpoint_cartesianFibration
  let _ : CartesianFibration (Over.mk p).hom.hom := SSet.stdSimplex.sourceEndpoint_cartesianFibration
  let _ : Quasicategory (max (Δ[1] : SSet.{u})).toSSet := inferInstanceAs (Quasicategory (Δ[1] : SSet.{u}))
  apply (cartesianCells_rlp_iff_cartesianObjects p).mpr
  refine ⟨inferInstance, ?_⟩
  intro e
  refine ⟨fun _ => ?_, fun _ => Set.mem_univ _⟩
  obtain ⟨x, hx⟩ := point_edge_degenerate e
  exact hx ▸ CartesianEdge.isPCartesian_degenerate p.hom x

/-- The original source endpoint is in the auxiliary Cartesian slice cell-right class over the point. -/
theorem pointSourceEndpoint_cartesianAuxiliaryRight :
    (cartesianCellsOver (Δ[0] : SSet.{u})).rlp (pointEndpoint.{u} (1 : Fin 2)) := by
  apply (cartesianCellsOver_rlp_iff _).mpr
  exact pointSourceEndpoint_cartesianCellRight

/-- The same fully marked target endpoint lies in the actual cocartesian marked-cell right class. -/
theorem pointTargetEndpoint_cocartesianCellRight :
    cocartesianCells.{u}.rlp (maximal.map (SSet.stdSimplex.{u}.δ (0 : Fin 2))) := by
  let p : max (Δ[0] : SSet.{u}) ⟶ max (Δ[1] : SSet.{u}) := maximal.map (SSet.stdSimplex.δ 0)
  let _ : CocartesianFibration p.hom := SSet.stdSimplex.targetEndpoint_cocartesianFibration
  let _ : CocartesianFibration (Over.mk p).hom.hom := SSet.stdSimplex.targetEndpoint_cocartesianFibration
  let _ : Quasicategory (max (Δ[1] : SSet.{u})).toSSet := inferInstanceAs (Quasicategory (Δ[1] : SSet.{u}))
  apply (cocartesianCells_rlp_iff_cocartesianObjects p).mpr
  refine ⟨inferInstance, ?_⟩
  intro e
  refine ⟨fun _ => ?_, fun _ => Set.mem_univ _⟩
  obtain ⟨x, hx⟩ := point_edge_degenerate e
  exact hx ▸ CocartesianEdge.isPCocartesian_degenerate p.hom x

/-- The original target endpoint is in the auxiliary cocartesian slice cell-right class over the point. -/
theorem pointTargetEndpoint_cocartesianAuxiliaryRight :
    (cocartesianCellsOver (Δ[0] : SSet.{u})).rlp (pointEndpoint.{u} (0 : Fin 2)) := by
  apply (cocartesianCellsOver_rlp_iff _).mpr
  exact pointTargetEndpoint_cocartesianCellRight

end SSet.Marked
