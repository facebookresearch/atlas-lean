/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectMedialBondLabel

open SimpleGraph

namespace StatMech.FrontierD

@[simp] theorem fkRectMedialDartPrimalLabel_west_vertexOfEdge
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectMedialDartPrimalLabel R
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) =
      fkRectMedialWestPrimal R e := by
  simp [fkRectMedialDartPrimalLabel, fkMedialWestDart]

@[simp] theorem fkRectMedialDartPrimalLabel_east_vertexOfEdge
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectMedialDartPrimalLabel R
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) =
      fkRectMedialEastPrimal R e := by
  simp [fkRectMedialDartPrimalLabel, fkMedialEastDart]



theorem fkRectMedial_adj_primalLabel_reachable
    (R : FKRectTorus) (omega : R.Configuration)
    {d e : FKMedialDart R.medialTorus}
    (hde : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).Adj d e) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R e) := by
  rw [fkMedialLoopGraph_adj_iff] at hde
  rcases hde with hlocal | hbond
  · subst e
    exact fkRectMedialDartPrimalLabel_localMate_reachable R omega d
  · subst e
    rw [fkRectMedialDartPrimalLabel_bondMate]

private theorem fkRectMedial_walk_primalLabel_reachable
    (R : FKRectTorus) (omega : R.Configuration)
    {d e : FKMedialDart R.medialTorus}
    (p : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).Walk d e) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R e) := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons u v w huv p ih =>
      exact (fkRectMedial_adj_primalLabel_reachable R omega huv).trans ih



theorem fkRectMedial_reachable_primalLabel_reachable
    (R : FKRectTorus) (omega : R.Configuration)
    {d e : FKMedialDart R.medialTorus}
    (hde : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).Reachable d e) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R e) := by
  obtain ⟨p⟩ := hde
  exact fkRectMedial_walk_primalLabel_reachable R omega p



theorem fkRectMedial_west_east_not_reachable_of_endpoints
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex)
    {p q : R.Vertex} (hedge : fkRectTorusIndexedEdge R e = s(p, q))
    (hpq : ¬ (fkRectOpenGraph R omega).Reachable p q) :
    ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).Reachable
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) := by
  intro hmedial
  have hprimal := fkRectMedial_reachable_primalLabel_reachable
    R omega hmedial
  simp only [fkRectMedialDartPrimalLabel_west_vertexOfEdge,
    fkRectMedialDartPrimalLabel_east_vertexOfEdge] at hprimal
  have heq : s(p, q) =
      s(fkRectMedialWestPrimal R e, fkRectMedialEastPrimal R e) :=
    hedge.symm.trans (fkRectTorusIndexedEdge_eq_medialPrimals R e)
  rcases Sym2.eq_iff.mp heq with heq | heq
  · exact hpq (by simpa [heq.1, heq.2] using hprimal)
  · exact hpq (by simpa [heq.1, heq.2] using hprimal.symm)

end StatMech.FrontierD
