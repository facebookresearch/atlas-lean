/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.ClusterAdaptiveProjection
import Code.FrontierD.FKRectHorizontalCylinderExploration









open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



def fkRectHorizontalCylinderAdaptiveInsideEdges
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (rho : ConfigSpace (Sym2 R.Vertex)) : Finset (Sym2 R.Vertex) :=
  FK.clusterAdaptiveInsideEdges (fkRectHorizontalCylinderGraph R)
    (fkRectHorizontalCylinderBottomRoots R S) rho


def fkRectHorizontalCylinderAdaptiveProjection
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (rho : ConfigSpace (Sym2 R.Vertex)) : ConfigSpace (Sym2 R.Vertex) :=
  FK.clusterAdaptiveProjection (fkRectHorizontalCylinderGraph R)
    (fkRectHorizontalCylinderBottomRoots R S) rho

theorem fkRectHorizontalCylinderAdaptiveProjection_idem
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectHorizontalCylinderAdaptiveProjection R S
        (fkRectHorizontalCylinderAdaptiveProjection R S rho) =
      fkRectHorizontalCylinderAdaptiveProjection R S rho :=
  FK.clusterAdaptiveProjection_idem (fkRectHorizontalCylinderGraph R)
    (fkRectHorizontalCylinderBottomRoots R S) rho

theorem fkRectHorizontalCylinderAdaptiveInsideEdges_eq_clusterPairs
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectHorizontalCylinderAdaptiveInsideEdges R S rho =
      FK.clusterUnexploredPairEdges (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S) :=
  rfl

theorem fkRectHorizontalCylinderExploredVertex_projection_iff
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (rho : ConfigSpace (Sym2 R.Vertex)) (v : R.Vertex) :
    FKRectHorizontalCylinderExploredVertex R
        (fkRectHorizontalCylinderAdaptiveProjection R S rho) S v ↔
      FKRectHorizontalCylinderExploredVertex R rho S v :=
  FK.clusterExploredVertex_projection_iff
    (fkRectHorizontalCylinderGraph R)
    (fkRectHorizontalCylinderBottomRoots R S) rho v



theorem fkRectHorizontalCylinderSourceReachable_projection_iff
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (rho : ConfigSpace (Sym2 R.Vertex)) {x : Fin R.width} (hx : x ∈ S)
    (v : R.Vertex) :
    (FK.openSub (fkRectHorizontalCylinderGraph R)
        (fkRectHorizontalCylinderAdaptiveProjection R S rho)).Reachable
        (x, fkRectBottomRow R) v ↔
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
        (x, fkRectBottomRow R) v := by
  exact FK.clusterRootReachable_projection_iff
    (fkRectHorizontalCylinderGraph R)
    (fkRectHorizontalCylinderBottomRoots R S)
    rho
    (fkRectHorizontalCylinder_bottomRoot_mem R S hx) v



theorem fkRectHorizontalCylinderDistinctPairedWitness_projection_iff
    (R : FKRectTorus) (pair : Fin R.width → Fin R.width)
    (S : Finset (Fin R.width)) (rho : ConfigSpace (Sym2 R.Vertex)) :
    FKRectHorizontalCylinderDistinctPairedWitness R pair S
        (fkRectHorizontalCylinderAdaptiveProjection R S rho) ↔
      FKRectHorizontalCylinderDistinctPairedWitness R pair S rho := by
  constructor
  · rintro ⟨hpair, hdistinct⟩
    exact ⟨fun x hx =>
        (fkRectHorizontalCylinderSourceReachable_projection_iff
          R S rho hx _).1 (hpair x hx),
      fun x hx y hy hxy hreach => hdistinct x hx y hy hxy
        ((fkRectHorizontalCylinderSourceReachable_projection_iff
          R S rho hx _).2 hreach)⟩
  · rintro ⟨hpair, hdistinct⟩
    exact ⟨fun x hx =>
        (fkRectHorizontalCylinderSourceReachable_projection_iff
          R S rho hx _).2 (hpair x hx),
      fun x hx y hy hxy hreach => hdistinct x hx y hy hxy
        ((fkRectHorizontalCylinderSourceReachable_projection_iff
          R S rho hx _).1 hreach)⟩


theorem fkRectHorizontalCylinderDistinctPairedWitness_fibre_iff
    (R : FKRectTorus) (pair : Fin R.width → Fin R.width)
    (S : Finset (Fin R.width))
    {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hproj : fkRectHorizontalCylinderAdaptiveProjection R S rho =
      fkRectHorizontalCylinderAdaptiveProjection R S sigma) :
    FKRectHorizontalCylinderDistinctPairedWitness R pair S rho ↔
      FKRectHorizontalCylinderDistinctPairedWitness R pair S sigma := by
  rw [← fkRectHorizontalCylinderDistinctPairedWitness_projection_iff
      R pair S rho,
    ← fkRectHorizontalCylinderDistinctPairedWitness_projection_iff
      R pair S sigma,
    hproj]



theorem fkRectHorizontalCylinderAdaptiveProjection_filter_eq_condFibre
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (psi : ConfigSpace (Sym2 R.Vertex))
    (hpsi : fkRectHorizontalCylinderAdaptiveProjection R S psi = psi) :
    Finset.univ.filter
        (fun rho => fkRectHorizontalCylinderAdaptiveProjection R S rho = psi) =
      FK.condFibre
        (fkRectHorizontalCylinderAdaptiveInsideEdges R S psi) psi :=
  FK.clusterAdaptiveProjection_filter_eq_condFibre
    (fkRectHorizontalCylinderGraph R)
    (fkRectHorizontalCylinderBottomRoots R S) psi hpsi


theorem fkRectHorizontalCylinderDistinctPairedWitness_insert_imp_base
    (R : FKRectTorus) (pair : Fin R.width → Fin R.width)
    (S : Finset (Fin R.width)) (x : Fin R.width)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectHorizontalCylinderDistinctPairedWitness
      R pair (insert x S) rho) :
    FKRectHorizontalCylinderDistinctPairedWitness R pair S rho := by
  exact ⟨fun y hy => h.1 y (Finset.mem_insert_of_mem hy),
    fun y hy z hz hyz => h.2 y (Finset.mem_insert_of_mem hy)
      z (Finset.mem_insert_of_mem hz) hyz⟩

end

end StatMech.FrontierD
