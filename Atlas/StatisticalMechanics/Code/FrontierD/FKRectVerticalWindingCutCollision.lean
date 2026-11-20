/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectVerticalWindingCutUnits
import Code.FrontierD.FKRectVerticalWindingPrimitiveArithmetic
import Code.FrontierD.FKRectHorizontalCylinderPlanarization












open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkRectOpenGraph_forceHorizontalCutClosed_le_horizontalCylinderGraph
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega) ≤
      fkRectHorizontalCylinderGraph R := by
  let eta : FKRectHorizontalCutClosedConfig R :=
    ⟨fkRectForceHorizontalCutClosed R omega,
      fkRectHorizontalCutClosedConfiguration_force R omega⟩
  intro x y hxy
  have hopen :
      (FK.openSub (fkRectHorizontalCylinderGraph R)
        (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1).Adj x y := by
    rw [fkRectHorizontalCylinder_openSub_eq R eta]
    exact hxy
  rw [FK.openSub_adj] at hopen
  exact hopen.1



theorem fkRectForceHorizontalCutClosedWalk_winding_snd_eq_zero
    (R : FKRectTorus) (omega : R.Configuration) {x y : R.Vertex}
    (p : (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).Walk x y) :
    (fkRectWalkWinding R p).2 = 0 := by
  let q := p.mapLe
    (fkRectOpenGraph_forceHorizontalCutClosed_le_horizontalCylinderGraph
      R omega)
  have hq := fkRectHorizontalCylinderWalk_winding_snd_eq_zero R q
  rw [fkRectWalkWinding_mapLe R
    (fkRectOpenGraph_forceHorizontalCutClosed_le_horizontalCylinderGraph
      R omega) p] at hq
  exact hq



theorem exists_closedWalk_winding_snd_eq_of_horizontalCutComponent_eq
    (R : FKRectTorus) (omega : R.Configuration) {x y : R.Vertex}
    (p : (fkRectOpenGraph R omega).Walk x y)
    (hxy :
      (fkRectOpenGraph R
          (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk x =
        (fkRectOpenGraph R
          (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk y) :
    ∃ q : (fkRectOpenGraph R omega).Walk x x,
      (fkRectWalkWinding R q).2 = (fkRectWalkWinding R p).2 := by
  obtain ⟨r⟩ := ConnectedComponent.exact hxy.symm
  let r' := r.mapLe (fkRectOpenGraph_forceHorizontalCutClosed_le R omega)
  refine ⟨p.append r', ?_⟩
  rw [fkRectWalkWinding_append]
  have hr : (fkRectWalkWinding R r').2 = 0 := by
    rw [fkRectWalkWinding_mapLe R
      (fkRectOpenGraph_forceHorizontalCutClosed_le R omega) r]
    exact fkRectForceHorizontalCutClosedWalk_winding_snd_eq_zero R omega r
  simp only [Prod.snd]
  rw [hr, add_zero]



theorem FKRectPrimalComponentHasNet.of_closedWalks
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    {x y : R.Vertex}
    (hx : (fkRectOpenGraph R omega).connectedComponentMk x = K)
    (hy : (fkRectOpenGraph R omega).connectedComponentMk y = K)
    (p : (fkRectOpenGraph R omega).Walk x x)
    (q : (fkRectOpenGraph R omega).Walk y y)
    (hind : FKRectWindingIndependent
      (fkRectWalkWinding R p) (fkRectWalkWinding R q)) :
    FKRectPrimalComponentHasNet R omega K := by
  obtain ⟨rx⟩ := ConnectedComponent.exact (K.out_eq.trans hx.symm)
  obtain ⟨ry⟩ := ConnectedComponent.exact (K.out_eq.trans hy.symm)
  let p' := (rx.append p).append rx.reverse
  let q' := (ry.append q).append ry.reverse
  refine ⟨p', q', ?_⟩
  rw [fkRectWalkWinding_conjugate, fkRectWalkWinding_conjugate]
  exact hind





theorem fkRectPrimalComponentHasNet_of_primitiveBoundary_cutCollision
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (d : FKMedialBlackDart R.medialTorus)
    (hdK : (fkRectOpenGraph R omega).connectedComponentMk
      (fkRectMedialDartPrimalLabel R d.1) = K)
    (hprimitive : FKRectPrimitiveWinding
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)))
    {x y : R.Vertex} (p : (fkRectOpenGraph R omega).Walk x y)
    (hxK : (fkRectOpenGraph R omega).connectedComponentMk x = K)
    (hxy :
      (fkRectOpenGraph R
          (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk x =
        (fkRectOpenGraph R
          (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk y)
    (hboundary : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (hpath : 0 < (fkRectWalkWinding R p).2)
    (hstrict : (fkRectWalkWinding R p).2 <
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2) :
    FKRectPrimalComponentHasNet R omega K := by
  obtain ⟨q, hq⟩ :=
    exists_closedWalk_winding_snd_eq_of_horizontalCutComponent_eq
      R omega p hxy
  have hind : FKRectWindingIndependent
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d))
      (fkRectWalkWinding R q) := by
    apply windingIndependent_of_primitive_of_snd_between hprimitive hboundary
    · simpa [hq] using hpath
    · simpa [hq] using hstrict
  exact FKRectPrimalComponentHasNet.of_closedWalks R omega K
    hdK hxK (fkRectBlackBoundaryPrimalCycleWalk R omega d) q hind

end

end StatMech.FrontierD
