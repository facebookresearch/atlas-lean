/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDualBarrierAuxiliary



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section




theorem exists_fkRectForceDualPullbackUnitPattern_localizedVerticalWalk
    (R : FKRectTorus) (right : Nat) (hright : 1 <= right)
    (omega : R.Configuration)
    (t : Finset
      (FKRectColumnBandVertex R 1 right 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 right 1 (R.height - 1)))
    (hspans : FKRectColumnBandConnectionChainSpans R 1 right
      (fkRectUnitGapColumn R) (by rfl) hright t)
    (haux : fkRectUnitDualBarrierAuxiliary R right t omega) :
    let forced := fkRectForceIndexedPattern R
      (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
      (fkRectDualPullbackConfiguration R
        (fkRectAllButOneOpenConfiguration R
          (fkRectUnitLeftBarrierGap R))) omega
    ∃ w : (fkRectOpenGraph R forced).Walk
        (fkRectRowOneVertex R (fkRectUnitGapColumn R))
        (fkRectLastRowVertex R (fkRectUnitGapColumn R)),
      ∀ v ∈ w.support,
        1 <= v.1.val ∧ v.1.val <= right ∧
          1 <= v.2.val ∧ v.2.val <= R.height - 1 := by
  dsimp only
  let eta := fkRectDualPullbackConfiguration R
    (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))
  let forced := fkRectForceIndexedPattern R
    (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) eta omega
  let S := fkRectColumnBand R 1 right 1 (R.height - 1)
  let sigma := FK.ocd_innerRestrict
    (Subtype.val : FKRectInducedVertex R S -> R.Vertex)
    (fkRectFullGraphConfiguration R forced)
  have hchain : sigma ∈ fkRectInducedConnectionChainEvent R S t := by
    exact fkRectForceDualPullbackSeam_preserves_columnBand_chain
      R 1 right 1 (R.height - 1) (by rfl) eta omega t haux.1
  have hreach := hspans sigma hchain
  obtain ⟨w⟩ := hreach
  let f : FK.openSub (fkRectInducedGraph R S) sigma →g
      fkRectOpenGraph R forced :=
    { toFun := Subtype.val
      map_rel' := by
        intro u v huv
        rw [← fkOpenSub_fullGraphConfiguration R forced]
        constructor
        · exact huv.1
        · simpa [sigma, FK.ocd_innerRestrict,
            FK.ocd_innerEdge_mk] using huv.2 }
  let W := w.map f
  refine ⟨W, ?_⟩
  intro v hv
  have hsupp := SimpleGraph.Walk.support_map f w
  obtain ⟨u, hu, huv⟩ := List.mem_map.mp (hsupp ▸ hv)
  have hvS : v ∈ S := huv ▸ u.2
  exact hvS

end

end StatMech.FrontierD
