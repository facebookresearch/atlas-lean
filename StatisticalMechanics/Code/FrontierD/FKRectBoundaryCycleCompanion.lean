/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectPrimalBoundaryFiberWinding



namespace StatMech.FrontierD

noncomputable section




theorem exists_other_nonzero_blackBoundaryCycle_in_primalCluster
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (C : FKRectConfigurationBlackBoundaryCycle R omega)
    (hCcluster : fkRectBlackBoundaryCycleInPrimalCluster R omega x C)
    (hCne : fkRectBlackBoundaryCycleWinding R omega C ≠ 0) :
    ∃ D : FKRectConfigurationBlackBoundaryCycle R omega,
      D ≠ C ∧
        fkRectBlackBoundaryCycleInPrimalCluster R omega x D ∧
        fkRectBlackBoundaryCycleWinding R omega D ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hsingle : fkRectPrimalClusterBoundaryCycleWindingSum R omega x =
      fkRectBlackBoundaryCycleWinding R omega C := by
    unfold fkRectPrimalClusterBoundaryCycleWindingSum
    rw [Finset.sum_eq_single C]
    · simp [hCcluster]
    · intro D _ hDC
      by_cases hDcluster :
          fkRectBlackBoundaryCycleInPrimalCluster R omega x D
      · have hDzero : fkRectBlackBoundaryCycleWinding R omega D = 0 := by
          exact hnone D hDC hDcluster
        simp [hDcluster, hDzero]
      · simp [hDcluster]
    · simp
  have hzero := fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero
    R omega x
  rw [hsingle] at hzero
  exact hCne hzero

end

end StatMech.FrontierD
