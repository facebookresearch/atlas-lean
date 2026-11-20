/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianPhysicalCumulants





open Filter Finset Topology

namespace StatMech.FrontierA

theorem tendsto_scalarCumulantsOfMoments
    (moments : Nat → Nat → Real) (limitMoments : Nat → Real)
    (hmoments : ∀ order,
      Tendsto (fun scale => moments scale order) atTop
        (nhds (limitMoments order))) :
    ∀ order,
      Tendsto
        (fun scale => scalarCumulantsOfMoments (moments scale) order)
        atTop (nhds (scalarCumulantsOfMoments limitMoments order)) := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      cases order with
      | zero => simp
      | succ n =>
          have hsum : Tendsto
              (fun scale => ∑ k : Fin n,
                (n.choose k : Real) *
                  scalarCumulantsOfMoments (moments scale) (k + 1) *
                    moments scale (n - k))
              atTop
              (nhds (∑ k : Fin n,
                (n.choose k : Real) *
                  scalarCumulantsOfMoments limitMoments (k + 1) *
                    limitMoments (n - k))) := by
            apply tendsto_finsetSum
            intro k hk
            exact (tendsto_const_nhds.mul
              (ih (k + 1) (by omega))).mul (hmoments (n - k))
          have hlimit := (hmoments (n + 1)).sub hsum
          have hfun :
              (fun scale => scalarCumulantsOfMoments (moments scale) (n + 1)) =
                fun scale => moments scale (n + 1) - ∑ k : Fin n,
                  (n.choose k : Real) *
                    scalarCumulantsOfMoments (moments scale) (k + 1) *
                      moments scale (n - k) := by
            funext scale
            rw [scalarCumulantsOfMoments_succ]
          rw [hfun, scalarCumulantsOfMoments_succ]
          exact hlimit

end StatMech.FrontierA
