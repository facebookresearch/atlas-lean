/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalOddAveragedDensityEndpoints





namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem tendsto_sixVertexCanonicalOddAveragedDensityHalfCell
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      let N := sixVertexFourWidth (2 * s + 1) k
      let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
      let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
      let F := sixVertexBetheCountingFunction c N n p
      2 * ∑ j : Fin (s + k + 1),
        (Real.log (F (sixVertexCanonicalOddMidpointHalfRoot hc s k j) /
            sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
          Real.log (F (sixVertexCanonicalOddLeftHalfRoot hc s k j) /
            sixVertexCanonicalOddLeftHalfRoot hc s k j)))
      atTop
      (nhds (Real.log (1 / (4 * Real.pi)) -
        Real.log (sixVertexFourierPhysicalDensity c hc 0))) := by
  simpa [sixVertexCanonicalOddCountingAverage] using
    tendsto_sixVertexCanonicalOddAveragedDensityHalfIncrement hc s

end

end StatMech.FrontierD
