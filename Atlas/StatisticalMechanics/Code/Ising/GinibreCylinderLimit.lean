/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.GinibreBoundary
import Code.Ising.IsingCylinderTransfer
import Code.Ising.CylinderWidthLimit

open Filter Topology

namespace StatMech.Ising



theorem ginibre_telescope_of_endpoint_tendsto
    (m : Real) (top bottom deficit : Nat -> Real) (D : Real)
    (htop : Tendsto top atTop (nhds m))
    (hbottom : Tendsto bottom atTop (nhds (-m)))
    (hdeficit : Tendsto deficit atTop (nhds D))
    (htelescope : forall N,
      m * (top N - bottom N) <= deficit N) :
    2 * m ^ 2 <= D := by
  have hleft : Tendsto (fun N => m * (top N - bottom N)) atTop
      (nhds (m * (m - -m))) :=
    tendsto_const_nhds.mul (htop.sub hbottom)
  have hle := le_of_tendsto_of_tendsto hleft hdeficit
    (Filter.Eventually.of_forall htelescope)
  nlinarith



theorem ginibre_telescope_endpoint_le_uniform_bound
    (m C : Real) (top bottom deficit : Nat -> Real)
    (htop : Tendsto top atTop (nhds m))
    (hbottom : Tendsto bottom atTop (nhds (-m)))
    (htelescope : forall N,
      m * (top N - bottom N) <= deficit N)
    (hupper : forall N, deficit N <= C) :
    2 * m ^ 2 <= C := by
  have hleft : Tendsto (fun N => m * (top N - bottom N)) atTop
      (nhds (m * (m - -m))) :=
    tendsto_const_nhds.mul (htop.sub hbottom)
  have hbound : forall N, m * (top N - bottom N) <= C :=
    fun N => (htelescope N).trans (hupper N)
  have hle := le_of_tendsto' hleft hbound
  nlinarith




theorem ginibre_widthLimit_lower_bound
    (m energy : Nat -> Real) (M E : Real)
    (hm : Tendsto m atTop (nhds M))
    (henergy : Tendsto energy atTop (nhds E))
    (hlower : forall L, 2 * (m L) ^ 2 <= energy L) :
    2 * M ^ 2 <= E := by
  have hleft : Tendsto (fun L => 2 * (m L) ^ 2) atTop
      (nhds (2 * M ^ 2)) := by
    simpa [pow_two] using tendsto_const_nhds.mul (hm.mul hm)
  exact le_of_tendsto_of_tendsto hleft henergy
    (Filter.Eventually.of_forall hlower)

end StatMech.Ising
