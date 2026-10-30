/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.DVRPoints

/-- Smoke test: the DVR-points theorem applies with `P = 𝒪`. -/
example {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪] : True := by
  have _h := IsLocalRing.exists_fin_points_dvr_iInf_ker_eq_bot (𝒪 := 𝒪) (P := 𝒪)
  trivial
