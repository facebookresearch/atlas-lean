/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterLowFaceCertificateCore

namespace StatMech.Ising.LowFaceCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in

theorem radializedCrossCoeff_bounds_at_five :
    forall (j k : Fin 8) (t : TriTerm),
      t ∈ (radialize (crossCoeffPoly 5 j k)).terms ->
        t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in

theorem crossCoeff_bounds_at_five :
    forall (j k : Fin 8) (t : TriTerm),
      t ∈ (crossCoeffPoly 5 j k).terms ->
        3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6 := by
  decide

end StatMech.Ising.LowFaceCertificate
