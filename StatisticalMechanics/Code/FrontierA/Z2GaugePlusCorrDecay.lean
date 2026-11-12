/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Sharpness.IsingSharpnessUnconditional
import Code.Sharpness.IsingSusceptibilityPlus
import Code.Sharpness.IsingExponentialPlus









namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice
  StatMech.Percolation

noncomputable section




theorem plusCorr_allPairs_exponential_of_lt_betaC
    {d : Nat} (hd : 2 <= d) {beta : Real}
    (hbeta : 0 <= beta) (hlt : beta < betaC d) :
    exists c, 0 < c /\ forall x y : Site d,
      plusCorr d beta x y <= Real.exp (-c * (l1dist d x y : Real)) := by
  obtain ⟨c, hc, hdecay⟩ :=
    (ising_sharpness_unconditional (d := d) hd).2.2 beta hbeta hlt
  refine ⟨c, hc, fun x y => ?_⟩
  rw [plusCorr_eq_origin_translate beta hbeta]
  have h := hdecay (y - x)
  rw [l1dist_origin_sub (d := d) y x] at h
  exact h

end

end StatMech.FrontierA
