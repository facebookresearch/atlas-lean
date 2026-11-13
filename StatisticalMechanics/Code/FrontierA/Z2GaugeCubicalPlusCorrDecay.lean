/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.Z2GaugePlusCorrDecay
import Code.FrontierA.Z2GaugeCubicalTwoPointLimit
import Code.FrontierA.Z2GaugeTypedFKCylinderGeometry
import Code.FrontierA.Z2GaugeTypedFKInternalCylinder









namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice
  StatMech.Percolation

noncomputable section


def oddCubicalCenteredSite (m : Nat)
    (q : CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :
    Site 3 :=
  (rectangularPrismSiteEquivSctBoxDobrushin m
    (oddCubicalCellEquivPrismSite m q)).1

@[simp] theorem oddCubicalCenteredSite_zero (m : Nat)
    (q : CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :
    oddCubicalCenteredSite m q 0 = (q.x.val : Int) - m := by
  unfold oddCubicalCenteredSite
  rw [rectangularPrismSiteEquivSctBoxDobrushin_apply_zero]
  rfl

@[simp] theorem oddCubicalCenteredSite_one (m : Nat)
    (q : CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :
    oddCubicalCenteredSite m q 1 = (q.y.val : Int) - m := by
  unfold oddCubicalCenteredSite
  rw [rectangularPrismSiteEquivSctBoxDobrushin_apply_one]
  rfl

@[simp] theorem oddCubicalCenteredSite_two (m : Nat)
    (q : CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :
    oddCubicalCenteredSite m q 2 = (m : Int) - q.z.val := by
  unfold oddCubicalCenteredSite
  rw [rectangularPrismSiteEquivSctBoxDobrushin_apply_two]
  rfl

private theorem natAbs_natCast_sub_eq_dist (u v : Nat) :
    ((u : Int) - v).natAbs = Nat.dist u v := by
  apply Int.ofNat_injective
  rw [show Int.ofNat (((u : Int) - v).natAbs) = |(u : Int) - v| from
    Int.natCast_natAbs ((u : Int) - v)]
  by_cases h : u <= v
  · rw [abs_of_nonpos (by omega)]
    simp [Nat.dist, Nat.sub_eq_zero_of_le h]
    exact (Int.ofNat_sub h).symm
  · have h' : v <= u := Nat.le_of_not_ge h
    rw [abs_of_nonneg (by omega)]
    simp [Nat.dist, Nat.sub_eq_zero_of_le h']
    exact (Int.ofNat_sub h').symm



theorem l1dist_oddCubicalCenteredSite
    (m : Nat)
    (q r : CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :
    l1dist 3 (oddCubicalCenteredSite m q)
        (oddCubicalCenteredSite m r) =
      cubicalDualL1 (some q) (some r) := by
  unfold l1dist cubicalDualL1
  rw [Fin.sum_univ_three]
  simp only [oddCubicalCenteredSite_zero, oddCubicalCenteredSite_one,
    oddCubicalCenteredSite_two]
  rw [show ((q.x.val : Int) - m - ((r.x.val : Int) - m)) =
      (q.x.val : Int) - r.x.val by ring,
    show ((q.y.val : Int) - m - ((r.y.val : Int) - m)) =
      (q.y.val : Int) - r.y.val by ring,
    show ((m : Int) - q.z.val - ((m : Int) - r.z.val)) =
      (r.z.val : Int) - q.z.val by ring,
    natAbs_natCast_sub_eq_dist,
    natAbs_natCast_sub_eq_dist,
    natAbs_natCast_sub_eq_dist,
    Nat.dist_comm r.z.val q.z.val]



theorem plusCorr_oddCubical_exponential_of_lt_betaC
    {beta : Real} (hbeta : 0 <= beta) (hlt : beta < betaC 3) :
    exists c, 0 < c /\ forall m (q r :
      CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)),
      plusCorr 3 beta (oddCubicalCenteredSite m q)
          (oddCubicalCenteredSite m r) <=
        Real.exp (-c * (cubicalDualL1 (some q) (some r) : Real)) := by
  obtain ⟨c, hc, hcorr⟩ :=
    plusCorr_allPairs_exponential_of_lt_betaC (d := 3) (by norm_num)
      hbeta hlt
  refine ⟨c, hc, fun m q r => ?_⟩
  rw [← l1dist_oddCubicalCenteredSite m q r]
  exact hcorr _ _

end

end StatMech.FrontierA
