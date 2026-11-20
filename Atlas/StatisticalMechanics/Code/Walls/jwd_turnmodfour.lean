/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Code.Lattice.TurningNumber
import Code.Lattice.NoDiagTouchClose

open SimpleGraph Function

namespace StatMech.Walls

open StatMech.Lattice














theorem jwd_cumTurn_eq_zero_of_closes (K : Set (Site 2)) (e : Dart) (p : ℕ)
    (hclose : (dartNext K)^[p] e = e) :
    cumTurn K e p = 0 :=
  cumTurn_eq_zero_of_iterate_eq K e p hclose




theorem jwd_four_dvd_totalTurn_of_closes (K : Set (Site 2)) (e : Dart) (p : ℕ)
    (hclose : (dartNext K)^[p] e = e) :
    (4 : ℤ) ∣ totalTurnZ K e p :=
  four_dvd_totalTurnZ_of_iterate_eq K e p hclose




















theorem jwd_four_dvd_orbit_totalTurn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) :=
  four_dvd_orbit_totalTurnZ K a



theorem jwd_orbit_cumTurn_eq_zero (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    cumTurn K a.1 (dartOrbitPeriod K a) = 0 :=
  dartOrbitPeriod_cumTurn_eq_zero K a




theorem jwd_orbit_turn_eq_four_mul (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    ∃ k : ℤ, totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * k :=
  jwd_four_dvd_orbit_totalTurn K a













theorem jwd_starHull_four_dvd_orbit_totalTurn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    (4 : ℤ) ∣ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) :=
  jwd_four_dvd_orbit_totalTurn (ndt_StarHull K) a





theorem jwd_box_four_dvd_orbit_totalTurn (n : ℕ)
    (a : {e : Dart // IsBoundaryDart (box 2 n) e}) :
    (4 : ℤ) ∣ totalTurnZ (box 2 n) a.1 (dartOrbitPeriod (box 2 n) a) :=
  jwd_four_dvd_orbit_totalTurn (box 2 n) a












theorem jwd_four_dvd_of_fullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : TurningIsFullRevolution K a) :
    (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  rcases h with h | h
  · exact ⟨1, by rw [h]; ring⟩
  · exact ⟨-1, by rw [h]; ring⟩

end StatMech.Walls
