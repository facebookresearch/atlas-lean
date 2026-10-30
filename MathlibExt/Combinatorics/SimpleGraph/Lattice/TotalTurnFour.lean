/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EarContraction
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.GaussBonnet
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHull

/-!
# Total turn `±4` for boundary orbits of star hulls

For a set `K` of sites of `ℤ²`, the boundary orbits of its star hull `ndt_StarHull K` have no
pinches. The lattice Umlaufsatz predicts that each such orbit has total turn `4` or `-4` over one
period. This file reduces that statement to two winding bounds (total turn of absolute value at
most `4`, and nonzero), using that the total turn is a multiple of `4`, and relates it to the
Euler-characteristic form `EulerCharOne`.

The statement itself is not proved unconditionally here.
`ttf_totalTurn_eq_four_of_balancePreservingContraction` assumes `BalancePreservingContraction`,
which is false (`not_balancePreservingContraction`), so it is vacuous.
The general `turningIsFullRevolution_of_eulerCharOne` assumes `EulerCharOne`, which for orbits
of period at least three is equivalent to the conclusion (`ttf_eulerCharOne_iff_winds`). The face
loops of these orbits are cycles (`ndt_orbit_isCycle`), so the Umlaufsatz for simple closed lattice
walks, `turnSum_eq_four_or_neg_four`, is the natural route to an unconditional proof; that
transfer is not done here.

## Main definitions

* `StatMech.Lattice.ttf_WindsAtMostOnce`, `StatMech.Lattice.ttf_WindsAtLeastOnce`: the total turn
  of a boundary orbit of the star hull has absolute value at most `4`, resp. is nonzero.

## Main results

* `StatMech.Lattice.ttf_totalTurn_eq_four_of_winds`, `StatMech.Lattice.ttf_winds_iff`: total turn
  `±4` iff both winding bounds hold.
* `StatMech.Lattice.ttf_eulerCharOne_iff_winds`: for period at least three, `EulerCharOne` iff
  both winding bounds hold.
* `StatMech.Lattice.ttf_totalTurn_eq_four_of_balancePreservingContraction`: total turn `±4`
  under `BalancePreservingContraction` (vacuous).
-/

@[expose] public section

open SimpleGraph Function Set Finset

namespace StatMech

namespace Lattice

/-- The total turn of the boundary orbit of `a` in the star hull of `K` has absolute value at most
`4`. Specialization of `uc_WindsAtMostOnce` to star hulls. -/
def ttf_WindsAtMostOnce (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) : Prop :=
  |totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a)| ≤ 4

/-- The total turn of the boundary orbit of `a` in the star hull of `K` is nonzero. Specialization
of `uc_WindsAtLeastOnce` to star hulls. -/
def ttf_WindsAtLeastOnce (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) : Prop :=
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) ≠ 0

/-- Total turn `±4` for a boundary orbit of a star hull that winds at most once and at least once.
See also `uc_totalTurn_eq_four_of_winds` for arbitrary sets. -/
theorem ttf_totalTurn_eq_four_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hmax : ttf_WindsAtMostOnce K a) (hmin : ttf_WindsAtLeastOnce K a) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
  have hdvd := four_dvd_orbit_totalTurnZ (ndt_StarHull K) a
  unfold ttf_WindsAtMostOnce at hmax
  unfold ttf_WindsAtLeastOnce at hmin
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hmax hmin ⊢
  rw [abs_le] at hmax
  have hk1 : k = 1 ∨ k = -1 := by
    rcases lt_trichotomy k 0 with h | h | h
    · right; omega
    · exact absurd (by rw [h]; ring) hmin
    · left; omega
  rcases hk1 with h | h
  · left; rw [h]; ring
  · right; rw [h]; ring

/-- Total turn `±4` satisfies both winding bounds. -/
theorem ttf_winds_of_totalTurn_eq_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (h : totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) :
    ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a := by
  unfold ttf_WindsAtMostOnce ttf_WindsAtLeastOnce
  rcases h with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩

/-- For a boundary orbit of a star hull, total turn `±4` iff both winding bounds hold. -/
theorem ttf_winds_iff (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    (ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a) ↔
      (totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
        totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) := by
  constructor
  · rintro ⟨hmax, hmin⟩; exact ttf_totalTurn_eq_four_of_winds K a hmax hmin
  · exact ttf_winds_of_totalTurn_eq_four K a

/-- For a boundary orbit of a star hull with period at least three, `EulerCharOne` holds iff both
winding bounds hold. -/
theorem ttf_eulerCharOne_iff_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a) :
    EulerCharOne (ndt_StarHull K) a ↔
      (ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a) := by
  rw [eulerCharOne_iff_turningIsFullRevolution (ndt_StarHull K) a hp]
  unfold TurningIsFullRevolution
  rw [ttf_winds_iff]

/-- Total turn `±4` for every boundary orbit of a finite nonempty star hull, assuming
`BalancePreservingContraction`. Vacuous: `BalancePreservingContraction` is refuted by
`not_balancePreservingContraction`. -/
theorem ttf_totalTurn_eq_four_of_balancePreservingContraction (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hcontr : BalancePreservingContraction) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  turningIsFullRevolution_of_contraction hcontr (ndt_StarHull K) hSK hne a

/-- The unit-cell orbit winds exactly once. -/
theorem ttf_unitCell_winds :
    |totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)| ≤ 4 ∧
      totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) ≠ 0 := by
  rcases unitCell_turningIsFullRevolution with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩

end Lattice

end StatMech
