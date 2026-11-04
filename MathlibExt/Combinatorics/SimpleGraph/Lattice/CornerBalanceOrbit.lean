/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EarContraction
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.GaussBonnet

/-!
# Orbit invariance of the corner balance and the rotation index

For a finite set `K` of sites of `ℤ²`, the successor map `dartNextSub K` permutes the boundary
darts, and all darts of one boundary orbit share the same orbit period, total turning, corner
balance, rotation index and `EulerCharOne` property: these quantities depend only on the orbit, not
on the starting dart. The corner balance is `4` times the rotation index, so `BalanceIsFour` means
rotation index `±1`, which for orbits of length at least `3` is `EulerCharOne`.

## Main results

* `StatMech.Lattice.dartOrbitPeriod_dartNextSub`, `StatMech.Lattice.totalTurnZ_period_dartNextSub`,
  `StatMech.Lattice.cornerBalance_iterate_dartNextSub`, `StatMech.Lattice.revCount_dartNextSub`,
  `StatMech.Lattice.eulerCharOne_dartNextSub`: invariance along an orbit.
* `StatMech.Lattice.cornerBalance_eq_four_revCount`: corner balance `= 4 · revCount`.
* `StatMech.Lattice.balanceIsFour_iff_revCount_pm_one`,
  `StatMech.Lattice.eulerCharOne_iff_balanceIsFour`: the corner-balance, rotation-index and
  Euler-characteristic forms of a full revolution agree.
-/

@[expose] public section

open SimpleGraph Function

namespace StatMech

namespace Lattice

/-- Shifting the index of a sum over `range p` by one does not change it when the summand takes the
same value at `p` and at `0`. -/
theorem sum_range_cyclic_shift (g : ℕ → ℤ) (p : ℕ) (hcyc : g p = g 0) :
    ∑ i ∈ Finset.range p, g (i + 1) = ∑ i ∈ Finset.range p, g i := by
  have h1 : ∑ i ∈ Finset.range (p + 1), g i = (∑ i ∈ Finset.range p, g (i + 1)) + g 0 :=
    Finset.sum_range_succ' g p
  have h2 : ∑ i ∈ Finset.range (p + 1), g i = (∑ i ∈ Finset.range p, g i) + g p :=
    Finset.sum_range_succ g p
  rw [hcyc] at h2
  omega

/-- All darts of a boundary orbit of a finite set have the same orbit period. -/
theorem dartOrbitPeriod_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    dartOrbitPeriod K (dartNextSub K a) = dartOrbitPeriod K a := by
  have hfin : Finite {e : Dart // IsBoundaryDart K e} := (boundaryDarts_finite K hK).to_subtype
  unfold dartOrbitPeriod
  exact Function.minimalPeriod_apply ((dartNextSub_injective K).mem_periodicPts a)

theorem dartOrbitPeriod_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    dartOrbitPeriod K ((dartNextSub K)^[n] a) = dartOrbitPeriod K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', dartOrbitPeriod_dartNextSub K hK, ih]

/-- The total turning over one period of a boundary orbit of a finite set does not depend on the
starting dart. -/
theorem totalTurnZ_period_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K (dartNextSub K a).1 (dartOrbitPeriod K (dartNextSub K a))
      = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  rw [dartOrbitPeriod_dartNextSub K hK a]
  set p := dartOrbitPeriod K a with hp
  set g := fun i => turnZ K ((dartNext K)^[i] a.1) with hg
  have hper : (dartNext K)^[p] a.1 = a.1 := orbit_iterate_period_eq K a
  have hcyc : g p = g 0 := by simp only [hg, hper, Function.iterate_zero_apply]
  unfold totalTurnZ
  rw [dartNextSub_val]
  have key : ∀ i, (dartNext K)^[i] (dartNext K a.1) = (dartNext K)^[i + 1] a.1 := by
    intro i; rw [Function.iterate_succ_apply]
  simp_rw [key]
  exact sum_range_cyclic_shift g p hcyc

theorem totalTurnZ_period_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    totalTurnZ K ((dartNextSub K)^[n] a).1 (dartOrbitPeriod K ((dartNextSub K)^[n] a))
      = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', totalTurnZ_period_dartNextSub K hK, ih]

/-- The corner balance does not change when the orbit is started one dart later. -/
theorem cornerBalance_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance K (dartNextSub K a) = cornerBalance K a := by
  rw [cornerBalance_eq_totalTurnZ, cornerBalance_eq_totalTurnZ]
  exact totalTurnZ_period_dartNextSub K hK a

theorem cornerBalance_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    cornerBalance K ((dartNextSub K)^[n] a) = cornerBalance K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', cornerBalance_dartNextSub K hK, ih]

/-- The corner balance is constant along a boundary orbit of a finite set. -/
theorem cornerBalance_constant_on_orbit (K : Set (Site 2)) (hK : K.Finite)
    (a b : {e : Dart // IsBoundaryDart K e}) (n : ℕ) (hb : b = (dartNextSub K)^[n] a) :
    cornerBalance K b = cornerBalance K a := by
  rw [hb]; exact cornerBalance_iterate_dartNextSub K hK a n

/-- The rotation index does not change when the orbit is started one dart later. -/
theorem revCount_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    revCount K (dartNextSub K a) = revCount K a := by
  unfold revCount
  rw [totalTurnZ_period_dartNextSub K hK a]

theorem revCount_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    revCount K ((dartNextSub K)^[n] a) = revCount K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', revCount_dartNextSub K hK, ih]

/-- `EulerCharOne` does not change when the orbit is started one dart later. -/
theorem eulerCharOne_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    EulerCharOne K (dartNextSub K a) ↔ EulerCharOne K a := by
  unfold EulerCharOne
  rw [revCount_dartNextSub K hK a, dartOrbitPeriod_dartNextSub K hK a]

theorem eulerCharOne_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    EulerCharOne K ((dartNextSub K)^[n] a) ↔ EulerCharOne K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', eulerCharOne_dartNextSub K hK, ih]

/-- The corner balance is `4` times the rotation index. -/
theorem cornerBalance_eq_four_revCount (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance K a = 4 * revCount K a := by
  rw [cornerBalance_eq_totalTurnZ, gaussBonnet_local_global]

/-- The corner balance is `±4` exactly when the rotation index is `±1`. -/
theorem balanceIsFour_iff_revCount_pm_one (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    BalanceIsFour K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
  unfold BalanceIsFour
  rw [cornerBalance_eq_four_revCount]
  constructor
  · rintro (h | h)
    · left; omega
    · right; omega
  · rintro (h | h)
    · left; rw [h]; ring
    · right; rw [h]; ring

/-- For a boundary orbit of length at least `3`, `EulerCharOne` holds exactly when the corner
balance is `±4`. -/
theorem eulerCharOne_iff_balanceIsFour (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ BalanceIsFour K a := by
  rw [balanceIsFour_iff_simplePolygon, simplePolygonCornerBalance_iff,
    eulerCharOne_iff_turningIsFullRevolution K a hp]

theorem unitCell_cornerBalance_dartNextSub :
    cornerBalance unitCell (dartNextSub unitCell ucBase) = cornerBalance unitCell ucBase :=
  cornerBalance_dartNextSub unitCell unitCell_finite ucBase

theorem domino_cornerBalance_dartNextSub :
    cornerBalance domino (dartNextSub domino dmBase) = cornerBalance domino dmBase :=
  cornerBalance_dartNextSub domino domino_finite dmBase

end Lattice

end StatMech
