/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceDomino
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Cyclomatic

/-!
# Discrete Gauss–Bonnet for boundary contours of lattice sets

Fix a set `K` of sites of `ℤ²` and a boundary dart `a` of `K`. Along the boundary orbit of `a`
(the darts `a, dartNext K a, dartNext K (dartNext K a), …`) the contour turns by `turnZ = +1`, `0`
or `-1` quarter turns at each dart. After one period the dart direction is back where it started,
so the total turning is a multiple of `4`: it equals `4 * revCount K a`, where the rotation index
`revCount K a` counts full revolutions. The orbit makes one full revolution
(`TurningIsFullRevolution`) exactly when `revCount K a = ±1`.

The file also packages this as an "Euler characteristic" identity: the cycle graph `C_p` on
`p ≥ 3` vertices has `p` edges, cyclomatic number `1`, and is not acyclic. `contourEulerChar p`
is the cyclomatic number of `C_p` (so it is `1` for `p ≥ 3`), and `EulerCharOne K a` says that
`revCount K a = ±contourEulerChar p` for the orbit period `p`. For `p ≥ 3` this is equivalent to a
full revolution. The quantity `1` here is the first Betti number of the contour cycle, which equals
the Euler characteristic of the disk it bounds; the Euler characteristic `V - E` of the cycle
itself is `0`.

The identity `total turning = 4 · revCount` is only the quantization half of the Gauss–Bonnet /
Hopf Umlaufsatz statement; that `revCount = ±1` for every boundary orbit is not proved here. See
`StatMech.Lattice.wad_defect_eq_four_chi` for the angle-defect form of discrete Gauss–Bonnet for
unions of unit squares, and
`StatMech.Onsager.GeneralUmlaufsatz.turnSum_eq_four_or_neg_four` for the Umlaufsatz of simple
closed lattice walks.

## Main definitions

* `StatMech.Lattice.revCount K a`: the rotation index of the boundary orbit of `a`, its total
  turning divided by `4`.
* `StatMech.Lattice.contourEulerChar p`: the cyclomatic number of the cycle graph `C_p` for
  `p ≥ 3`, and `0` otherwise.
* `StatMech.Lattice.EulerCharOne K a`: `revCount K a = ±contourEulerChar (dartOrbitPeriod K a)`.

## Main results

* `StatMech.Lattice.gaussBonnet_local_global`: the total turning along one period of a boundary
  orbit is `4 * revCount`.
* `StatMech.Lattice.turningIsFullRevolution_iff_revCount`: a full revolution means
  `revCount = ±1`.
* `StatMech.Lattice.cycleGraph_card_edges`, `StatMech.Lattice.cycleGraph_cyclomaticNumber_eq_one`,
  `StatMech.Lattice.cycleGraph_not_isAcyclic`: edge count, cyclomatic number and non-acyclicity of
  the cycle graph `C_{n+3}`.
* `StatMech.Lattice.contour_card_darts`: one period of a boundary orbit consists of
  `dartOrbitPeriod K a` distinct darts.
* `StatMech.Lattice.eulerCharOne_iff_turningIsFullRevolution`: for orbits of length at least `3`,
  `EulerCharOne` is equivalent to a full revolution.
* `StatMech.Lattice.unitCell_eulerCharOne`, `StatMech.Lattice.domino_eulerCharOne`: the unit cell
  and the domino satisfy it.

## References

* H. Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2 (1935).
-/

@[expose] public section

open SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The rotation index of the boundary orbit of `a`: the total turning `totalTurnZ` over one
period, in quarter turns, divided by `4`. -/
noncomputable def revCount (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : ℤ :=
  totalTurnZ K a.1 (dartOrbitPeriod K a) / 4

/-- Discrete Gauss–Bonnet (quantization): the total turning over one period of a boundary orbit
is `4` times its rotation index, i.e. the sum of the local turns `turnZ` is a whole number of
revolutions. This does not say that the rotation index is `±1` (Hopf's Umlaufsatz); see
`StatMech.Onsager.GeneralUmlaufsatz.turnSum_eq_four_or_neg_four` for that statement for simple
closed lattice walks. -/
theorem gaussBonnet_local_global (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * revCount K a := by
  unfold revCount
  rw [Int.mul_ediv_cancel' (four_dvd_orbit_totalTurnZ K a)]

/-- A boundary orbit makes one full revolution exactly when its rotation index is `±1`. -/
theorem turningIsFullRevolution_iff_revCount (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    TurningIsFullRevolution K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
  unfold TurningIsFullRevolution
  rw [gaussBonnet_local_global K a]
  constructor
  · rintro (h | h)
    · left; omega
    · right; omega
  · rintro (h | h)
    · left; rw [h]; ring
    · right; rw [h]; ring

/-- The cycle graph `C_{n+3}` has `n + 3` edges. See also
`StatMech.Onsager.JedBridge.cycleGraph_card_edges` for the `edgeSet.ncard` form. -/
theorem cycleGraph_card_edges (n : ℕ) :
    (cycleGraph (n + 3)).edgeFinset.card = n + 3 := by
  have hsum : ∑ v : Fin (n + 3), (cycleGraph (n + 3)).degree v
      = 2 * (cycleGraph (n + 3)).edgeFinset.card :=
    sum_degrees_eq_twice_card_edges _
  have hsum2 : ∑ v : Fin (n + 3), (cycleGraph (n + 3)).degree v = 2 * (n + 3) := by
    rw [Finset.sum_congr rfl (fun v _ => cycleGraph_degree_three_le)]
    simp [Finset.sum_const, Finset.card_univ]
    ring
  omega

/-- The cycle graph `C_{n+3}` has cyclomatic number `1`. See also
`StatMech.Onsager.JedBridge.cycle_nullity_one`. -/
theorem cycleGraph_cyclomaticNumber_eq_one (n : ℕ) :
    cyclomaticNumber (cycleGraph (n + 3)) = 1 := by
  unfold cyclomaticNumber
  rw [cycleGraph_card_edges]
  simp

/-- The cycle graph `C_{n+3}` is not acyclic. See also `SimpleGraph.cycleGraph.isCycle_cycle`,
which exhibits the cycle. -/
theorem cycleGraph_not_isAcyclic (n : ℕ) : ¬ (cycleGraph (n + 3)).IsAcyclic := by
  rw [← cyclomaticNumber_eq_zero_iff_isAcyclic connected_cycleGraph_add_one]
  rw [cycleGraph_cyclomaticNumber_eq_one]
  decide

/-- The first `dartOrbitPeriod K a` iterates of the successor map are pairwise distinct. A
specialization of `Function.iterate_injOn_Iio_minimalPeriod`. -/
theorem orbitEnum_injective (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    Function.Injective
      (fun i : Fin (dartOrbitPeriod K a) => (dartNextSub K)^[i.val] a) := by
  intro i j h
  simp only at h
  have hmp : dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a := rfl
  have := Function.iterate_injOn_Iio_minimalPeriod (f := dartNextSub K) (x := a)
    (Set.mem_Iio.mpr (by rw [← hmp]; exact i.isLt))
    (Set.mem_Iio.mpr (by rw [← hmp]; exact j.isLt)) h
  exact Fin.ext this

open Classical in
/-- One period of the boundary orbit of `a` consists of exactly `dartOrbitPeriod K a` distinct
darts. -/
theorem contour_card_darts (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (Finset.univ.image
      (fun i : Fin (dartOrbitPeriod K a) => (dartNextSub K)^[i.val] a)).card
      = dartOrbitPeriod K a := by
  rw [Finset.card_image_of_injective _ (orbitEnum_injective K a), Finset.card_univ,
    Fintype.card_fin]

/-- The cyclomatic number (first Betti number) of the cycle graph `C_p` for `p ≥ 3`, and `0`
for `p < 3`. It equals `1` whenever `p ≥ 3`: this is the Euler characteristic of the disk bounded by
a contour of length `p`, not the Euler characteristic `V - E = 0` of the contour itself. -/
noncomputable def contourEulerChar (p : ℕ) : ℕ := by
  classical
  exact if h : 3 ≤ p then cyclomaticNumber (cycleGraph p) else 0

/-- `contourEulerChar p = 1` for `p ≥ 3`. -/
theorem contourEulerChar_eq_one {p : ℕ} (hp : 3 ≤ p) : contourEulerChar p = 1 := by
  unfold contourEulerChar
  rw [dite_eq_left hp]
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 3 := ⟨p - 3, by omega⟩
  exact cycleGraph_cyclomaticNumber_eq_one n

/-- The rotation index of the boundary orbit of `a` is `±contourEulerChar p`, where `p` is the
orbit period. For `p ≥ 3` this just says that the rotation index is `±1`. -/
def EulerCharOne (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  revCount K a = (contourEulerChar (dartOrbitPeriod K a) : ℤ) ∨
    revCount K a = -(contourEulerChar (dartOrbitPeriod K a) : ℤ)

/-- A boundary orbit of length at least `3` satisfying `EulerCharOne` makes a full revolution. -/
theorem turningIsFullRevolution_of_eulerCharOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (h : EulerCharOne K a) :
    TurningIsFullRevolution K a := by
  apply (turningIsFullRevolution_iff_revCount K a).mpr
  have hchi : contourEulerChar (dartOrbitPeriod K a) = 1 := contourEulerChar_eq_one hp
  rcases h with h | h
  · left; rw [h, hchi]; rfl
  · right; rw [h, hchi]; rfl

/-- For a boundary orbit of length at least `3`, `EulerCharOne` holds exactly when the orbit makes a
full revolution. -/
theorem eulerCharOne_iff_turningIsFullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ TurningIsFullRevolution K a := by
  constructor
  · exact turningIsFullRevolution_of_eulerCharOne K a hp
  · intro h
    have hchi : contourEulerChar (dartOrbitPeriod K a) = 1 := contourEulerChar_eq_one hp
    unfold EulerCharOne
    rw [hchi]
    rcases (turningIsFullRevolution_iff_revCount K a).mp h with h1 | h1
    · left; rw [h1]; rfl
    · right; rw [h1]; rfl

/-- The boundary orbit of the unit cell satisfies `EulerCharOne`. -/
theorem unitCell_eulerCharOne : EulerCharOne unitCell ucBase := by
  have hp : 3 ≤ dartOrbitPeriod unitCell ucBase := by
    rw [unitCell_orbitPeriod_eq_four]; norm_num
  exact (eulerCharOne_iff_turningIsFullRevolution unitCell ucBase hp).mpr
    unitCell_turningIsFullRevolution

/-- The boundary orbit of the domino satisfies `EulerCharOne`. -/
theorem domino_eulerCharOne : EulerCharOne domino dmBase := by
  have hp : 3 ≤ dartOrbitPeriod domino dmBase := by
    rw [domino_orbitPeriod_eq_six]; norm_num
  exact (eulerCharOne_iff_turningIsFullRevolution domino dmBase hp).mpr
    domino_turningIsFullRevolution

end Lattice

end StatMech
