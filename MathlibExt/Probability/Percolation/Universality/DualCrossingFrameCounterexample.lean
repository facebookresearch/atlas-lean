/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.RotatedDualCounterexamples

/-!
# Two vertex-frame dual crossing events that are not dual to a horizontal crossing

The standard crossing-duality lemma for bond percolation on `ℤ²` says that a box has no open
left–right crossing exactly when the dual box has a closed (dual-open) top–bottom crossing. In
this library the dual configuration `dualConfig ω` is indexed through the quarter turn
`crossEdge`, so a dual crossing has to be stated in the right coordinates. This file records, on
the explicit wall configuration `bcc_wallCfg` (the three horizontal edges between columns `0` and
`1` of the box `[0, 2]²` are closed, all other edges open), that two natural vertex-indexed
candidates are *not* implied by the absence of a horizontal crossing:

* `DualVerticalCrossing ω 0 2 0 2`, a vertical open crossing of `dualConfig ω` in the same box;
* `dcp_DualCutConnectsRot ω 2`, bottom-to-top reachability in the quarter-turned barrier graph
  `dcw_dualBarrierGraph` of `DualCutToPath`.

The correct face-indexed event is `pmd_FaceDualVCrossing`; on the same configuration it holds
(`pmd_wall_only_face_frame_works`).

## Main results

* `rdv_box_frame_target_false`: `¬ (∀ ω, ¬ H(ω, [0,2]²) → DualVerticalCrossing ω 0 2 0 2)`.
* `rdv_rotResidue_false_on_noH`: `¬ dcp_DualCutConnectsRot bcc_wallCfg 2`, although
  `bcc_wallCfg` has no horizontal crossing of `[0, 2]²`.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

/-- The vertex-frame implication `¬ HorizontalCrossing → DualVerticalCrossing` on the box
`[0, 2]²` is false: the wall configuration `bcc_wallCfg` is a counterexample.
See also `bcc_dichotomy_false`, the same statement phrased as a non-inclusion of events. -/
theorem rdv_box_frame_target_false :
    ¬ (∀ ω : ConfigSpace (Sym2 (Site 2)),
        ¬ HorizontalCrossing ω 0 2 0 2 → DualVerticalCrossing ω 0 2 0 2) := by
  intro h
  exact bcc_noV_wall (h bcc_wallCfg bcc_noH_wall)

/-- In the wall configuration every vertex of the box reachable from the left side lies in
column `0`. -/
theorem rdv_leftReach_wall_x0 {v : Site 2} (h : v ∈ bcd_leftReach bcc_wallCfg 2) :
    v 0 = 0 := by
  obtain ⟨_hvbox, x, hxL, hvbox', hconn⟩ := h
  have hx0 : x 0 = 0 := hxL.2
  have hinv := bcc_wall_walk_keeps_x0 (x := ⟨x, leftSide_subset hxL⟩) (y := ⟨v, hvbox'⟩)
    hconn.some
  exact hinv.mp hx0

/-- In the wall configuration every vertex of the quarter-turned barrier graph that has a
neighbour has second coordinate at most `1`. -/
theorem rdv_barrier_wall_snd_le {p q : Site 2}
    (h : (dcw_dualBarrierGraph bcc_wallCfg 2).Adj p q) : p 1 ≤ 1 := by
  obtain ⟨v, w, ⟨hvL, hwbox, hwnL, hadj⟩, hpq⟩ := h
  have hv0 : v 0 = 0 := rdv_leftReach_wall_x0 hvL
  have hw0 : w 0 = 1 := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    rw [hv0] at hadj
    rw [mem_rect] at hwbox
    have hw0ne : w 0 ≠ 0 := fun hw00 => hwnL
      (dcw_leftSide_in_L bcc_wallCfg 2 ⟨by rw [mem_rect]; omega, hw00⟩)
    omega
  have hrv1 : (rot90Fun v) 1 = v 0 := by simp [rot90Fun]
  have hrw1 : (rot90Fun w) 1 = w 0 := by simp [rot90Fun]
  rcases hpq with ⟨hp, _⟩ | ⟨hp, _⟩
  · rw [hp, hrv1, hv0]; norm_num
  · rw [hp, hrw1, hw0]

/-- Walks in the quarter-turned wall barrier graph never leave the half-plane `y ≤ 1`. -/
theorem rdv_barrier_wall_walk_snd_le {p q : Site 2}
    (c : (dcw_dualBarrierGraph bcc_wallCfg 2).Walk p q) (hp : p 1 ≤ 1) : q 1 ≤ 1 := by
  induction c with
  | nil => exact hp
  | @cons a b d hab _tail ih => exact ih (rdv_barrier_wall_snd_le hab.symm)

/-- The rotated barrier-graph crossing `dcp_DualCutConnectsRot` fails for the wall configuration,
which has no horizontal crossing of `[0, 2]²` (`bcc_noH_wall`). So the hypothesis of
`dcp_rotatedDualVerticalCrossing_of_cutConnectsRot` does not follow from the absence of a
horizontal crossing. -/
theorem rdv_rotResidue_false_on_noH : ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 := by
  rintro ⟨p₀, hp₀, q₀, hq₀, hreach⟩
  have hp0 : p₀ 1 = 0 := hp₀.2
  have hq2 : q₀ 1 = 2 := hq₀.2
  obtain ⟨c⟩ := hreach
  have hend := rdv_barrier_wall_walk_snd_le c (by rw [hp0]; norm_num)
  rw [hq2] at hend; norm_num at hend

/-- On the wall configuration there is no horizontal crossing of `[0, 2]²`, and neither
vertex-frame dual event (`DualVerticalCrossing ω 0 2 0 2`, nor
`dcp_DualCutConnectsRot`) holds. -/
theorem rdv_both_targets_false_on_witness :
    ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧
      ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2 ∧
      ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 :=
  ⟨bcc_noH_wall, bcc_noV_wall, rdv_rotResidue_false_on_noH⟩

end Universality

end StatMech
