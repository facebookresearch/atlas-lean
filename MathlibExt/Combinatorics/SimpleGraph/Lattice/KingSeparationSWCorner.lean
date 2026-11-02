/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerFaces
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationThickPoint

/-!
# The south-west corner of a least escape site

This file refines `kns_EscapeThickPoint` by examining the south-west corner
`c = (q 0 - 1, q 1 - 1)` of a least escape site `q` of a king separation. If `c` is on the walk
and one of the two lattice edges from `c` to the west and south neighbors of `q` is not traversed,
the walk has a thick point outright. The residual predicate `etp_EscapeWallThick` asks for a thick
point only in the two remaining cases: `c` is off the walk and outside the interior, or `c` is on
the walk with both corner edges traversed. The file also shows that a king-saturated set cannot
pass the gaps above and below a site of a horizontal wall.

The residual predicates in this chain are reductions, not theorems: for a four-thin walk and an
interior seed, each of them is equivalent to `ksc_NoKingSeparation Vc seed` itself, because the
conclusion of each predicate is a thick point (impossible for a four-thin walk) and
`kns_escapeThickPoint_of_noKingSeparation` gives the converse. The conditional four-thin
theorems that restated the target conclusion from these predicates were therefore removed;
what remains here is the geometric corner analysis, the weakening from the previous
predicate, and the fjord / staircase examples, which show the predicates are satisfiable
without showing they hold for any four-thin walk with a king separation (they cannot).

## Main definitions

* `StatMech.Lattice.etp_EscapeWallThick Vc seed`: the residual hypothesis described above.

## Main results

* `StatMech.Lattice.etp_horiz_wall_gaps_blocked`: across a separation, the middle site of a
  horizontal run is on the walk and the sites above and below it are not interior.
* `StatMech.Lattice.etp_thickPoint_of_swCorner`: a missing corner edge is a thick point.
* `StatMech.Lattice.etp_escape_structure_box`: the least escape site with box bounds.
* `StatMech.Lattice.etp_escapeWallThick_of_escapeThickPoint`: the new predicate is weaker.
* `StatMech.Lattice.etp_fjord_nonvacuous`.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- If a king-saturated set `T` contains `(x - 1, y)` but not the interior site `(x + 1, y)`, then
`(x, y + 1)` is not interior: otherwise two diagonal king steps through it would carry `T` to
`(x + 1, y)`. -/
theorem etp_horiz_wall_upperGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hL : (![x - 1, y] : Site 2) ∈ T)
    (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hRnT : (![x + 1, y] : Site 2) ∉ T) :
    (![x, y + 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hUI
  have hUT : (![x, y + 1] : Site 2) ∈ T := by
    have h : (![(x - 1) + 1, y + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hL (by simpa using hUI)
    simpa using h
  have hRT : (![x + 1, y] : Site 2) ∈ T := by
    have h : (![x + 1, (y + 1) + (-1)] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inr rfl) hUT (by simpa using hR)
    simpa using h
  exact hRnT hRT

/-- If a king-saturated set `T` contains `(x - 1, y)` but not the interior site `(x + 1, y)`, then
`(x, y - 1)` is not interior. -/
theorem etp_horiz_wall_lowerGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hL : (![x - 1, y] : Site 2) ∈ T)
    (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hRnT : (![x + 1, y] : Site 2) ∉ T) :
    (![x, y - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hDI
  have hDT : (![x, y - 1] : Site 2) ∈ T := by
    have h : (![(x - 1) + 1, y + (-1)] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inr rfl) hL
        (by rw [← sub_eq_add_neg]; simpa using hDI)
    rw [← sub_eq_add_neg] at h
    simpa using h
  have hRT : (![x + 1, y] : Site 2) ∈ T := by
    have h : (![x + 1, (y - 1) + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hDT (by simpa using hR)
    simpa using h
  exact hRnT hRT

/-- **Horizontal wall.** If a king-saturated set `T ⊆ I` contains `(x - 1, y)` but not the interior
site `(x + 1, y)`, then `(x, y)` is on the walk and neither `(x, y + 1)` nor `(x, y - 1)` is
interior. -/
theorem etp_horiz_wall_gaps_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {x y : ℤ} (hL : (![x - 1, y] : Site 2) ∈ T)
    (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hRnT : (![x + 1, y] : Site 2) ∉ T) :
    (![x, y] : Site 2) ∈ Vc.support ∧
      (![x, y + 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
      (![x, y - 1] : Site 2) ∉ jil_offSupportInterior Vc :=
  ⟨ksc_separated_midOnSupport_horiz Vc hsat hTsub hL hR hRnT,
   etp_horiz_wall_upperGap_blocked Vc hsat hL hR hRnT,
   etp_horiz_wall_lowerGap_blocked Vc hsat hL hR hRnT⟩

/-- If the west neighbor, the south neighbor and the south-west corner of `q` lie on the walk and
one of the two lattice edges from the corner to those neighbors is not traversed, the walk has a
thick point. -/
theorem etp_thickPoint_of_swCorner {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {q : Site 2}
    (hW : (![q 0 - 1, q 1] : Site 2) ∈ Vc.support)
    (hS : (![q 0, q 1 - 1] : Site 2) ∈ Vc.support)
    (hC : (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support)
    (hnon : s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∉ Vc.edges ∨
            s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc := by
  rcases hnon with h | h
  · refine ⟨(![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2), hW, hC, ?_, h⟩
    have hadj := (vadj_step (q 0 - 1) (q 1 - 1)).symm
    rw [show ((q 1 - 1) + 1 : ℤ) = q 1 by ring] at hadj
    exact hadj
  · refine ⟨(![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2), hS, hC, ?_, h⟩
    have hadj := (hadj_step (q 0 - 1) (q 1 - 1)).symm
    rw [show ((q 0 - 1) + 1 : ℤ) = q 0 by ring] at hadj
    exact hadj

/-- Residual hypothesis: at every least escape site `q` of a king separation from `seed` (west and
south neighbors on the walk), if the south-west corner is either off the walk and outside the
interior, or on the walk with both corner edges traversed, then the walk has a thick point.

Weaker than `kns_EscapeThickPoint`. For a four-thin walk and an interior seed it is still equivalent
to `ksc_NoKingSeparation Vc seed`. -/
def etp_EscapeWallThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) :
    Prop :=
  ∀ (T : Set (Site 2)), seed ∈ T → T ⊆ jil_offSupportInterior Vc → ksc_KingSaturated Vc T →
    ∀ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc → q ∉ T →
      (∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z) →
      (![q 0 - 1, q 1] : Site 2) ∈ Vc.support →
      (![q 0, q 1 - 1] : Site 2) ∈ Vc.support →
      ((![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![q 0 - 1, q 1 - 1] : Site 2) ∉ Vc.support) ∨
      ((![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support ∧
        s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges ∧
        s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges) →
      kns_ThickPoint Vc

/-- Escape structure with box bounds: as `kns_kingSeparation_escape_structure`, also recording that
`q` and its south-west corner lie in the box `(-M, M]²`. -/
theorem etp_escape_structure_box {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hsep : kns_KingSeparation Vc seed) :
    ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧
      ∃ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧
        (∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
          rlc_lexMeasure M q ≤ rlc_lexMeasure M z) ∧
        (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧
        (![q 0, q 1 - 1] : Site 2) ∈ Vc.support ∧
        ((-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M)) ∧
        ((-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) := by
  obtain ⟨T, hseedT, hTsub, hsat, z, hzI, hznT⟩ := hsep
  obtain ⟨M₀, hM₀⟩ := rlc_interior_bounded Vc
  set M : ℤ := M₀ + 1 with hM
  obtain ⟨q, hqI, hqnT, hmin⟩ := kns_exists_lexMin_escape Vc hzI hznT M
  have hqL : q ∈ jec_leftRegion Vc := (jil_mem_offSupportInterior Vc _ |>.mp hqI).2
  obtain ⟨⟨hq0a, hq0b⟩, ⟨hq1a, hq1b⟩⟩ := hM₀ _ hqL
  have hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M) := by
    rw [hM]; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hWbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M) := by
    rw [hM]; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hSbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) := by
    rw [hM]; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hCbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) := by
    rw [hM]; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  obtain ⟨hW, hSsup⟩ :=
    kns_escape_axials_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox hWbox hSbox
  exact ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hSsup, hqbox, hCbox⟩

/-- `kns_EscapeThickPoint` implies `etp_EscapeWallThick`. -/
theorem etp_escapeWallThick_of_escapeThickPoint {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hktp : kns_EscapeThickPoint Vc seed) :
    etp_EscapeWallThick Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin hW hS _hcorner
  exact hktp T hseedT hTsub hsat M q hqI hqnT hmin hW hS

/-- The fjord satisfies `etp_EscapeWallThick` because it has a thick point. -/
theorem etp_fjord_escapeWallThick : etp_EscapeWallThick sdc_fjord (![5, 1] : Site 2) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => kns_fjord_thickPoint

/-- The fjord has a king separation, a thick point, and satisfies `etp_EscapeWallThick`; it is not
four-thin. -/
theorem etp_fjord_nonvacuous :
    kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    etp_EscapeWallThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ⟨kns_fjord_kingSeparation, kns_fjord_thickPoint, etp_fjord_escapeWallThick,
   mci_fjord_not_fourThin⟩

/-- The staircase walk `ksd_stair` satisfies `etp_EscapeWallThick` from `(1, 1)`. -/
theorem etp_ksd_escapeWallThick : etp_EscapeWallThick ksd_stair (![1, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hW _hS _hcorner
  exact absurd (ksc_ksd_noKingSeparation T hseedT hTsub hsat hqI) hqnT

/-- The staircase walk `kda_stairDR` satisfies `etp_EscapeWallThick` from `(3, 1)`. -/
theorem etp_kda_escapeWallThick : etp_EscapeWallThick kda_stairDR (![3, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hW _hS _hcorner
  exact absurd (ksc_kda_noKingSeparation T hseedT hTsub hsat hqI) hqnT

end Lattice

end StatMech
