/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparation

/-!
# King separations and thick points

A thick point of a closed walk `Vc` in the square lattice is a pair of lattice-adjacent sites of
the walk whose edge `Vc` does not traverse; `Vc` is four-thin (`mci_FourThin`) when it has none.
Given a king separation `T` of the interior (a proper king-saturated subset containing the seed),
take the interior site `q ∉ T` that is least for the row-major order `rlc_lexMeasure`. Its west and
south lattice neighbors both lie on the walk (`kns_kingSeparation_escape_structure`). The residual
predicate `kns_EscapeThickPoint` asks that this configuration force a thick point; under it a
four-thin walk has no king separation.

The residual predicates in this chain are reductions, not theorems: for a four-thin walk and an
interior seed, each of them is equivalent to `ksc_NoKingSeparation Vc seed` itself, because the
conclusion of each predicate is a thick point (impossible for a four-thin walk) and
`kns_escapeThickPoint_of_noKingSeparation` gives the converse. The four-thin results below
therefore restate the target conclusion rather than prove it. The fjord and staircase examples
show the predicates are satisfiable; they do not show they hold for any four-thin walk with a
king separation (they cannot).

## Main definitions

* `StatMech.Lattice.kns_KingSeparation Vc seed`: a proper king-saturated subset of the interior
  containing `seed`.
* `StatMech.Lattice.kns_ThickPoint Vc`: two adjacent walk sites not joined by a walk edge.
* `StatMech.Lattice.kns_EscapeThickPoint Vc seed`: the residual hypothesis described above.

## Main results

* `StatMech.Lattice.kns_kingSeparation_iff_not_noKingSeparation`,
  `StatMech.Lattice.kns_thickPoint_iff_not_fourThin`: the new notions are negations of the old.
* `StatMech.Lattice.kns_exists_lexMin_escape`,
  `StatMech.Lattice.kns_kingSeparation_escape_structure`: the least escape site and its west and
  south neighbors on the walk.
* `StatMech.Lattice.kns_row_complete`: a king-saturated set fills a horizontal off-walk run.
* `StatMech.Lattice.kns_noKingSeparation_of_fourThin`,
  `StatMech.Lattice.kns_kingRowLinked_of_fourThin`,
  `StatMech.Lattice.kns_kingInteriorConnected_of_fourThin`: conditional on `kns_EscapeThickPoint`.
* `StatMech.Lattice.kns_fjord_nonvacuous`: the fjord has a king separation and a thick point.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The two staircase walks `ksd_stair` and `kda_stairDR` are four-thin and have no king separation.
-/
theorem kns_fourThin_noKingSeparation_examples :
    (mci_FourThin ksd_stair ∧ ksc_NoKingSeparation ksd_stair (![1, 1] : Site 2)) ∧
    (mci_FourThin kda_stairDR ∧ ksc_NoKingSeparation kda_stairDR (![3, 1] : Site 2)) :=
  ⟨⟨ksd_stair_fourThin, ksc_ksd_noKingSeparation⟩,
   ⟨kda_stairDR_fourThin, ksc_kda_noKingSeparation⟩⟩

/-- The fjord is not four-thin and has a king separation from `(5, 1)`. -/
theorem kns_fjord_not_fourThin_has_separation :
    ¬ mci_FourThin sdc_fjord ∧ ¬ ksc_NoKingSeparation sdc_fjord (![5, 1] : Site 2) :=
  ⟨mci_fjord_not_fourThin, ksc_fjord_noKingSeparation_false⟩

/-- Let `T` be king-saturated and let `q` be an interior site outside `T` with least
`rlc_lexMeasure M` among such sites, inside the box `(-M, M]²`. Then every lattice neighbor of `q`
in the box that comes earlier in row-major order lies on the walk. -/
theorem kns_lexBelow_axial_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (_hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    {w : Site 2} (hwadj : (hypercubicLattice 2).Adj q w)
    (hwbox : (-M < w 0 ∧ w 0 ≤ M) ∧ (-M < w 1 ∧ w 1 ≤ M))
    (hlex : w 1 < q 1 ∨ (w 1 = q 1 ∧ w 0 < q 0)) :
    w ∈ Vc.support := by
  by_contra hwoff
  have hwI : w ∈ jil_offSupportInterior Vc :=
    mci_offSupport_neighbor_interior Vc hqI hwadj hwoff
  have hwT : w ∈ T := by
    by_contra hwnT
    have hle := hmin w hwI hwnT
    have hlt : rlc_lexMeasure M w < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        hwbox.1.1 hwbox.1.2 hwbox.2.1 hwbox.2.2 hlex
    omega
  exact hqnT (ksc_saturated_axial Vc hsat hwT hqI hwadj.symm)

/-- At a least escape site `q`, the west neighbor `(q 0 - 1, q 1)` and the south neighbor
`(q 0, q 1 - 1)` lie on the walk. -/
theorem kns_escape_axials_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hWbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hSbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧ (![q 0, q 1 - 1] : Site 2) ∈ Vc.support := by
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  constructor
  · refine kns_lexBelow_axial_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox
      (w := (![q 0 - 1, q 1] : Site 2)) ?_ ?_ ?_
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    · simpa using hWbox
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      right; exact ⟨trivial, by omega⟩
  · refine kns_lexBelow_axial_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox
      (w := (![q 0, q 1 - 1] : Site 2)) ?_ ?_ ?_
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    · simpa using hSbox
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      left; omega

/-- At a least escape site `q`, the south-west corner `(q 0 - 1, q 1 - 1)` lies on the walk or
outside the interior. -/
theorem kns_lexBelow_diag_corner {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (_hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hCbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCoff, hCI⟩ := hcon
  have hCnT : (![q 0 - 1, q 1 - 1] : Site 2) ∉ T → False := by
    intro hCnT
    have hle := hmin _ hCI hCnT
    have hlt : rlc_lexMeasure M (![q 0 - 1, q 1 - 1] : Site 2) < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        (by simpa using hCbox.1.1) (by simpa using hCbox.1.2)
        (by simpa using hCbox.2.1) (by simpa using hCbox.2.2)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; left; omega)
    omega
  have hCT : (![q 0 - 1, q 1 - 1] : Site 2) ∈ T := by
    by_contra h; exact hCnT h
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  have hdiag : mci_kingGraph.Adj (![q 0 - 1, q 1 - 1] : Site 2) q := by
    rw [hq01]
    simp
  exact hqnT (hsat _ _ hCT hqI hdiag)

/-- At a least escape site `q`, the south-east corner `(q 0 + 1, q 1 - 1)` lies on the walk or
outside the interior. -/
theorem kns_lexBelow_diag_corner_SE {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (_hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hCbox : (-M < q 0 + 1 ∧ q 0 + 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![q 0 + 1, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![q 0 + 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCoff, hCI⟩ := hcon
  have hCT : (![q 0 + 1, q 1 - 1] : Site 2) ∈ T := by
    by_contra hCnT
    have hle := hmin _ hCI hCnT
    have hlt : rlc_lexMeasure M (![q 0 + 1, q 1 - 1] : Site 2) < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        (by simpa using hCbox.1.1) (by simpa using hCbox.1.2)
        (by simpa using hCbox.2.1) (by simpa using hCbox.2.2)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; left; omega)
    omega
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  have hdiag : mci_kingGraph.Adj (![q 0 + 1, q 1 - 1] : Site 2) q := by
    rw [hq01]
    simp
  exact hqnT (hsat _ _ hCT hqI hdiag)

/-- The east neighbor of an interior site is interior when it is off the walk. -/
theorem kns_right_mem_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hright : (![x + 1, y] : Site 2) ∉ Vc.support) :
    (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc := by
  have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x + 1, y] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  exact mci_offSupport_neighbor_interior Vc hz hadj hright

/-- A king-saturated set that contains one site of a horizontal run of off-walk sites contains the
whole run. -/
theorem kns_row_complete {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {lo hi y x₀ x₁ : ℤ}
    (hx₀T : (![x₀, y] : Site 2) ∈ T)
    (hloff : (![lo, y] : Site 2) ∉ Vc.support)
    (hx₀lo : lo ≤ x₀) (hx₀hi : x₀ ≤ hi) (hx₁lo : lo ≤ x₁) (hx₁hi : x₁ ≤ hi)
    (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ Vc.support) :
    (![x₁, y] : Site 2) ∈ T := by
  obtain ⟨p, hp⟩ := jil_hsegment_reachable_offSupport {p | p ∈ Vc.support}
    (lo := lo) (hi := hi) (y := y) (x₁ := x₀) (x₂ := x₁)
    (by simpa using hloff) hx₀lo hx₀hi hx₁lo hx₁hi
    (by intro t ht ht'; simpa using hrun t ht ht')
  have hp' : ∀ z ∈ p.support, z ∉ Vc.support := by intro z hz; simpa using hp z hz
  have hx₀I : (![x₀, y] : Site 2) ∈ jil_offSupportInterior Vc := hTsub hx₀T
  have hint := mci_offSupport_walk_interior Vc p hp' hx₀I
  have hpk : ∀ w ∈ (p.mapLe mci_hyper_le_king).support, w ∈ jil_offSupportInterior Vc := by
    intro w hw
    rw [SimpleGraph.Walk.support_mapLe_eq_support mci_hyper_le_king p] at hw
    exact hint w hw
  exact ksc_saturated_absorbs_kingWalk Vc hsat (p.mapLe mci_hyper_le_king) hpk hx₀T

/-- A king separation of the interior of `Vc` from `seed`: a king-saturated subset of the interior
that contains `seed` and misses some interior site. -/
def kns_KingSeparation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∃ T : Set (Site 2), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧
    ksc_KingSaturated Vc T ∧ ∃ z ∈ jil_offSupportInterior Vc, z ∉ T

/-- A thick point of `Vc`: two lattice-adjacent sites of the walk joined by an edge that the walk
does not traverse. Its absence is `mci_FourThin` (`kns_thickPoint_iff_not_fourThin`). -/
def kns_ThickPoint {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∃ u v : Site 2, u ∈ Vc.support ∧ v ∈ Vc.support ∧
    (hypercubicLattice 2).Adj u v ∧ s(u, v) ∉ Vc.edges

/-- A king separation exists iff `ksc_NoKingSeparation` fails. The interior-seed hypothesis is not
used. -/
theorem kns_kingSeparation_iff_not_noKingSeparation {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (_hseedI : seed ∈ jil_offSupportInterior Vc) :
    kns_KingSeparation Vc seed ↔ ¬ ksc_NoKingSeparation Vc seed := by
  constructor
  · rintro ⟨T, hseedT, hTsub, hsat, z, hzI, hznT⟩ hns
    exact hznT (hns T hseedT hTsub hsat hzI)
  · intro hns
    rw [ksc_NoKingSeparation] at hns
    push Not at hns
    obtain ⟨T, hseedT, hTsub, hsat, hnsub⟩ := hns
    rw [Set.not_subset] at hnsub
    obtain ⟨z, hzI, hznT⟩ := hnsub
    exact ⟨T, hseedT, hTsub, hsat, z, hzI, hznT⟩

/-- A walk has a thick point iff it is not four-thin. -/
theorem kns_thickPoint_iff_not_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    kns_ThickPoint Vc ↔ ¬ mci_FourThin Vc := by
  constructor
  · rintro ⟨u, v, hu, hv, hadj, hne⟩ hthin
    exact hne (hthin u v hu hv hadj)
  · intro hthin
    rw [mci_FourThin] at hthin
    push Not at hthin
    obtain ⟨u, v, hu, hv, hadj, hne⟩ := hthin
    exact ⟨u, v, hu, hv, hadj, hne⟩

/-- Residual hypothesis: for every king separation `T` of the interior from `seed` and every least
escape site `q` of `T` (least `rlc_lexMeasure M` among interior sites outside `T`) whose west and
south neighbors lie on the walk, the walk has a thick point.

For a four-thin walk and an interior seed this is equivalent to `ksc_NoKingSeparation Vc seed`. -/
def kns_EscapeThickPoint {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) :
    Prop :=
  ∀ (T : Set (Site 2)), seed ∈ T → T ⊆ jil_offSupportInterior Vc → ksc_KingSaturated Vc T →
    ∀ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc → q ∉ T →
      (∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z) →
      (![q 0 - 1, q 1] : Site 2) ∈ Vc.support →
      (![q 0, q 1 - 1] : Site 2) ∈ Vc.support →
      kns_ThickPoint Vc

/-- An interior site outside `T` yields an interior site outside `T` of least `rlc_lexMeasure M`;
the interior is finite. -/
theorem kns_exists_lexMin_escape {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} {z : Site 2} (hzI : z ∈ jil_offSupportInterior Vc) (hznT : z ∉ T)
    (M : ℤ) :
    ∃ q ∈ jil_offSupportInterior Vc, q ∉ T ∧
      ∀ w ∈ jil_offSupportInterior Vc, w ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M w := by
  classical
  have hfin := rlc_offSupportInterior_finite Vc
  set S : Finset (Site 2) := hfin.toFinset.filter (fun w => w ∉ T) with hS
  have hzS : z ∈ S := by
    rw [hS, Finset.mem_filter]; exact ⟨hfin.mem_toFinset.mpr hzI, hznT⟩
  obtain ⟨q, hqS, hqmin⟩ := S.exists_min_image (rlc_lexMeasure M) ⟨z, hzS⟩
  rw [hS, Finset.mem_filter] at hqS
  refine ⟨q, hfin.mem_toFinset.mp hqS.1, hqS.2, ?_⟩
  intro w hwI hwnT
  exact hqmin w (by rw [hS, Finset.mem_filter]; exact ⟨hfin.mem_toFinset.mpr hwI, hwnT⟩)

/-- **Escape structure.** A king separation has a least escape site `q` whose west and south
neighbors lie on the walk. -/
theorem kns_kingSeparation_escape_structure {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hsep : kns_KingSeparation Vc seed) :
    ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧
      ∃ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧
        (∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
          rlc_lexMeasure M q ≤ rlc_lexMeasure M z) ∧
        (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧
        (![q 0, q 1 - 1] : Site 2) ∈ Vc.support := by
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
  obtain ⟨hW, hSsup⟩ :=
    kns_escape_axials_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox hWbox hSbox
  exact ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hSsup⟩

/-- A four-thin closed walk satisfying `kns_EscapeThickPoint` has no king separation from an
interior seed.

Conditional: for four-thin walks the hypothesis `kns_EscapeThickPoint` is equivalent to the
conclusion (see `kns_escapeThickPoint_of_noKingSeparation`). -/
theorem kns_noKingSeparation_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : kns_EscapeThickPoint Vc seed) :
    ksc_NoKingSeparation Vc seed := by
  by_contra hns
  have hsep := (kns_kingSeparation_iff_not_noKingSeparation Vc hseedI).mpr hns
  obtain ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hSsup⟩ :=
    kns_kingSeparation_escape_structure Vc hsep
  have htp := hres T hseedT hTsub hsat M q hqI hqnT hmin hW hSsup
  exact (kns_thickPoint_iff_not_fourThin Vc).mp htp hthin

/-- Without a king separation the residual hypothesis `kns_EscapeThickPoint` holds trivially. -/
theorem kns_escapeThickPoint_of_noKingSeparation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hns : ksc_NoKingSeparation Vc seed) :
    kns_EscapeThickPoint Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hW _hSsup
  exact absurd (hns T hseedT hTsub hsat hqI) hqnT

/-- A four-thin walk satisfying `kns_EscapeThickPoint` is king row-linked to an interior seed.
Conditional, as `kns_noKingSeparation_of_fourThin`. -/
theorem kns_kingRowLinked_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : kns_EscapeThickPoint Vc seed) :
    mci_KingRowLinked Vc seed :=
  ksc_kingRowLinked_of_noKingSeparation Vc hseedI
    (kns_noKingSeparation_of_fourThin Vc hseedI hthin hres)

/-- A four-thin walk with nonempty interior satisfying `kns_EscapeThickPoint` for every interior
seed has a king-connected interior. Conditional, as `kns_noKingSeparation_of_fourThin`. -/
theorem kns_kingInteriorConnected_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z₀ : Site 2} (hz₀ : z₀ ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : ∀ seed ∈ jil_offSupportInterior Vc, kns_EscapeThickPoint Vc seed) :
    mci_KingInteriorConnected Vc :=
  ⟨z₀, hz₀, kns_kingRowLinked_of_fourThin Vc hz₀ hthin (hres z₀ hz₀)⟩

/-- The fjord has a thick point: `(3, 1)` and `(4, 1)` lie on the walk but are not joined by a walk
edge. -/
theorem kns_fjord_thickPoint : kns_ThickPoint sdc_fjord := by
  refine ⟨(![3, 1] : Site 2), (![4, 1] : Site 2), mci_fjord_on_31, sdc_fjord_on_41, ?_,
    mci_fjord_no_row1_horizontal_edge⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide

/-- The right pocket of the fjord is a king separation from `(5, 1)`. -/
theorem kns_fjord_kingSeparation : kns_KingSeparation sdc_fjord (![5, 1] : Site 2) := by
  obtain ⟨hRPint, hRPsat, hRPproper⟩ := ksc_fjord_rp_is_king_separation
  exact ⟨iwc_RightPocket, iwc_mem_rightPocket_51, hRPint, hRPsat,
    (![1, 1] : Site 2), sdc_fjord_mem_interior_11,
    fun h => iwc_not_rightPocket_11 h⟩

/-- The fjord satisfies `kns_EscapeThickPoint` because it has a thick point. -/
theorem kns_fjord_escapeThickPoint : kns_EscapeThickPoint sdc_fjord (![5, 1] : Site 2) :=
  fun _ _ _ _ _ _ _ _ _ _ _ => kns_fjord_thickPoint

/-- The fjord has a king separation, a thick point, and satisfies `kns_EscapeThickPoint`; it is not
four-thin. -/
theorem kns_fjord_nonvacuous :
    kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    kns_EscapeThickPoint sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ⟨kns_fjord_kingSeparation, kns_fjord_thickPoint, kns_fjord_escapeThickPoint,
   mci_fjord_not_fourThin⟩

/-- The staircase walk `ksd_stair` satisfies `kns_EscapeThickPoint` from `(1, 1)`. -/
theorem kns_ksd_escapeThickPoint : kns_EscapeThickPoint ksd_stair (![1, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin hW hSsup
  exact absurd (ksc_ksd_noKingSeparation T hseedT hTsub hsat hqI) hqnT

/-- The staircase walk `kda_stairDR` satisfies `kns_EscapeThickPoint` from `(3, 1)`. -/
theorem kns_kda_escapeThickPoint : kns_EscapeThickPoint kda_stairDR (![3, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin hW hSsup
  exact absurd (ksc_kda_noKingSeparation T hseedT hTsub hsat hqI) hqnT

end Lattice

end StatMech
