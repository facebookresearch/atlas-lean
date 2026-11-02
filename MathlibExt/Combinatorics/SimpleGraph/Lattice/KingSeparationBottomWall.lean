/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationSWCorner

/-!
# The escape row below a least escape site

At a least escape site `q` of a king separation `T`, every interior site of the row of `q` that is
outside `T` (and inside the bounding box) has its south neighbor on the walk
(`ewt_escapeRow_down_onSupport`); in particular so do the sites of the off-walk run through `q`
(`ewt_runBottom_onSupport`). The residual predicate `ewt_BottomWallThick` adds this bottom-wall
fact, and the box bounds of `q`, as extra antecedents to `etp_EscapeWallThick`. The file also
gives the vertical analogue of the wall lemma.

The residual predicates in this chain are reductions, not theorems: for a four-thin walk and an
interior seed, each of them is equivalent to `ksc_NoKingSeparation Vc seed` itself, because the
conclusion of each predicate is a thick point (impossible for a four-thin walk) and
`kns_escapeThickPoint_of_noKingSeparation` gives the converse. The conditional four-thin
theorems that restated the target conclusion from these predicates were therefore removed;
what remains here is the geometric corner analysis, the weakening from the previous
predicate, and the fjord / staircase examples, which show the predicates are satisfiable
without showing they hold for any four-thin walk with a king separation (they cannot).

## Main definitions

* `StatMech.Lattice.ewt_BottomWallThick Vc seed`: the residual hypothesis described above.

## Main results

* `StatMech.Lattice.ewt_escapeRow_notMem_of_run`,
  `StatMech.Lattice.ewt_escapeRow_down_onSupport`,
  `StatMech.Lattice.ewt_runBottom_onSupport`: the escape row and the wall below it.
* `StatMech.Lattice.ewt_vert_wall_gaps_blocked`: the vertical wall lemma.
* `StatMech.Lattice.ewt_escape_structure_rowbox`: the least escape site with box bounds.
* `StatMech.Lattice.ewt_bottomWallThick_of_escapeWallThick`: the new predicate is weaker.
* `StatMech.Lattice.ewt_fjord_nonvacuous`.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- If `q ∉ T` for a king-saturated `T`, and `[lo, hi]` is a run of off-walk sites in the row of `q`
containing `q`, then no site of the run is in `T`. -/
theorem ewt_escapeRow_notMem_of_run {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqnT : q ∉ T)
    {lo hi x₁ : ℤ}
    (hloff : (![lo, q 1] : Site 2) ∉ Vc.support)
    (hlolo : lo ≤ q 0) (hqhi : q 0 ≤ hi) (hx₁lo : lo ≤ x₁) (hx₁hi : x₁ ≤ hi)
    (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∉ Vc.support) :
    (![x₁, q 1] : Site 2) ∉ T := by
  intro hx₁T
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  apply hqnT
  rw [hq01]
  exact kns_row_complete Vc hsat hTsub hx₁T hloff hx₁lo hx₁hi hlolo hqhi hrun

/-- At a least escape site `q`, every interior site `(wx, q 1)` outside `T` whose south neighbor
lies in the box has that south neighbor `(wx, q 1 - 1)` on the walk. -/
theorem ewt_escapeRow_down_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {q : Site 2}
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    {wx : ℤ}
    (hw : (![wx, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hwnT : (![wx, q 1] : Site 2) ∉ T)
    (hwbox : (-M < wx ∧ wx ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![wx, q 1 - 1] : Site 2) ∈ Vc.support := by
  by_contra hoff
  have hdI : (![wx, q 1 - 1] : Site 2) ∈ jil_offSupportInterior Vc := by
    have := rlc_down_mem_interior Vc hw (by simpa using hoff)
    simpa using this
  have hdT : (![wx, q 1 - 1] : Site 2) ∈ T := by
    by_contra hdnT
    have hle := hmin _ hdI hdnT
    have hlt : rlc_lexMeasure M (![wx, q 1 - 1] : Site 2) < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        (by simpa using hwbox.1.1) (by simpa using hwbox.1.2)
        (by simpa using hwbox.2.1) (by simpa using hwbox.2.2)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; left; omega)
    omega
  have hadj : (hypercubicLattice 2).Adj (![wx, q 1 - 1] : Site 2) (![wx, q 1] : Site 2) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  exact hwnT (ksc_saturated_axial Vc hsat hdT hw hadj)

/-- At a least escape site `q`, the sites below an interior off-walk run through `q` all lie on the
walk. -/
theorem ewt_runBottom_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hq1box : -M < q 1 - 1 ∧ q 1 - 1 ≤ M)
    {lo hi : ℤ}
    (hloff : (![lo, q 1] : Site 2) ∉ Vc.support)
    (hlolo : lo ≤ q 0) (hqhi : q 0 ≤ hi)
    (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∉ Vc.support)
    (hrunI : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
    {x : ℤ} (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hxbox : -M < x ∧ x ≤ M) :
    (![x, q 1 - 1] : Site 2) ∈ Vc.support := by
  have hxI : (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc := hrunI x hxlo hxhi
  have hxnT : (![x, q 1] : Site 2) ∉ T :=
    ewt_escapeRow_notMem_of_run Vc hsat hTsub hqnT hloff hlolo hqhi hxlo hxhi hrun
  exact ewt_escapeRow_down_onSupport Vc hsat M hmin hqbox hxI hxnT ⟨hxbox, hq1box⟩

/-- If a king-saturated set `T` contains `(x, y - 1)` but not the interior site `(x, y + 1)`, then
`(x + 1, y)` is not interior. -/
theorem ewt_vert_wall_rightGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hD : (![x, y - 1] : Site 2) ∈ T)
    (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hUnT : (![x, y + 1] : Site 2) ∉ T) :
    (![x + 1, y] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hRI
  have hRT : (![x + 1, y] : Site 2) ∈ T := by
    have h : (![x + 1, (y - 1) + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hD (by simpa using hRI)
    simpa using h
  have hUT : (![x, y + 1] : Site 2) ∈ T := by
    have h : (![(x + 1) + (-1), y + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inr rfl) (Or.inl rfl) hRT (by simpa using hU)
    simpa using h
  exact hUnT hUT

/-- If a king-saturated set `T` contains `(x, y - 1)` but not the interior site `(x, y + 1)`, then
`(x - 1, y)` is not interior. -/
theorem ewt_vert_wall_leftGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hD : (![x, y - 1] : Site 2) ∈ T)
    (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hUnT : (![x, y + 1] : Site 2) ∉ T) :
    (![x - 1, y] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hLI
  have hLT : (![x - 1, y] : Site 2) ∈ T := by
    have h : (![x + (-1), (y - 1) + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inr rfl) (Or.inl rfl) hD
        (by rw [← sub_eq_add_neg]; simpa using hLI)
    rw [← sub_eq_add_neg] at h
    simpa using h
  have hUT : (![x, y + 1] : Site 2) ∈ T := by
    have h : (![(x - 1) + 1, y + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hLT (by simpa using hU)
    simpa using h
  exact hUnT hUT

/-- **Vertical wall.** If a king-saturated set `T ⊆ I` contains `(x, y - 1)` but not the interior
site `(x, y + 1)`, then `(x, y)` is on the walk and neither `(x + 1, y)` nor `(x - 1, y)` is
interior. -/
theorem ewt_vert_wall_gaps_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {x y : ℤ} (hD : (![x, y - 1] : Site 2) ∈ T)
    (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hUnT : (![x, y + 1] : Site 2) ∉ T) :
    (![x, y] : Site 2) ∈ Vc.support ∧
      (![x + 1, y] : Site 2) ∉ jil_offSupportInterior Vc ∧
      (![x - 1, y] : Site 2) ∉ jil_offSupportInterior Vc :=
  ⟨ksc_separated_midOnSupport_vert Vc hsat hTsub hD hU hUnT,
   ewt_vert_wall_rightGap_blocked Vc hsat hD hU hUnT,
   ewt_vert_wall_leftGap_blocked Vc hsat hD hU hUnT⟩

/-- Residual hypothesis: as `etp_EscapeWallThick`, with the extra antecedents that `q` lies in the
box `(-M, M]²` and that every interior site of the escape row outside `T` has its south neighbor on
the walk.

Those antecedents always hold at a least escape site (`ewt_escapeRow_down_onSupport`), so the
predicate is weaker than `etp_EscapeWallThick`. For a four-thin walk and an interior seed it is
equivalent to `ksc_NoKingSeparation Vc seed`. -/
def ewt_BottomWallThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) :
    Prop :=
  ∀ (T : Set (Site 2)), seed ∈ T → T ⊆ jil_offSupportInterior Vc → ksc_KingSaturated Vc T →
    ∀ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc → q ∉ T →
      (∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z) →
      ((-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M)) →
      (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) →
      (![q 0 - 1, q 1] : Site 2) ∈ Vc.support →
      (![q 0, q 1 - 1] : Site 2) ∈ Vc.support →
      ((![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![q 0 - 1, q 1 - 1] : Site 2) ∉ Vc.support) ∨
      ((![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support ∧
        s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges ∧
        s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges) →
      (∀ wx : ℤ, (-M < wx ∧ wx ≤ M) →
        (![wx, q 1] : Site 2) ∈ jil_offSupportInterior Vc →
        (![wx, q 1] : Site 2) ∉ T →
        (![wx, q 1 - 1] : Site 2) ∈ Vc.support) →
      kns_ThickPoint Vc

/-- Escape structure with box bounds for `q`, its west neighbor and its south neighbor. -/
theorem ewt_escape_structure_rowbox {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hsep : kns_KingSeparation Vc seed) :
    ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧
      ∃ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧
        (∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
          rlc_lexMeasure M q ≤ rlc_lexMeasure M z) ∧
        (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧
        (![q 0, q 1 - 1] : Site 2) ∈ Vc.support ∧
        ((-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M)) ∧
        (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) ∧
        (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) := by
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
  have hq1box : -M < q 1 - 1 ∧ q 1 - 1 ≤ M := by rw [hM]; exact ⟨by omega, by omega⟩
  have hq0box : -M < q 0 - 1 ∧ q 0 - 1 ≤ M := by rw [hM]; exact ⟨by omega, by omega⟩
  obtain ⟨hW, hSsup⟩ :=
    kns_escape_axials_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox hWbox hSbox
  exact ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hSsup, hqbox, hq1box, hq0box⟩

/-- `etp_EscapeWallThick` implies `ewt_BottomWallThick`. -/
theorem ewt_bottomWallThick_of_escapeWallThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hetp : etp_EscapeWallThick Vc seed) :
    ewt_BottomWallThick Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin _hqbox _hq1box hW hS hcorner _hbottom
  exact hetp T hseedT hTsub hsat M q hqI hqnT hmin hW hS hcorner

/-- `kns_EscapeThickPoint` implies `ewt_BottomWallThick`. -/
theorem ewt_bottomWallThick_of_escapeThickPoint {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hktp : kns_EscapeThickPoint Vc seed) :
    ewt_BottomWallThick Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin _hqbox _hq1box hW hS _hcorner _hbottom
  exact hktp T hseedT hTsub hsat M q hqI hqnT hmin hW hS

/-- The fjord satisfies `ewt_BottomWallThick` because it has a thick point. -/
theorem ewt_fjord_bottomWallThick : ewt_BottomWallThick sdc_fjord (![5, 1] : Site 2) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => kns_fjord_thickPoint

/-- The fjord has a king separation, a thick point, and satisfies `ewt_BottomWallThick`; it is not
four-thin. -/
theorem ewt_fjord_nonvacuous :
    kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    ewt_BottomWallThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ⟨kns_fjord_kingSeparation, kns_fjord_thickPoint, ewt_fjord_bottomWallThick,
   mci_fjord_not_fourThin⟩

/-- The staircase walk `ksd_stair` satisfies `ewt_BottomWallThick` from `(1, 1)`. -/
theorem ewt_ksd_bottomWallThick : ewt_BottomWallThick ksd_stair (![1, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hqbox _hq1box _hW _hS _hcorner _hbottom
  exact absurd (ksc_ksd_noKingSeparation T hseedT hTsub hsat hqI) hqnT

/-- The staircase walk `kda_stairDR` satisfies `ewt_BottomWallThick` from `(3, 1)`. -/
theorem ewt_kda_bottomWallThick : ewt_BottomWallThick kda_stairDR (![3, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hqbox _hq1box _hW _hS _hcorner _hbottom
  exact absurd (ksc_kda_noKingSeparation T hseedT hTsub hsat hqI) hqnT

end Lattice

end StatMech
