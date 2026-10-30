/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationRunEnd

/-!
# The south-east corner at the end of the escape run

Let `q` be a least escape site of a king separation and `(e, q 1)` the first walk site east of
`q`. The site below the last run site, `(e - 1, q 1 - 1)`, lies on the walk
(`cat_runEnd_corner_data`). As for the south-west corner of `q`, the south-east corner
`(e, q 1 - 1)` either gives a thick point outright (a missing corner edge), lies off the walk and
outside the interior, or lies on the walk with both corner edges traversed
(`cat_seCorner_dichotomy`). The residual predicate `cat_CrossArcThick` asks for a thick point only
in the last two cases; it is the weakest predicate of the chain
`kns_EscapeThickPoint → etp_EscapeWallThick → ewt_BottomWallThick → gtp_RunEndReconnect →
cat_CrossArcThick`.

The residual predicates in this chain are reductions, not theorems: for a four-thin walk and an
interior seed, each of them is equivalent to `ksc_NoKingSeparation Vc seed` itself, because the
conclusion of each predicate is a thick point (impossible for a four-thin walk) and
`kns_escapeThickPoint_of_noKingSeparation` gives the converse. The four-thin results below
therefore restate the target conclusion rather than prove it. The fjord and staircase examples
show the predicates are satisfiable; they do not show they hold for any four-thin walk with a
king separation (they cannot).

`cat_CrossArcThick` fails for the four-thin figure-eight walk (`wpc_cat_crossArcThick_false`), so
four-thinness alone is not enough for king connectivity of the interior.

## Main definitions

* `StatMech.Lattice.cat_CrossArcThick Vc seed`: the residual hypothesis described above.

## Main results

* `StatMech.Lattice.cat_thickPoint_of_seCorner`, `StatMech.Lattice.cat_seCorner_dichotomy`,
  `StatMech.Lattice.cat_runEnd_corner_data`: the south-east corner analysis.
* `StatMech.Lattice.cat_escape_structure_eastbox`: the least escape site with box bounds.
* `StatMech.Lattice.cat_noKingSeparation_of_fourThin`,
  `StatMech.Lattice.cat_kingRowLinked_of_fourThin`,
  `StatMech.Lattice.cat_kingInteriorConnected_of_fourThin`: conditional on `cat_CrossArcThick`.
* `StatMech.Lattice.cat_crossArcThick_of_runEndReconnect`: the new predicate is weaker.
* `StatMech.Lattice.cat_residuals_iff_noKingSeparation_of_fourThin`: for four-thin walks every
  residual predicate of the chain is equivalent to the conclusion.
* `StatMech.Lattice.cat_fjord_nonvacuous`.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- If `(e, y)`, `(e - 1, y - 1)` and the corner `(e, y - 1)` lie on the walk and one of the two
lattice edges from the corner to the other two sites is not traversed, the walk has a thick point.
-/
theorem cat_thickPoint_of_seCorner {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {e y : ℤ}
    (hE : (![e, y] : Site 2) ∈ Vc.support)
    (hB : (![e - 1, y - 1] : Site 2) ∈ Vc.support)
    (hC : (![e, y - 1] : Site 2) ∈ Vc.support)
    (hnon : s((![e, y] : Site 2), (![e, y - 1] : Site 2)) ∉ Vc.edges ∨
            s((![e - 1, y - 1] : Site 2), (![e, y - 1] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc := by
  rcases hnon with h | h
  · refine ⟨(![e, y] : Site 2), (![e, y - 1] : Site 2), hE, hC, ?_, h⟩
    have hadj := (vadj_step e (y - 1)).symm
    rw [show ((y - 1) + 1 : ℤ) = y by ring] at hadj
    exact hadj
  · refine ⟨(![e - 1, y - 1] : Site 2), (![e, y - 1] : Site 2), hB, hC, ?_, h⟩
    have hadj := hadj_step (e - 1) (y - 1)
    rw [show ((e - 1) + 1 : ℤ) = e by ring] at hadj
    exact hadj

/-- At a least escape site `q`, if `(e - 1, q 1)` is an interior site outside `T`, then the
south-east corner `(e, q 1 - 1)` lies on the walk or outside the interior. -/
theorem cat_seCorner_dichotomy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {q : Site 2} (M e : ℤ)
    (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hCbox : (-M < e ∧ e ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M))
    (hwI : (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hwnT : (![e - 1, q 1] : Site 2) ∉ T) :
    (![e, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCoff, hCI⟩ := hcon
  have hCT : (![e, q 1 - 1] : Site 2) ∈ T := by
    by_contra hCnT
    have hle := hmin _ hCI hCnT
    have hlt : rlc_lexMeasure M (![e, q 1 - 1] : Site 2) < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        (by simpa using hCbox.1.1) (by simpa using hCbox.1.2)
        (by simpa using hCbox.2.1) (by simpa using hCbox.2.2)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; left; omega)
    omega
  have hwT : (![e - 1, q 1] : Site 2) ∈ T := by
    have h : (![e + (-1), (q 1 - 1) + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inr rfl) (Or.inl rfl) hCT
        (by rw [← sub_eq_add_neg]; simpa using hwI)
    rw [← sub_eq_add_neg] at h
    simpa using h
  exact hwnT hwT

/-- At a least escape site `q` whose row is interior up to the walk site `(e, q 1)`, the last run
site `(e - 1, q 1)` is interior and outside `T`, and the site below it is on the walk. -/
theorem cat_runEnd_corner_data {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (M : ℤ) (hqnT : q ∉ T)
    (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hq1box : -M < q 1 - 1 ∧ q 1 - 1 ≤ M)
    {e : ℤ} (he₁ : q 0 < e) (heM : -M < e - 1 ∧ e - 1 ≤ M)
    (he₃ : ∀ x : ℤ, q 0 ≤ x → x < e → (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc) :
    (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc ∧
      (![e - 1, q 1] : Site 2) ∉ T ∧
      (![e - 1, q 1 - 1] : Site 2) ∈ Vc.support := by
  have hlastI : (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc :=
    he₃ (e - 1) (by omega) (by omega)
  have hrun_off : ∀ t : ℤ, q 0 ≤ t → t ≤ e - 1 → (![t, q 1] : Site 2) ∉ Vc.support := by
    intro t ht ht'; exact (jil_mem_offSupportInterior Vc _ |>.mp (he₃ t ht (by omega))).1
  have hlastnT : (![e - 1, q 1] : Site 2) ∉ T :=
    ewt_escapeRow_notMem_of_run Vc hsat hTsub hqnT
      (hrun_off (q 0) (le_refl _) (by omega)) (le_refl _) (by omega)
      (by omega) (le_refl _) hrun_off
  have hbot : (![e - 1, q 1 - 1] : Site 2) ∈ Vc.support :=
    ewt_escapeRow_down_onSupport Vc hsat M hmin hqbox hlastI hlastnT ⟨heM, hq1box⟩
  exact ⟨hlastI, hlastnT, hbot⟩

/-- Residual hypothesis: as `gtp_RunEndReconnect`, also given that `(e - 1, q 1 - 1)` is on the walk
and that the south-east corner `(e, q 1 - 1)` is either off the walk and outside the interior, or on
the walk with both corner edges traversed.

The weakest predicate of the chain. For a four-thin walk and an interior seed it is equivalent to
`ksc_NoKingSeparation Vc seed`; it fails for the figure-eight walk (`wpc_cat_crossArcThick_false`).
-/
def cat_CrossArcThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
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
      (∀ (e : ℤ), q 0 < e → (![e, q 1] : Site 2) ∈ Vc.support →
        (∀ x : ℤ, q 0 ≤ x → x < e → (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc) →
        (![e - 1, q 1 - 1] : Site 2) ∈ Vc.support →
        ((![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
          (![e, q 1 - 1] : Site 2) ∉ Vc.support) ∨
        ((![e, q 1 - 1] : Site 2) ∈ Vc.support ∧
          s((![e, q 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges ∧
          s((![e - 1, q 1 - 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges) →
        kns_ThickPoint Vc)

/-- Escape structure with the box bound `M₀` of the interior, so that the east end of the escape run
can also be placed in the box. -/
theorem cat_escape_structure_eastbox {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hsep : kns_KingSeparation Vc seed) :
    ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧
      ∃ (M₀ : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧
        (∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
          rlc_lexMeasure (M₀ + 1) q ≤ rlc_lexMeasure (M₀ + 1) z) ∧
        (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧
        (![q 0, q 1 - 1] : Site 2) ∈ Vc.support ∧
        ((-(M₀ + 1) < q 0 ∧ q 0 ≤ M₀ + 1) ∧ (-(M₀ + 1) < q 1 ∧ q 1 ≤ M₀ + 1)) ∧
        (-(M₀ + 1) < q 1 - 1 ∧ q 1 - 1 ≤ M₀ + 1) ∧
        (-(M₀ + 1) < q 0 - 1 ∧ q 0 - 1 ≤ M₀ + 1) ∧
        (∀ z ∈ jec_leftRegion Vc,
          (-M₀ < z 0 ∧ z 0 ≤ M₀) ∧ (-M₀ < z 1 ∧ z 1 ≤ M₀)) := by
  obtain ⟨T, hseedT, hTsub, hsat, z, hzI, hznT⟩ := hsep
  obtain ⟨M₀, hM₀⟩ := rlc_interior_bounded Vc
  obtain ⟨q, hqI, hqnT, hmin⟩ := kns_exists_lexMin_escape Vc hzI hznT (M₀ + 1)
  have hqL : q ∈ jec_leftRegion Vc := (jil_mem_offSupportInterior Vc _ |>.mp hqI).2
  obtain ⟨⟨hq0a, hq0b⟩, ⟨hq1a, hq1b⟩⟩ := hM₀ _ hqL
  have hqbox : (-(M₀ + 1) < q 0 ∧ q 0 ≤ M₀ + 1) ∧ (-(M₀ + 1) < q 1 ∧ q 1 ≤ M₀ + 1) :=
    ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hWbox : (-(M₀ + 1) < q 0 - 1 ∧ q 0 - 1 ≤ M₀ + 1) ∧ (-(M₀ + 1) < q 1 ∧ q 1 ≤ M₀ + 1) :=
    ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hSbox : (-(M₀ + 1) < q 0 ∧ q 0 ≤ M₀ + 1) ∧ (-(M₀ + 1) < q 1 - 1 ∧ q 1 - 1 ≤ M₀ + 1) :=
    ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hq1box : -(M₀ + 1) < q 1 - 1 ∧ q 1 - 1 ≤ M₀ + 1 := ⟨by omega, by omega⟩
  have hq0box : -(M₀ + 1) < q 0 - 1 ∧ q 0 - 1 ≤ M₀ + 1 := ⟨by omega, by omega⟩
  obtain ⟨hW, hSsup⟩ :=
    kns_escape_axials_onSupport Vc hsat hTsub hqI hqnT (M₀ + 1) hmin hqbox hWbox hSbox
  exact ⟨T, hseedT, hTsub, hsat, M₀, q, hqI, hqnT, hmin, hW, hSsup, hqbox, hq1box, hq0box, hM₀⟩

/-- A four-thin closed walk satisfying `cat_CrossArcThick` has no king separation from an interior
seed.

Conditional: for four-thin walks the hypothesis is equivalent to the conclusion. It is false for the
four-thin figure-eight walk, so no proof of `cat_CrossArcThick` from four-thinness alone exists. -/
theorem cat_noKingSeparation_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : cat_CrossArcThick Vc seed) :
    ksc_NoKingSeparation Vc seed := by
  by_contra hns
  classical
  have hsep := (kns_kingSeparation_iff_not_noKingSeparation Vc hseedI).mpr hns
  obtain ⟨T, hseedT, hTsub, hsat, M₀, q, hqI, hqnT, hmin, hW, hS, hqbox, hq1box, hq0box, hM₀⟩ :=
    cat_escape_structure_eastbox Vc hsep
  set M : ℤ := M₀ + 1 with hM
  have hnotThin : kns_ThickPoint Vc → False :=
    fun htp => (kns_thickPoint_iff_not_fourThin Vc).mp htp hthin
  have hbottom : ∀ wx : ℤ, (-M < wx ∧ wx ≤ M) →
      (![wx, q 1] : Site 2) ∈ jil_offSupportInterior Vc →
      (![wx, q 1] : Site 2) ∉ T →
      (![wx, q 1 - 1] : Site 2) ∈ Vc.support := by
    intro wx hwxbox hwI hwnT
    exact ewt_escapeRow_down_onSupport Vc hsat M hmin hqbox hwI hwnT ⟨hwxbox, hq1box⟩
  have hSWclause :
      ((![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![q 0 - 1, q 1 - 1] : Site 2) ∉ Vc.support) ∨
      ((![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support ∧
        s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges ∧
        s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges) := by
    by_cases hCsup : (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support
    · by_cases hWC : s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges
      · by_cases hSC : s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges
        · exact Or.inr ⟨hCsup, hWC, hSC⟩
        · exact absurd (etp_thickPoint_of_swCorner Vc hW hS hCsup (Or.inr hSC)) hnotThin
      · exact absurd (etp_thickPoint_of_swCorner Vc hW hS hCsup (Or.inl hWC)) hnotThin
    · have hCbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) :=
        ⟨hq0box, hq1box⟩
      have hcorner := kns_lexBelow_diag_corner Vc hsat hTsub hqI hqnT M hmin hqbox hCbox
      have hCext : (![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
        rcases hcorner with h | h
        · exact absurd h hCsup
        · exact h
      exact Or.inl ⟨hCext, hCsup⟩
  obtain ⟨e, he₁, he₂, he₃⟩ := gtp_eastBoundary_onSupport Vc hqI
  have hlastL : (![e - 1, q 1] : Site 2) ∈ jec_leftRegion Vc :=
    (jil_mem_offSupportInterior Vc _ |>.mp (he₃ (e - 1) (by omega) (by omega))).2
  obtain ⟨⟨he1a, he1b⟩, _⟩ := hM₀ _ hlastL
  simp only [Matrix.cons_val_zero] at he1a he1b
  have heM : -M < e - 1 ∧ e - 1 ≤ M := ⟨by rw [hM]; omega, by rw [hM]; omega⟩
  obtain ⟨hlastI, hlastnT, hbotCorner⟩ :=
    cat_runEnd_corner_data Vc hsat hTsub M hqnT hmin hqbox hq1box he₁ heM he₃
  have hSEclause :
      ((![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![e, q 1 - 1] : Site 2) ∉ Vc.support) ∨
      ((![e, q 1 - 1] : Site 2) ∈ Vc.support ∧
        s((![e, q 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges ∧
        s((![e - 1, q 1 - 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges) := by
    by_cases hCsup : (![e, q 1 - 1] : Site 2) ∈ Vc.support
    · by_cases hEC : s((![e, q 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges
      · by_cases hBC : s((![e - 1, q 1 - 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges
        · exact Or.inr ⟨hCsup, hEC, hBC⟩
        · exact absurd (cat_thickPoint_of_seCorner Vc he₂ hbotCorner hCsup (Or.inr hBC)) hnotThin
      · exact absurd (cat_thickPoint_of_seCorner Vc he₂ hbotCorner hCsup (Or.inl hEC)) hnotThin
    · have hCEbox : (-M < e ∧ e ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) :=
        ⟨⟨by rw [hM]; omega, by rw [hM]; omega⟩, hq1box⟩
      have hdich := cat_seCorner_dichotomy Vc hsat M e hmin hqbox hCEbox hlastI hlastnT
      have hCext : (![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
        rcases hdich with h | h
        · exact absurd h hCsup
        · exact h
      exact Or.inl ⟨hCext, hCsup⟩
  exact hnotThin
    (hres T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hSWclause hbottom
      e he₁ he₂ he₃ hbotCorner hSEclause)

/-- A four-thin walk satisfying `cat_CrossArcThick` is king row-linked to an interior seed.
Conditional, as `cat_noKingSeparation_of_fourThin`. -/
theorem cat_kingRowLinked_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : cat_CrossArcThick Vc seed) :
    mci_KingRowLinked Vc seed :=
  ksc_kingRowLinked_of_noKingSeparation Vc hseedI
    (cat_noKingSeparation_of_fourThin Vc hseedI hthin hres)

/-- A four-thin walk with nonempty interior satisfying `cat_CrossArcThick` for every interior seed
has a king-connected interior. Conditional, as `cat_noKingSeparation_of_fourThin`. -/
theorem cat_kingInteriorConnected_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z₀ : Site 2} (hz₀ : z₀ ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : ∀ seed ∈ jil_offSupportInterior Vc, cat_CrossArcThick Vc seed) :
    mci_KingInteriorConnected Vc :=
  ⟨z₀, hz₀, cat_kingRowLinked_of_fourThin Vc hz₀ hthin (hres z₀ hz₀)⟩

/-- `gtp_RunEndReconnect` implies `cat_CrossArcThick`. -/
theorem cat_crossArcThick_of_runEndReconnect {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hgtp : gtp_RunEndReconnect Vc seed) :
    cat_CrossArcThick Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hcorner hbottom
    e he₁ he₂ he₃ _hbotCorner _hSEclause
  exact hgtp T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hcorner hbottom e he₁ he₂ he₃

/-- `etp_EscapeWallThick` implies `cat_CrossArcThick`. -/
theorem cat_crossArcThick_of_escapeWallThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hetp : etp_EscapeWallThick Vc seed) :
    cat_CrossArcThick Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin _hqbox _hq1box hW hS hcorner _hbottom
    _e _he₁ _he₂ _he₃ _hbotCorner _hSEclause
  exact hetp T hseedT hTsub hsat M q hqI hqnT hmin hW hS hcorner

/-- The fjord satisfies `cat_CrossArcThick` because it has a thick point. -/
theorem cat_fjord_crossArcThick : cat_CrossArcThick sdc_fjord (![5, 1] : Site 2) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => kns_fjord_thickPoint

/-- The fjord has a king separation, a thick point, and satisfies `cat_CrossArcThick`; it is not
four-thin. -/
theorem cat_fjord_nonvacuous :
    kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    cat_CrossArcThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ⟨kns_fjord_kingSeparation, kns_fjord_thickPoint, cat_fjord_crossArcThick,
   mci_fjord_not_fourThin⟩

/-- The staircase walk `ksd_stair` satisfies `cat_CrossArcThick` from `(1, 1)`. -/
theorem cat_ksd_crossArcThick : cat_CrossArcThick ksd_stair (![1, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hqbox _hq1box _hW _hS _hcorner _hbottom
    _e _he₁ _he₂ _he₃ _hbotCorner _hSEclause
  exact absurd (ksc_ksd_noKingSeparation T hseedT hTsub hsat hqI) hqnT

/-- The staircase walk `kda_stairDR` satisfies `cat_CrossArcThick` from `(3, 1)`. -/
theorem cat_kda_crossArcThick : cat_CrossArcThick kda_stairDR (![3, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hqbox _hq1box _hW _hS _hcorner _hbottom
    _e _he₁ _he₂ _he₃ _hbotCorner _hSEclause
  exact absurd (ksc_kda_noKingSeparation T hseedT hTsub hsat hqI) hqnT

/-- For a four-thin closed walk and an interior seed, each residual predicate of the
thick-point chain (`kns_EscapeThickPoint`, `etp_EscapeWallThick`, `ewt_BottomWallThick`,
`gtp_RunEndReconnect`, `cat_CrossArcThick`) is equivalent to the conclusion
`ksc_NoKingSeparation Vc seed`. So the `*_noKingSeparation_of_fourThin` theorems restate their
target rather than reduce it to a weaker input. -/
theorem cat_residuals_iff_noKingSeparation_of_fourThin {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc) :
    (cat_CrossArcThick Vc seed ↔ ksc_NoKingSeparation Vc seed) ∧
    (gtp_RunEndReconnect Vc seed ↔ ksc_NoKingSeparation Vc seed) ∧
    (ewt_BottomWallThick Vc seed ↔ ksc_NoKingSeparation Vc seed) ∧
    (etp_EscapeWallThick Vc seed ↔ ksc_NoKingSeparation Vc seed) ∧
    (kns_EscapeThickPoint Vc seed ↔ ksc_NoKingSeparation Vc seed) := by
  have k := fun h => kns_escapeThickPoint_of_noKingSeparation Vc (seed := seed) h
  have e := fun h => etp_escapeWallThick_of_escapeThickPoint Vc (k h)
  have b := fun h => ewt_bottomWallThick_of_escapeWallThick Vc (e h)
  have g := fun h => gtp_runEndReconnect_of_bottomWallThick Vc (b h)
  have c := fun h => cat_crossArcThick_of_runEndReconnect Vc (g h)
  exact ⟨⟨cat_noKingSeparation_of_fourThin Vc hseedI hthin, c⟩,
    ⟨gtp_noKingSeparation_of_fourThin Vc hseedI hthin, g⟩,
    ⟨ewt_noKingSeparation_of_fourThin Vc hseedI hthin, b⟩,
    ⟨etp_noKingSeparation_of_fourThin Vc hseedI hthin, e⟩,
    ⟨kns_noKingSeparation_of_fourThin Vc hseedI hthin, k⟩⟩

end Lattice

end StatMech
