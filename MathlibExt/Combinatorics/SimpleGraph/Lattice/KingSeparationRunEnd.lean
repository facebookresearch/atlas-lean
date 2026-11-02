/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationBottomWall

/-!
# The east end of the escape run

From an interior site `q`, walking east one reaches a first site `(e, q 1)` of the walk, and all
sites strictly between are interior (`gtp_eastBoundary_onSupport`). The residual predicate
`gtp_RunEndReconnect` adds this east end as an extra antecedent to `ewt_BottomWallThick`. The file
also records that two adjacent walk sites are joined by a walk edge or form a thick point.

The residual predicates in this chain are reductions, not theorems: for a four-thin walk and an
interior seed, each of them is equivalent to `ksc_NoKingSeparation Vc seed` itself, because the
conclusion of each predicate is a thick point (impossible for a four-thin walk) and
`kns_escapeThickPoint_of_noKingSeparation` gives the converse. The conditional four-thin
theorems that restated the target conclusion from these predicates were therefore removed;
what remains here is the geometric corner analysis, the weakening from the previous
predicate, and the fjord / staircase examples, which show the predicates are satisfiable
without showing they hold for any four-thin walk with a king separation (they cannot).

## Main definitions

* `StatMech.Lattice.gtp_RunEndReconnect Vc seed`: the residual hypothesis described above.

## Main results

* `StatMech.Lattice.gtp_edge_or_thick_horiz`, `StatMech.Lattice.gtp_edge_or_thick_vert`.
* `StatMech.Lattice.gtp_eastBoundary_onSupport`: the east end of the run through an interior site.
* `StatMech.Lattice.gtp_runEndReconnect_of_bottomWallThick`: the new predicate is weaker.
* `StatMech.Lattice.gtp_fjord_nonvacuous`.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- Two horizontally adjacent walk sites not joined by a walk edge form a thick point. -/
theorem gtp_thickPoint_of_adj_horiz {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (h1 : (![x, y] : Site 2) ∈ Vc.support) (h2 : (![x + 1, y] : Site 2) ∈ Vc.support)
    (hne : s((![x, y] : Site 2), (![x + 1, y] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc := by
  refine ⟨_, _, h1, h2, ?_, hne⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

/-- Two vertically adjacent walk sites not joined by a walk edge form a thick point. -/
theorem gtp_thickPoint_of_adj_vert {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (h1 : (![x, y] : Site 2) ∈ Vc.support) (h2 : (![x, y + 1] : Site 2) ∈ Vc.support)
    (hne : s((![x, y] : Site 2), (![x, y + 1] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc := by
  refine ⟨_, _, h1, h2, ?_, hne⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

/-- Two horizontally adjacent walk sites are joined by a walk edge, or the walk has a thick point.
-/
theorem gtp_edge_or_thick_horiz {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (h1 : (![x, y] : Site 2) ∈ Vc.support) (h2 : (![x + 1, y] : Site 2) ∈ Vc.support) :
    s((![x, y] : Site 2), (![x + 1, y] : Site 2)) ∈ Vc.edges ∨ kns_ThickPoint Vc := by
  by_cases he : s((![x, y] : Site 2), (![x + 1, y] : Site 2)) ∈ Vc.edges
  · exact Or.inl he
  · exact Or.inr (gtp_thickPoint_of_adj_horiz Vc h1 h2 he)

/-- Two vertically adjacent walk sites are joined by a walk edge, or the walk has a thick point. -/
theorem gtp_edge_or_thick_vert {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (h1 : (![x, y] : Site 2) ∈ Vc.support) (h2 : (![x, y + 1] : Site 2) ∈ Vc.support) :
    s((![x, y] : Site 2), (![x, y + 1] : Site 2)) ∈ Vc.edges ∨ kns_ThickPoint Vc := by
  by_cases he : s((![x, y] : Site 2), (![x, y + 1] : Site 2)) ∈ Vc.edges
  · exact Or.inl he
  · exact Or.inr (gtp_thickPoint_of_adj_vert Vc h1 h2 he)

/-- **East end of a run.** For an interior site `q` there is `e > q 0` with `(e, q 1)` on the walk
and every site `(x, q 1)` with `q 0 ≤ x < e` interior. -/
theorem gtp_eastBoundary_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {q : Site 2}
    (hqI : q ∈ jil_offSupportInterior Vc) :
    ∃ e : ℤ, q 0 < e ∧ (![e, q 1] : Site 2) ∈ Vc.support ∧
      ∀ x : ℤ, q 0 ≤ x → x < e → (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc := by
  classical
  obtain ⟨M, hM⟩ := rlc_interior_bounded Vc
  have hbound : ∃ n : ℕ, (![q 0 + ((n : ℤ) + 1), q 1] : Site 2) ∉ jil_offSupportInterior Vc := by
    refine ⟨(M - q 0 + 1).toNat, ?_⟩
    intro hin
    have hL := (jil_mem_offSupportInterior Vc _ |>.mp hin).2
    have := (hM _ hL).1.2
    simp only [Matrix.cons_val_zero] at this
    omega
  set P : ℕ → Prop := fun n => (![q 0 + ((n : ℤ) + 1), q 1] : Site 2) ∉ jil_offSupportInterior Vc
    with hP
  have hPfind : P (Nat.find hbound) := Nat.find_spec hbound
  set n0 := Nat.find hbound with hn0
  set e : ℤ := q 0 + ((n0 : ℤ) + 1) with he
  have hq01 : q = (![q 0, q 1] : Site 2) := by ext i; fin_cases i <;> simp
  have hxint : ∀ x : ℤ, q 0 ≤ x → x < e → (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc := by
    intro x hxlo hxhi
    obtain ⟨j, hj⟩ : ∃ j : ℕ, x = q 0 + (j : ℤ) := ⟨(x - q 0).toNat, by omega⟩
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj, hj0]; simp only [Nat.cast_zero, add_zero]; rw [← hq01]; exact hqI
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
      have hkn0 : k < n0 := by omega
      have hnp := Nat.find_min hbound hkn0
      simp only [not_not] at hnp
      have hxe : x = q 0 + ((k : ℤ) + 1) := by rw [hj, hk]; push_cast; ring
      rw [hxe]; exact hnp
  refine ⟨e, by omega, ?_, hxint⟩
  by_contra hesup
  apply hPfind
  have he1 : (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc :=
    hxint (e - 1) (by omega) (by omega)
  have hh : (![(e - 1) + 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc := by
    apply kns_right_mem_interior Vc he1
    simpa using hesup
  simpa using hh

/-- The bottom-wall property of the escape row, applied to the last site `(e - 1, q 1)` of the run.
-/
theorem gtp_runEnd_bottomCorner_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} {q : Site 2} {M e : ℤ}
    (hbottom : ∀ wx : ℤ, (-M < wx ∧ wx ≤ M) →
      (![wx, q 1] : Site 2) ∈ jil_offSupportInterior Vc →
      (![wx, q 1] : Site 2) ∉ T →
      (![wx, q 1 - 1] : Site 2) ∈ Vc.support)
    (hlastbox : -M < e - 1 ∧ e - 1 ≤ M)
    (hlastI : (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hlastnT : (![e - 1, q 1] : Site 2) ∉ T) :
    (![e - 1, q 1 - 1] : Site 2) ∈ Vc.support :=
  hbottom (e - 1) hlastbox hlastI hlastnT

/-- Residual hypothesis: as `ewt_BottomWallThick`, also given the east end `e` of the escape run
(the first walk site east of `q`, with the sites between interior).

Weaker than `ewt_BottomWallThick`. For a four-thin walk and an interior seed it is equivalent to
`ksc_NoKingSeparation Vc seed`. -/
def gtp_RunEndReconnect {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) :
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
      (∀ (e : ℤ), q 0 < e → (![e, q 1] : Site 2) ∈ Vc.support →
        (∀ x : ℤ, q 0 ≤ x → x < e → (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc) →
        kns_ThickPoint Vc)

/-- `etp_EscapeWallThick` implies `gtp_RunEndReconnect`. -/
theorem gtp_runEndReconnect_of_escapeWallThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hetp : etp_EscapeWallThick Vc seed) :
    gtp_RunEndReconnect Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin _hqbox _hq1box hW hS hcorner _hbottom
    _e _he₁ _he₂ _he₃
  exact hetp T hseedT hTsub hsat M q hqI hqnT hmin hW hS hcorner

/-- `ewt_BottomWallThick` implies `gtp_RunEndReconnect`. -/
theorem gtp_runEndReconnect_of_bottomWallThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hewt : ewt_BottomWallThick Vc seed) :
    gtp_RunEndReconnect Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hcorner hbottom
    _e _he₁ _he₂ _he₃
  exact hewt T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hcorner hbottom

/-- The fjord satisfies `gtp_RunEndReconnect` because it has a thick point. -/
theorem gtp_fjord_runEndReconnect : gtp_RunEndReconnect sdc_fjord (![5, 1] : Site 2) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => kns_fjord_thickPoint

/-- The fjord has a king separation, a thick point, and satisfies `gtp_RunEndReconnect`; it is not
four-thin. -/
theorem gtp_fjord_nonvacuous :
    kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    gtp_RunEndReconnect sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ⟨kns_fjord_kingSeparation, kns_fjord_thickPoint, gtp_fjord_runEndReconnect,
   mci_fjord_not_fourThin⟩

/-- The staircase walk `ksd_stair` satisfies `gtp_RunEndReconnect` from `(1, 1)`. -/
theorem gtp_ksd_runEndReconnect : gtp_RunEndReconnect ksd_stair (![1, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hqbox _hq1box _hW _hS _hcorner _hbottom _heast
  exact absurd (ksc_ksd_noKingSeparation T hseedT hTsub hsat hqI) hqnT

/-- The staircase walk `kda_stairDR` satisfies `gtp_RunEndReconnect` from `(3, 1)`. -/
theorem gtp_kda_runEndReconnect : gtp_RunEndReconnect kda_stairDR (![3, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hqbox _hq1box _hW _hS _hcorner _hbottom _heast
  exact absurd (ksc_kda_noKingSeparation T hseedT hTsub hsat hqI) hqnT

end Lattice

end StatMech
