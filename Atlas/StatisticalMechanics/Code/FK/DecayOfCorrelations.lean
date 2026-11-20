/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.FK.BoundaryDecay
import Code.FK.FKUniquenessClose3
import Code.FK.FKUniquenessClose2

open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}













noncomputable def docGap (d N : ℕ) (eb : Sym2 (boxVerts d N)) (p : ℝ) : ℝ :=
  wiredEdgeDensity d 2 (edgeIncl d N eb) p - freeEdgeDensity d 2 (edgeIncl d N eb) p



theorem docGap_nonneg (d N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ docGap d N eb p := by
  have := freeEdgeDensity_q2_le_wiredEdgeDensity d N eb hp hp1
  unfold docGap; linarith





theorem docGap_tendsto (d N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop (𝓝 (docGap d N eb p)) :=
  fbd_wired_free_gap_tendsto N eb hp hp1



















theorem doc_countable_density_discont (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    {p : ℝ | p ∈ Ioo (0:ℝ) 1 ∧
      ¬ ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p}.Countable :=
  (wiredEdgeDensity_q2_monotoneOn d N eb).countable_not_continuousWithinAt





















theorem doc_gap_zero_at_continuity (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
    {p : ℝ} (hpmem : p ∈ Ioo (0:ℝ) 1)
    (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
    docGap d N eb p = 0 := by
  have h := heq_at_cont_q2_of_secant d N eb hsecant p hpmem hcont
  unfold docGap; linarith [h]



theorem doc_free_eq_wired_at_continuity (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
    {p : ℝ} (hpmem : p ∈ Ioo (0:ℝ) 1)
    (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p :=
  heq_at_cont_q2_of_secant d N eb hsecant p hpmem hcont








theorem doc_gap_zero_off_countable (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ p ∈ Ioo (0:ℝ) 1, p ∉ S → docGap d N eb p = 0 := by
  refine ⟨{p : ℝ | p ∈ Ioo (0:ℝ) 1 ∧
      ¬ ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p},
    doc_countable_density_discont d N eb, ?_⟩
  intro p hpmem hpS
  have hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p := by
    by_contra hc
    exact hpS ⟨hpmem, hc⟩
  exact doc_gap_zero_at_continuity d N eb hsecant hpmem hcont







theorem doc_countable_gap_pos (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p) :
    {p : ℝ | p ∈ Ioo (0:ℝ) 1 ∧ docGap d N eb p ≠ 0}.Countable := by
  refine (doc_countable_density_discont d N eb).mono ?_
  intro p hp
  simp only [mem_setOf_eq] at hp ⊢
  obtain ⟨hpmem, hne⟩ := hp
  refine ⟨hpmem, fun hcont => hne ?_⟩
  exact doc_gap_zero_at_continuity d N eb hsecant hpmem hcont






















theorem doc_wired_free_interior_gap_decay_at_continuity (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
    {p : ℝ} (hpmem : p ∈ Ioo (0:ℝ) 1)
    (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop (𝓝 0) := by
  obtain ⟨hp0, hp1⟩ := hpmem
  have hgap : docGap d N eb p = 0 := doc_gap_zero_at_continuity d N eb hsecant ⟨hp0, hp1⟩ hcont
  have htend := docGap_tendsto d N eb hp0 hp1
  rwa [hgap] at htend










theorem doc_decay_at_continuity_wired (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) :=
  fbd_boundary_decay_boxSym S N eb

















theorem doc_decay_at_continuity (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
    {p : ℝ} (hpmem : p ∈ Ioo (0:ℝ) 1)
    (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) := by
  obtain ⟨hp0, hp1⟩ := hpmem
  
  have hW := dfi_wired_density_eq_limit N eb hp0 hp1
  have hF := dfi_free_density_eq_limit N (Sym2.map (S.lift N) eb) hp0 hp1
  have hsub := hW.sub hF
  
  have hfe' : freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p
      = freeEdgeDensity d 2 (edgeIncl d N eb) p :=
    (fbd_free_density_eq_boxSym S N eb hp0 hp1).symm
  have heq := doc_free_eq_wired_at_continuity d N eb hsecant ⟨hp0, hp1⟩ hcont
  have hzero : wiredEdgeDensity d 2 (edgeIncl d N eb) p
      - freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p = 0 := by
    rw [hfe']; linarith [heq]
  rwa [hzero] at hsub






















theorem doc_translate_density_eq_at_continuity (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
    {p : ℝ} (hpmem : p ∈ Ioo (0:ℝ) 1)
    (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p
      ∧ wiredEdgeDensity d 2 (edgeIncl d N eb) p
          = wiredEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p
      ∧ freeEdgeDensity d 2 (edgeIncl d N eb) p
          = freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
  obtain ⟨hp0, hp1⟩ := hpmem
  exact ⟨doc_free_eq_wired_at_continuity d N eb hsecant ⟨hp0, hp1⟩ hcont,
    fbd_wired_density_eq_boxSym S N eb hp0 hp1,
    fbd_free_density_eq_boxSym S N eb hp0 hp1⟩












theorem doc_gap_boxSym_eq (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    docGap d N (Sym2.map (S.lift N) eb) p = docGap d N eb p := by
  unfold docGap
  rw [← fbd_wired_density_eq_boxSym S N eb hp hp1, ← fbd_free_density_eq_boxSym S N eb hp hp1]

end FK

end StatMech
