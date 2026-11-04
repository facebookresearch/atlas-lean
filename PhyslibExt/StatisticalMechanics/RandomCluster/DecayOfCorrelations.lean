/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BoundaryDecay
public import PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessFromSecant

/-!
# Vanishing of the free–wired gap for `q = 2` edge densities

The gap `φ^1_p(e open) - φ^0_p(e open)` between the wired and free `q = 2` infinite-volume edge
densities is the limit of the finite-volume gaps, and under the secant bound it vanishes at every
continuity point of the wired density, hence off a countable set.

## i. Overview

`docGap d N eb p` is the free–wired gap of the edge `eb` of `Λ_N`. It is nonnegative and is the
limit of the gaps between the wired and free edge marginals on growing boxes. The wired density is
monotone on `(0, 1)`, so it has countably many discontinuities; at a continuity point the secant
hypothesis `hsecant` closes the gap. Consequently the effect of the boundary condition on the
marginal of a fixed edge decays as the box grows, at all but countably many `p`. Box symmetries
preserve the gap.

## ii. Key results

- `docGap_tendsto` : the gap is the limit of finite-volume gaps.
- `doc_gap_zero_at_continuity`, `doc_gap_zero_off_countable` : the gap vanishes at continuity
  points and off a countable set, given `hsecant`.
- `doc_wired_free_interior_gap_decay_at_continuity` : decay of the finite-volume boundary effect.
- `doc_gap_boxSym_eq` : the gap is invariant under box symmetries.

## iii. Table of contents

- A. The free–wired gap
- B. The gap vanishes off a countable set
- C. Decay of boundary effects and symmetry

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 4.63.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}

/-! ## A. The free–wired gap -/

/-- The gap `φ^1_{p,2}(eb open) - φ^0_{p,2}(eb open)` between the wired and free infinite-volume
densities of the edge `eb` of `Λ_N`.
-/
noncomputable def docGap (d N : ℕ) (eb : Sym2 (boxVerts d N)) (p : ℝ) : ℝ :=
  wiredEdgeDensity d 2 (edgeIncl d N eb) p - freeEdgeDensity d 2 (edgeIncl d N eb) p

lemma docGap_nonneg (d N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ docGap d N eb p := by
  have := freeEdgeDensity_q2_le_wiredEdgeDensity d N eb hp hp1
  unfold docGap; linarith

lemma docGap_tendsto (d N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop (𝓝 (docGap d N eb p)) :=
  fbd_wired_free_gap_tendsto N eb hp hp1

/-! ## B. The gap vanishes off a countable set -/

lemma doc_countable_density_discont (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    {p : ℝ | p ∈ Ioo (0 : ℝ) 1 ∧
      ¬ ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) p}.Countable :=
  (wiredEdgeDensity_q2_monotoneOn d N eb).countable_not_continuousWithinAt

lemma doc_gap_zero_at_continuity (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
    {p : ℝ} (hpmem : p ∈ Ioo (0 : ℝ) 1)
    (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) p) :
    docGap d N eb p = 0 := by
  have h := heq_at_cont_q2_of_secant d N eb hsecant p hpmem hcont
  unfold docGap; linarith [h]

lemma doc_free_eq_wired_at_continuity (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
    {p : ℝ} (hpmem : p ∈ Ioo (0 : ℝ) 1)
    (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) p) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p :=
  heq_at_cont_q2_of_secant d N eb hsecant p hpmem hcont

lemma doc_gap_zero_off_countable (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ p ∈ Ioo (0 : ℝ) 1, p ∉ S → docGap d N eb p = 0 := by
  refine ⟨{p : ℝ | p ∈ Ioo (0 : ℝ) 1 ∧
      ¬ ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) p},
    doc_countable_density_discont d N eb, ?_⟩
  intro p hpmem hpS
  have hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) p := by
    by_contra hc
    exact hpS ⟨hpmem, hc⟩
  exact doc_gap_zero_at_continuity d N eb hsecant hpmem hcont

lemma doc_countable_gap_pos (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p) :
    {p : ℝ | p ∈ Ioo (0 : ℝ) 1 ∧ docGap d N eb p ≠ 0}.Countable := by
  refine (doc_countable_density_discont d N eb).mono ?_
  intro p hp
  simp only [mem_ofPred_eq] at hp ⊢
  obtain ⟨hpmem, hne⟩ := hp
  refine ⟨hpmem, fun hcont => hne ?_⟩
  exact doc_gap_zero_at_continuity d N eb hsecant hpmem hcont

/-! ## C. Decay of boundary effects and symmetry -/

lemma doc_wired_free_interior_gap_decay_at_continuity (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
    {p : ℝ} (hpmem : p ∈ Ioo (0 : ℝ) 1)
    (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) p) :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop (𝓝 0) := by
  obtain ⟨hp0, hp1⟩ := hpmem
  have hgap : docGap d N eb p = 0 := doc_gap_zero_at_continuity d N eb hsecant ⟨hp0, hp1⟩ hcont
  have htend := docGap_tendsto d N eb hp0 hp1
  rwa [hgap] at htend

lemma doc_decay_at_continuity_wired (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) :=
  fbd_boundary_decay_boxSym S N eb

lemma doc_decay_at_continuity (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
    {p : ℝ} (hpmem : p ∈ Ioo (0 : ℝ) 1)
    (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) p) :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
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

lemma doc_translate_density_eq_at_continuity (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
    {p : ℝ} (hpmem : p ∈ Ioo (0 : ℝ) 1)
    (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) p) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p
      ∧ wiredEdgeDensity d 2 (edgeIncl d N eb) p
          = wiredEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p
      ∧ freeEdgeDensity d 2 (edgeIncl d N eb) p
          = freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
  obtain ⟨hp0, hp1⟩ := hpmem
  exact ⟨doc_free_eq_wired_at_continuity d N eb hsecant ⟨hp0, hp1⟩ hcont,
    fbd_wired_density_eq_boxSym S N eb hp0 hp1,
    fbd_free_density_eq_boxSym S N eb hp0 hp1⟩

lemma doc_gap_boxSym_eq (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    docGap d N (Sym2.map (S.lift N) eb) p = docGap d N eb p := by
  unfold docGap
  rw [← fbd_wired_density_eq_boxSym S N eb hp hp1, ← fbd_free_density_eq_boxSym S N eb hp hp1]

end FK

end StatMech
