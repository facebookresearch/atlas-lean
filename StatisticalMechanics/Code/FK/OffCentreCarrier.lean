/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.FK.BoundaryInfluenceDecay

open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}






















theorem occ_translated_eq_centred_wired (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N))
    {p q : ℝ} (k : ℕ) :
    edgeMargProb
        (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p q)
        (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb'))
      = edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p q)
          (innerEdgeLE d (Nat.le_add_right N k) eb') :=
  (fbd_centred_eq_translated_wired (N+k) v (innerEdgeLE d (Nat.le_add_right N k) eb')).symm












theorem occ_translated_tendsto_wiredDensity (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun k =>
        edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2)
            (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')))
      atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb') p)) := by
  refine (dfi_wired_density_eq_limit N eb' hp hp1).congr (fun k => ?_)
  exact (occ_translated_eq_centred_wired N v eb' k).symm















theorem occ_translated_between_iv (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (k : ℕ) :
    freeEdgeDensity d 2 (edgeIncl d N eb') p
        ≤ edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2)
            (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')) := by
  rw [occ_translated_eq_centred_wired N v eb' k]
  calc freeEdgeDensity d 2 (edgeIncl d N eb') p
      ≤ wiredEdgeDensity d 2 (edgeIncl d N eb') p :=
        freeEdgeDensity_q2_le_wiredEdgeDensity d N eb' hp hp1
    _ ≤ edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) eb') :=
        dfi_wired_per_edge_ge N (N+k) (Nat.le_add_right N k) eb' hp hp1













theorem occ_free_eq_wired_at_continuity (N : ℕ) (eb' : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb') p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb') p)
    {p : ℝ} (hpmem : p ∈ Ioo (0:ℝ) 1)
    (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb')) (Ioo (0:ℝ) 1) p) :
    freeEdgeDensity d 2 (edgeIncl d N eb') p = wiredEdgeDensity d 2 (edgeIncl d N eb') p :=
  doc_free_eq_wired_at_continuity d N eb' hsecant hpmem hcont






theorem occ_free_eq_wired_off_countable (N : ℕ) (eb' : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb') p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb') p) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ p ∈ Ioo (0:ℝ) 1, p ∉ S →
      freeEdgeDensity d 2 (edgeIncl d N eb') p = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
  refine ⟨{p : ℝ | p ∈ Ioo (0:ℝ) 1 ∧
      ¬ ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb')) (Ioo (0:ℝ) 1) p},
    doc_countable_density_discont d N eb', ?_⟩
  intro p hpmem hpS
  have hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb')) (Ioo (0:ℝ) 1) p := by
    by_contra hc; exact hpS ⟨hpmem, hc⟩
  exact occ_free_eq_wired_at_continuity N eb' hsecant hpmem hcont
























theorem occ_offCentreCarrier_squeeze (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fbd_offCentreCarrier N v eb' p 2) atTop (𝓝 0) := by
  
  have hC := dfi_wired_density_eq_limit N eb' hp hp1
  
  have hT := occ_translated_tendsto_wiredDensity N v eb' hp hp1
  
  have := fbd_sub_tendsto_zero_of_eq_limit hC hT
  unfold fbd_offCentreCarrier
  exact this













theorem occ_offCentreCarrier_eq_zero (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N))
    (p q : ℝ) (k : ℕ) :
    fbd_offCentreCarrier N v eb' p q k = 0 := by
  unfold fbd_offCentreCarrier
  rw [← fbd_centred_eq_translated_wired (N+k) v (innerEdgeLE d (Nat.le_add_right N k) eb'),
    sub_self]














theorem occ_offCentreCarrier (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N)) (p : ℝ) :
    Tendsto (fbd_offCentreCarrier N v eb' p 2) atTop (𝓝 0) := by
  have hzero : fbd_offCentreCarrier N v eb' p 2 = fun _ => (0:ℝ) := by
    funext k; exact occ_offCentreCarrier_eq_zero N v eb' p 2 k
  rw [hzero]
  exact tendsto_const_nhds























theorem occ_wired_density_eq_of_translation_cofinal (N : ℕ) (v : Site d)
    (eb eb' : Sym2 (boxVerts d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htrans : ∀ k,
        edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2)
            (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb'))
          = edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb') p :=
  fbd_wired_density_eq_of_offCentreCarrier N v eb eb' hp hp1
    (occ_offCentreCarrier N v eb' p) htrans

end FK

end StatMech
