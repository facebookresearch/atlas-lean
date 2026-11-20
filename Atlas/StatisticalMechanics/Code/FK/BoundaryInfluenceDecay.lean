/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.FK.DecayOfCorrelations
import Code.FK.FiniteVolumeShift

open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}





theorem fbd_sub_tendsto_zero_of_eq_limit {f g : ℕ → ℝ} {L : ℝ}
    (hf : Tendsto f atTop (𝓝 L)) (hg : Tendsto g atTop (𝓝 L)) :
    Tendsto (fun k => f k - g k) atTop (𝓝 0) := by
  have := hf.sub hg
  simpa using this



theorem fbd_sub_tendsto_zero_of_limits_eq {f g : ℕ → ℝ} {L M : ℝ}
    (hf : Tendsto f atTop (𝓝 L)) (hg : Tendsto g atTop (𝓝 M)) (hLM : L = M) :
    Tendsto (fun k => f k - g k) atTop (𝓝 0) := by
  subst hLM
  exact fbd_sub_tendsto_zero_of_eq_limit hf hg
























theorem fbd_decay_of_wired_density_eq (N : ℕ) (eb eb' : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (hdens : wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb') p) :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0) :=
  fbd_sub_tendsto_zero_of_limits_eq
    (dfi_wired_density_eq_limit N eb hp hp1) (dfi_wired_density_eq_limit N eb' hp hp1) hdens






theorem fbd_decay_of_free_density_eq (N : ℕ) (eb eb' : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (hdens : freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N eb') p) :
    Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0) :=
  fbd_sub_tendsto_zero_of_limits_eq
    (dfi_free_density_eq_limit N eb hp hp1) (dfi_free_density_eq_limit N eb' hp hp1) hdens












theorem fbd_decay_cross_of_density_eq (N : ℕ) (eb eb' : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (hdens : wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N eb') p) :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0) :=
  fbd_sub_tendsto_zero_of_limits_eq
    (dfi_wired_density_eq_limit N eb hp hp1) (dfi_free_density_eq_limit N eb' hp hp1) hdens















theorem fbd_decay_boxSym_wired (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) :=
  fbd_decay_of_wired_density_eq N eb (Sym2.map (S.lift N) eb) hp hp1
    (fbd_wired_density_eq_boxSym S N eb hp hp1)



theorem fbd_decay_boxSym_free (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) :=
  fbd_decay_of_free_density_eq N eb (Sym2.map (S.lift N) eb) hp hp1
    (fbd_free_density_eq_boxSym S N eb hp hp1)













theorem fbd_decay_interior_at_continuity (N : ℕ) (eb : Sym2 (boxVerts d N))
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
  exact fbd_decay_cross_of_density_eq N eb eb hp0 hp1
    (doc_free_eq_wired_at_continuity d N eb hsecant ⟨hp0, hp1⟩ hcont).symm









theorem fbd_decay_cross_boxSym_at_continuity (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
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
  refine fbd_decay_cross_of_density_eq N eb (Sym2.map (S.lift N) eb) hp0 hp1 ?_
  
  have huniq : freeEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb) p :=
    doc_free_eq_wired_at_continuity d N eb hsecant ⟨hp0, hp1⟩ hcont
  have hbox : freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p :=
    fbd_free_density_eq_boxSym S N eb hp0 hp1
  rw [← huniq, hbox]
























theorem fbd_centred_eq_translated_wired (m : ℕ) (v : Site d) (eb : Sym2 (boxVerts d m))
    {p q : ℝ} :
    edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) eb
      = edgeMargProb (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p q)
          (Sym2.map (fvs_transEquiv d m v) eb) :=
  (fvs_box_translation_edgeMarg d m v eb).1.symm




theorem fbd_centred_eq_translated_free (m : ℕ) (v : Site d) (eb : Sym2 (boxVerts d m))
    {p q : ℝ} :
    edgeMargProb (fkProb (boxGraph d m) p q) eb
      = edgeMargProb (fkProb (fvs_transBoxGraph d m v) p q) (Sym2.map (fvs_transEquiv d m v) eb) :=
  (fvs_box_translation_edgeMarg d m v eb).2.symm



















theorem fbd_decay_translate_wired (N : ℕ) (v : Site d) (eb : Sym2 (boxVerts d N)) {p q : ℝ} :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p q)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb
              (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p q)
              (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb)))
        atTop (𝓝 0) := by
  have hzero : (fun k =>
      edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p q)
          (innerEdgeLE d (Nat.le_add_right N k) eb)
        - edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p q)
            (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb)))
      = (fun _ => (0:ℝ)) := by
    funext k
    rw [← fbd_centred_eq_translated_wired (N+k) v (innerEdgeLE d (Nat.le_add_right N k) eb),
      sub_self]
  rw [hzero]
  exact tendsto_const_nhds



theorem fbd_decay_translate_free (N : ℕ) (v : Site d) (eb : Sym2 (boxVerts d N)) {p q : ℝ} :
    Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N+k)) p q)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (fvs_transBoxGraph d (N+k) v) p q)
              (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb)))
        atTop (𝓝 0) := by
  have hzero : (fun k =>
      edgeMargProb (fkProb (boxGraph d (N+k)) p q)
          (innerEdgeLE d (Nat.le_add_right N k) eb)
        - edgeMargProb (fkProb (fvs_transBoxGraph d (N+k) v) p q)
            (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb)))
      = (fun _ => (0:ℝ)) := by
    funext k
    rw [← fbd_centred_eq_translated_free (N+k) v (innerEdgeLE d (Nat.le_add_right N k) eb),
      sub_self]
  rw [hzero]
  exact tendsto_const_nhds
























theorem fbd_decay_iff_wired_density_eq (N : ℕ) (eb eb' : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0))
      ↔ wiredEdgeDensity d 2 (edgeIncl d N eb) p
          = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
  constructor
  · intro hdecay
    have hsub := (dfi_wired_density_eq_limit N eb hp hp1).sub
      (dfi_wired_density_eq_limit N eb' hp hp1)
    have := tendsto_nhds_unique hsub hdecay
    linarith [this]
  · intro hdens
    exact fbd_decay_of_wired_density_eq N eb eb' hp hp1 hdens



theorem fbd_decay_iff_free_density_eq (N : ℕ) (eb eb' : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0))
      ↔ freeEdgeDensity d 2 (edgeIncl d N eb) p
          = freeEdgeDensity d 2 (edgeIncl d N eb') p := by
  constructor
  · intro hdecay
    have hsub := (dfi_free_density_eq_limit N eb hp hp1).sub
      (dfi_free_density_eq_limit N eb' hp hp1)
    have := tendsto_nhds_unique hsub hdecay
    linarith [this]
  · intro hdens
    exact fbd_decay_of_free_density_eq N eb eb' hp hp1 hdens













theorem fbd_wired_density_translation_inv (v x y : Site d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (N : ℕ) (hx : x ∈ box d N) (hy : y ∈ box d N)
    (hx' : fktc_translate v x ∈ box d N) (hy' : fktc_translate v y ∈ box d N)
    (hdecay : Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy))
          - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0)) :
    wiredEdgeDensity d 2 s(x, y) p
      = wiredEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p :=
  fktc_wired_density_translation_inv v x y hp hp1 ⟨N, hx, hy, hx', hy', hdecay⟩


















noncomputable def fbd_offCentreCarrier (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N))
    (p q : ℝ) (k : ℕ) : ℝ :=
  edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p q)
      (innerEdgeLE d (Nat.le_add_right N k) eb')
    - edgeMargProb
        (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p q)
        (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb'))


















theorem fbd_wired_density_eq_of_offCentreCarrier (N : ℕ) (v : Site d)
    (eb eb' : Sym2 (boxVerts d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcarrier : Tendsto (fbd_offCentreCarrier N v eb' p 2) atTop (𝓝 0))
    (htrans : ∀ k,
        edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2)
            (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb'))
          = edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
  
  have hC' := dfi_wired_density_eq_limit N eb' hp hp1
  
  have hC := dfi_wired_density_eq_limit N eb hp hp1
  
  have hT : Tendsto (fun k =>
      edgeMargProb
          (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2)
          (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')))
      atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p)) := by
    refine hC.congr (fun k => (htrans k).symm)
  
  
  have hdiff : Tendsto (fun k =>
      edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) eb')
        - edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2)
            (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')))
      atTop (𝓝 0) := hcarrier
  
  have hsum := hdiff.add hT
  simp only [zero_add] at hsum
  have hcong : Tendsto (fun k =>
      edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) eb'))
      atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p)) := by
    refine hsum.congr (fun k => ?_)
    ring
  exact (tendsto_nhds_unique hC' hcong).symm

end FK

end StatMech
