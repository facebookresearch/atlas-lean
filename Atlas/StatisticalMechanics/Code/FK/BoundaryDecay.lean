/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.FK.TranslationCofinal
import Code.FK.Limits

open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}



















theorem fbd_free_le_wired_edgeMarg (m : ℕ) (e : Sym2 (boxVerts d m)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (fkProb (boxGraph d m) p 2) e
      ≤ edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e := by
  have hHolley := fkProb_le_wiredFkProb_increasing (boxGraph d m) (boxBoundary d m)
    hp hp1 (by norm_num : (1:ℝ) ≤ 2) (boxEdgeOpenEvent_isIncreasing d m e)
  
  have hfree : (∑ ω, (boxEdgeOpenEvent d m e).indicator (fun _ => (1 : ℝ)) ω
        * fkProb (boxGraph d m) p 2 ω)
      = edgeMargProb (fkProb (boxGraph d m) p 2) e := by
    unfold edgeMargProb
    exact Finset.sum_congr rfl fun ω _ => by rw [dfi_indicator_boxEdgeOpenEvent]
  have hwired : (∑ ω, (boxEdgeOpenEvent d m e).indicator (fun _ => (1 : ℝ)) ω
        * wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω)
      = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e := by
    unfold edgeMargProb
    exact Finset.sum_congr rfl fun ω _ => by rw [dfi_indicator_boxEdgeOpenEvent]
  rw [hfree, hwired] at hHolley
  exact hHolley





















theorem fbd_wired_free_gap_tendsto (N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop
      (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p
          - freeEdgeDensity d 2 (edgeIncl d N eb) p)) :=
  (dfi_wired_density_eq_limit N eb hp hp1).sub (dfi_free_density_eq_limit N eb hp hp1)










theorem fbd_wired_free_gap_nonneg (N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p ≤ wiredEdgeDensity d 2 (edgeIncl d N eb) p := by
  have hgap : (0 : ℝ) ≤ wiredEdgeDensity d 2 (edgeIncl d N eb) p
      - freeEdgeDensity d 2 (edgeIncl d N eb) p := by
    refine ge_of_tendsto (fbd_wired_free_gap_tendsto N eb hp hp1) ?_
    filter_upwards with k
    have := fbd_free_le_wired_edgeMarg (N+k) (innerEdgeLE d (Nat.le_add_right N k) eb) hp hp1
    linarith
  linarith






















theorem fbd_box_wired_edgeMarg_innerEdgeLE_boxSym (S : BoxSym d) (N m : ℕ) (hNm : N ≤ m)
    (eb : Sym2 (boxVerts d N)) {p : ℝ} :
    edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (innerEdgeLE d hNm eb)
      = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
          (innerEdgeLE d hNm (Sym2.map (S.lift N) eb)) := by
  rw [← S.lift_innerEdgeLE hNm eb,
    fkTI_box_wired_edgeMarg_inv S m (innerEdgeLE d hNm eb)]



theorem fbd_box_free_edgeMarg_innerEdgeLE_boxSym (S : BoxSym d) (N m : ℕ) (hNm : N ≤ m)
    (eb : Sym2 (boxVerts d N)) {p : ℝ} :
    edgeMargProb (fkProb (boxGraph d m) p 2) (innerEdgeLE d hNm eb)
      = edgeMargProb (fkProb (boxGraph d m) p 2) (innerEdgeLE d hNm (Sym2.map (S.lift N) eb)) := by
  rw [← S.lift_innerEdgeLE hNm eb, fkTI_box_free_edgeMarg_inv S m (innerEdgeLE d hNm eb)]
















theorem fbd_boundary_decay_boxSym (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ} :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) := by
  have hzero : (fun k =>
      edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) eb)
        - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb)))
      = (fun _ => (0 : ℝ)) := by
    funext k
    rw [fbd_box_wired_edgeMarg_innerEdgeLE_boxSym S N (N+k) (Nat.le_add_right N k) eb,
      sub_self]
  rw [hzero]
  exact tendsto_const_nhds




theorem fbd_boundary_decay_boxSym_free (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} :
    Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) := by
  have hzero : (fun k =>
      edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) eb)
        - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb)))
      = (fun _ => (0 : ℝ)) := by
    funext k
    rw [fbd_box_free_edgeMarg_innerEdgeLE_boxSym S N (N+k) (Nat.le_add_right N k) eb, sub_self]
  rw [hzero]
  exact tendsto_const_nhds





















theorem fbd_wired_density_eq_boxSym (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p :=
  fktc_wired_density_eq_of_marg_decay N eb (Sym2.map (S.lift N) eb) hp hp1
    (fbd_boundary_decay_boxSym S N eb)




theorem fbd_free_density_eq_boxSym (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p :=
  fktc_free_density_eq_of_marg_decay N eb (Sym2.map (S.lift N) eb) hp hp1
    (fbd_boundary_decay_boxSym_free S N eb)




















theorem fbd_wired_density_eq_boxSym_innerEdgeLE (S : BoxSym d) (N N' : ℕ) (hNN' : N ≤ N')
    (eb : Sym2 (boxVerts d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d N' (innerEdgeLE d hNN' eb)) p
      = wiredEdgeDensity d 2 (edgeIncl d N' (innerEdgeLE d hNN' (Sym2.map (S.lift N) eb))) p := by
  have hkey : innerEdgeLE d hNN' (Sym2.map (S.lift N) eb)
      = Sym2.map (S.lift N') (innerEdgeLE d hNN' eb) :=
    (S.lift_innerEdgeLE hNN' eb).symm
  rw [hkey]
  exact fbd_wired_density_eq_boxSym S N' (innerEdgeLE d hNN' eb) hp hp1

end FK

end StatMech
