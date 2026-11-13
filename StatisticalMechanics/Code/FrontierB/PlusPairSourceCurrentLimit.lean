/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.BoundarySourceParity
import Code.FrontierB.PlusPairSourceBoxCurrent
import Code.FrontierB.PairSourceCurrentLimit
import Code.FrontierB.InfiniteCurrentFiniteMarginals

open Filter MeasureTheory
open scoped ENNReal

namespace StatMech.FrontierB

open Lattice


noncomputable def growingPlusPairSourceCurrentMeasure
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (k : ℕ) : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
  let hNk : N ≤ k + N := Nat.le_add_left N k
  plusPairSourceBoxCurrentMeasure d (k + N) beta hbeta
    (pairSourceBoxSite x (box_mono d hNk hx))
    (pairSourceBoxSite y (box_mono d hNk hy))
    (pairSourceBoxSite_ne _ _ hxy)



theorem growingPlusPairSourceCurrentMeasure_edge_inverse_tail_le
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (k : ℕ) (e : Sym2 (Site d)) (K : ℕ) (hK : 0 < K) :
    (growingPlusPairSourceCurrentMeasure
      d N beta hbeta x y hx hy hxy k :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m e} ≤
      ENNReal.ofReal (2 * Real.exp beta) / K := by
  let n := k + N
  let xn : StatMech.FK.boxVerts d n :=
    pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)
  let yn : StatMech.FK.boxVerts d n :=
    pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy)
  let hxnyn : xn ≠ yn := pairSourceBoxSite_ne _ _ hxy
  by_cases he : e ∈ Set.range (boxCurrentEdgeIncl d (n + 1))
  · obtain ⟨eb, rfl⟩ := he
    rw [show growingPlusPairSourceCurrentMeasure
        d N beta hbeta x y hx hy hxy k =
      plusPairSourceBoxCurrentMeasure d n beta hbeta xn yn hxnyn by rfl,
      plusPairSourceBoxCurrentMeasure_edge_tail]
    calc
      (boundarySourceCurrentPMF (StatMech.FK.boxGraph d (n + 1)) beta
          (fun _ => 1) hbeta.le (fun _ => by positivity)
          (boxCurrentInterior d (n + 1)) {boxSiteSucc xn, boxSiteSucc yn}
          (plusPairBoundarySourceCurrentSum_pos
            d n beta hbeta xn yn hxnyn)).toMeasure {m | K ≤ m eb} ≤
          ENNReal.ofReal (2 * Real.exp beta / K) :=
        boundarySourceCurrentPMF_edge_inverse_tail_le
          (StatMech.FK.boxGraph d (n + 1)) beta hbeta
          (boxCurrentInterior d (n + 1)) {boxSiteSucc xn, boxSiteSucc yn}
          (plusPairBoundarySourceCurrentSum_pos
            d n beta hbeta xn yn hxnyn) eb K hK
      _ = ENNReal.ofReal (2 * Real.exp beta) / K := by
        rw [← ENNReal.ofReal_natCast K,
          ← ENNReal.ofReal_div_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)]
  · change Measure.map (extendBoxCurrent d (n + 1)) _ {m | K ≤ m e} ≤ _
    have hset : MeasurableSet
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K ≤ m e} :=
      (measurable_pi_apply e) MeasurableSet.of_discrete
    rw [Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hset]
    have hpre : extendBoxCurrent d (n + 1) ⁻¹' {m | K ≤ m e} = ∅ := by
      ext m
      simp [extendBoxCurrent_outside d (n + 1) m e he,
        Nat.not_le_of_gt hK]
    rw [hpre]
    simp

theorem growingPlusPairSourceCurrentMeasure_tight
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    IsTightMeasureSet (Set.range fun k =>
      (growingPlusPairSourceCurrentMeasure
        d N beta hbeta x y hx hy hxy k :
          Measure (InfiniteCurrentConfig (Sym2 (Site d))))) := by
  exact isTightMeasureSet_range_of_uniform_inverse_tail
    (growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy)
    (ENNReal.ofReal (2 * Real.exp beta)) ENNReal.ofReal_ne_top
    (growingPlusPairSourceCurrentMeasure_edge_inverse_tail_le
      d N beta hbeta x y hx hy hxy)



theorem growingPlusPairSourceCurrentMeasure_subsequence
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((growingPlusPairSourceCurrentMeasure
            d N beta hbeta x y hx hy hxy) ∘ phi) nu := by
  exact weakCurrent_subsequence_of_tight
    (growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy)
    (growingPlusPairSourceCurrentMeasure_tight
      d N beta hbeta x y hx hy hxy)

theorem growingPlusPairSourceCurrentMeasure_subsequence_with_cylinders
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((growingPlusPairSourceCurrentMeasure
            d N beta hbeta x y hx hy hxy) ∘ phi) nu ∧
        ∀ (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)),
          Tendsto
            (fun k => growingPlusPairSourceCurrentMeasure
              d N beta hbeta x y hx hy hxy (phi k)
                (currentCylinder S A)) atTop
            (nhds (nu (currentCylinder S A))) := by
  obtain ⟨nu, phi, hphi, hweak⟩ :=
    growingPlusPairSourceCurrentMeasure_subsequence
      d N beta hbeta x y hx hy hxy
  exact ⟨nu, phi, hphi, hweak, hweak.cylinder⟩

end StatMech.FrontierB
