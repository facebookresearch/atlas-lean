/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierB.PlusPairSourceCurrentLimit
import Code.FrontierB.CurrentSelectionIndependence

open Filter MeasureTheory
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice



noncomputable def growingFreePairSourceCurrentMeasure
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (k : ℕ) : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
  let n := (k + N) + 1
  let hNn : N ≤ n := le_trans (Nat.le_add_left N k) (Nat.le_succ _)
  pairSourceBoxCurrentMeasure d n beta hbeta
    (pairSourceBoxSite x (box_mono d hNn hx))
    (pairSourceBoxSite y (box_mono d hNn hy))
    (pairSourceBoxSite_ne _ _ hxy)



theorem growingFreePairSourceCurrentMeasure_edge_inverse_tail_le
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (k : ℕ) (e : Sym2 (Site d)) (K : ℕ) (hK : 0 < K) :
    (growingFreePairSourceCurrentMeasure
      d N beta hbeta x y hx hy hxy k :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m e} ≤
      ENNReal.ofReal
          (Real.exp beta / pairSourceBaseConstant d N beta x y hx hy) / K := by
  let n := (k + N) + 1
  let hNn : N ≤ n := le_trans (Nat.le_add_left N k) (Nat.le_succ _)
  let xn : StatMech.FK.boxVerts d n :=
    pairSourceBoxSite x (box_mono d hNn hx)
  let yn : StatMech.FK.boxVerts d n :=
    pairSourceBoxSite y (box_mono d hNn hy)
  let hxnyn : xn ≠ yn := pairSourceBoxSite_ne _ _ hxy
  let c := pairSourceBaseConstant d N beta x y hx hy
  have hc : 0 < c := pairSourceBaseConstant_pos d N beta hbeta x y hx hy
  by_cases he : e ∈ Set.range (boxCurrentEdgeIncl d n)
  · obtain ⟨eb, rfl⟩ := he
    have hcorr : c ≤ expectationJ (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) {xn, yn} :=
      pairSourceBaseConstant_le_expectation
        d N n beta hbeta x y hx hy hxy hNn
    have htail := sourceCurrentMeasure_edge_inverse_tail_le
      (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le
      (fun _ => by positivity) {xn, yn}
      (boxCurrentSum_pair_pos d n beta hbeta xn yn hxnyn) eb c hc hcorr K hK
    rw [show growingFreePairSourceCurrentMeasure
        d N beta hbeta x y hx hy hxy k =
      pairSourceBoxCurrentMeasure d n beta hbeta xn yn hxnyn by rfl,
      pairSourceBoxCurrentMeasure_edge_tail]
    calc
      (sourceCurrentMeasure (StatMech.FK.boxGraph d n) beta
          (fun _ => 1) hbeta.le (fun _ => by positivity) {xn, yn}
          (boxCurrentSum_pair_pos d n beta hbeta xn yn hxnyn) :
            Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m eb} ≤
          ENNReal.ofReal (Real.exp beta / (c * K)) := by simpa using htail
      _ = ENNReal.ofReal (Real.exp beta / c) / K := by
        rw [← ENNReal.ofReal_natCast K,
          ← ENNReal.ofReal_div_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)]
        congr 1
        simp only [div_eq_mul_inv, mul_inv]
        ring
  · change Measure.map (extendBoxCurrent d n) _ {m | K ≤ m e} ≤ _
    have hset : MeasurableSet
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K ≤ m e} :=
      (measurable_pi_apply e) MeasurableSet.of_discrete
    rw [Measure.map_apply (measurable_extendBoxCurrent d n) hset]
    have hpre : extendBoxCurrent d n ⁻¹' {m | K ≤ m e} = ∅ := by
      ext m
      simp [extendBoxCurrent_outside d n m e he, Nat.not_le_of_gt hK]
    rw [hpre]
    simp



theorem plusFreeSourceCurrentMeasure_joint_subsequence
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ∃ (nuFree nuPlus : ProbabilityMeasure
        (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((growingFreePairSourceCurrentMeasure
            d N beta hbeta x y hx hy hxy) ∘ phi) nuFree ∧
        WeakCurrentConverges
          ((growingPlusPairSourceCurrentMeasure
            d N beta hbeta x y hx hy hxy) ∘ phi) nuPlus := by
  obtain ⟨nuFree, phiFree, hphiFree, hfree⟩ :=
    weakCurrent_subsequence_of_uniform_inverse_tail
      (growingFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy)
      (ENNReal.ofReal
        (Real.exp beta / pairSourceBaseConstant d N beta x y hx hy))
      ENNReal.ofReal_ne_top
      (growingFreePairSourceCurrentMeasure_edge_inverse_tail_le
        d N beta hbeta x y hx hy hxy)
  obtain ⟨nuPlus, phiPlus, hphiPlus, hplus⟩ :=
    weakCurrent_subsequence_of_uniform_inverse_tail
      ((growingPlusPairSourceCurrentMeasure
        d N beta hbeta x y hx hy hxy) ∘ phiFree)
      (ENNReal.ofReal (2 * Real.exp beta)) ENNReal.ofReal_ne_top
      (fun i e K hK =>
        growingPlusPairSourceCurrentMeasure_edge_inverse_tail_le
          d N beta hbeta x y hx hy hxy (phiFree i) e K hK)
  refine ⟨nuFree, nuPlus, phiFree ∘ phiPlus,
    hphiFree.comp hphiPlus, ?_, hplus⟩
  exact hfree.comp hphiPlus.tendsto_atTop


structure PlusFreeSourceJointLimitData
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) where
  freeSourceLimit : ProbabilityMeasure
    (InfiniteCurrentConfig (Sym2 (Site d)))
  plusSourceLimit : ProbabilityMeasure
    (InfiniteCurrentConfig (Sym2 (Site d)))
  subsequence : ℕ → ℕ
  strictMono_subsequence : StrictMono subsequence
  freeSource_tendsto : WeakCurrentConverges
    ((growingFreePairSourceCurrentMeasure
      d N beta hbeta x y hx hy hxy) ∘ subsequence) freeSourceLimit
  plusSource_tendsto : WeakCurrentConverges
    ((growingPlusPairSourceCurrentMeasure
      d N beta hbeta x y hx hy hxy) ∘ subsequence) plusSourceLimit

noncomputable def plusFreeSourceJointLimitData
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    PlusFreeSourceJointLimitData d N beta hbeta x y hx hy hxy := by
  exact Classical.choice
    (show Nonempty
      (PlusFreeSourceJointLimitData d N beta hbeta x y hx hy hxy) from by
      obtain ⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩ :=
        plusFreeSourceCurrentMeasure_joint_subsequence
          d N beta hbeta x y hx hy hxy
      exact ⟨⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩⟩)


noncomputable def infiniteFreePairSourceCurrentMeasure
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (plusFreeSourceJointLimitData d N beta hbeta x y hx hy hxy).freeSourceLimit


noncomputable def infinitePlusPairSourceCurrentMeasure
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (plusFreeSourceJointLimitData d N beta hbeta x y hx hy hxy).plusSourceLimit


noncomputable def plusFreeSourceCurrentSubsequence
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) : ℕ → ℕ :=
  (plusFreeSourceJointLimitData d N beta hbeta x y hx hy hxy).subsequence

theorem plusFreeSourceCurrentSubsequence_strictMono
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    StrictMono
      (plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy) :=
  (plusFreeSourceJointLimitData
    d N beta hbeta x y hx hy hxy).strictMono_subsequence

theorem growingFreePairSourceCurrentMeasure_tendsto_jointLimit
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      ((growingFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘
        plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy)
      (infiniteFreePairSourceCurrentMeasure
        d N beta hbeta x y hx hy hxy) :=
  (plusFreeSourceJointLimitData
    d N beta hbeta x y hx hy hxy).freeSource_tendsto

theorem growingPlusPairSourceCurrentMeasure_tendsto_jointLimit
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      ((growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘
        plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy)
      (infinitePlusPairSourceCurrentMeasure
        d N beta hbeta x y hx hy hxy) :=
  (plusFreeSourceJointLimitData
    d N beta hbeta x y hx hy hxy).plusSource_tendsto



theorem freeBoxCurrentMeasure_tendsto_along_plusFreeSource
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      (fun k => freeBoxCurrentMeasure d
        ((plusFreeSourceCurrentSubsequence
          d N beta hbeta x y hx hy hxy k + N) + 1) beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) := by
  have hcofinal : Tendsto
      (fun k => (plusFreeSourceCurrentSubsequence
        d N beta hbeta x y hx hy hxy k + N) + 1) atTop atTop :=
    (((strictMono_id.add_const N).add_const 1).comp
      (plusFreeSourceCurrentSubsequence_strictMono
        d N beta hbeta x y hx hy hxy)).tendsto_atTop
  exact (freeBoxCurrentMeasure_tendsto_full d beta hbeta).comp hcofinal



theorem plusBoxCurrentMeasure_tendsto_along_plusFreeSource
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      (fun k => plusBoxCurrentMeasure d
        ((plusFreeSourceCurrentSubsequence
          d N beta hbeta x y hx hy hxy k + N) + 1) beta hbeta.le)
      (infinitePlusCurrentMeasure d beta hbeta.le) := by
  have hcofinal : Tendsto
      (fun k => (plusFreeSourceCurrentSubsequence
        d N beta hbeta x y hx hy hxy k + N) + 1) atTop atTop :=
    (((strictMono_id.add_const N).add_const 1).comp
      (plusFreeSourceCurrentSubsequence_strictMono
        d N beta hbeta x y hx hy hxy)).tendsto_atTop
  exact (plusBoxCurrentMeasure_tendsto_full d beta hbeta).comp hcofinal

end StatMech.FrontierB
