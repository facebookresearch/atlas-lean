/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.PairSourceBoxCurrent
import Code.FrontierB.FreeBoxSpinLimit
import Code.FrontierB.FreeBoxCurrentParity
import Code.FrontierB.CurrentSelectionIndependence

open Filter MeasureTheory
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice


def pairSourceBoxSite {d n : ℕ} (x : Site d) (hx : x ∈ box d n) :
    StatMech.FK.boxVerts d n :=
  ⟨x, hx⟩

theorem pairSourceBoxSite_ne {d n : ℕ} {x y : Site d}
    (hx : x ∈ box d n) (hy : y ∈ box d n) (hxy : x ≠ y) :
    pairSourceBoxSite x hx ≠ pairSourceBoxSite y hy := by
  intro h
  exact hxy (congrArg Subtype.val h)



theorem boxSpinSupport_pair {d n : ℕ} {x y : Site d}
    (hx : x ∈ box d n) (hy : y ∈ box d n) :
    boxSpinSupport d n {x, y} =
      {pairSourceBoxSite x hx, pairSourceBoxSite y hy} := by
  ext z
  simp only [boxSpinSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hz
    rcases hz with hz | hz
    · left
      exact Subtype.ext hz
    · right
      exact Subtype.ext hz
  · rintro (hz | hz)
    · exact Or.inl (congrArg Subtype.val hz)
    · exact Or.inr (congrArg Subtype.val hz)


noncomputable def pairSourceBaseConstant
    (d N : ℕ) (beta : ℝ) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) : ℝ :=
  boxPairCorrelationConstant d N beta
    (pairSourceBoxSite x hx) (pairSourceBoxSite y hy)

theorem pairSourceBaseConstant_pos
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) :
    0 < pairSourceBaseConstant d N beta x y hx hy :=
  boxPairCorrelationConstant_pos d N beta hbeta _ _



theorem pairSourceBaseConstant_le_expectation
    (d N n : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (hNn : N ≤ n) :
    pairSourceBaseConstant d N beta x y hx hy ≤
      expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1)
        {pairSourceBoxSite x (box_mono d hNn hx),
          pairSourceBoxSite y (box_mono d hNn hy)} := by
  let xN := pairSourceBoxSite x hx
  let yN := pairSourceBoxSite y hy
  let xn := pairSourceBoxSite x (box_mono d hNn hx)
  let yn := pairSourceBoxSite y (box_mono d hNn hy)
  have hbase : pairSourceBaseConstant d N beta x y hx hy ≤
      expectationJ (StatMech.FK.boxGraph d N) beta (fun _ => 1) {xN, yN} :=
    boxPairCorrelationConstant_le_expectation d N beta hbeta xN yN
      (pairSourceBoxSite_ne hx hy hxy)
  calc
    pairSourceBaseConstant d N beta x y hx hy ≤
        expectationJ (StatMech.FK.boxGraph d N) beta (fun _ => 1) {xN, yN} := hbase
    _ = isingExpectation (sctBoxGraph d N) beta 0
          (spinProd (boxSpinSupport d N {x, y})) := by
      rw [boxSpinSupport_pair hx hy]
      simpa only [xN, yN, boxGraph_eq_sctBoxGraph] using
        (expectationJ_one_eq_isingExpectation
          (G := StatMech.FK.boxGraph d N) beta {xN, yN})
    _ ≤ isingExpectation (sctBoxGraph d n) beta 0
          (spinProd (boxSpinSupport d n {x, y})) :=
      isingExpectation_boxSpinSupport_mono d hNn beta hbeta.le {x, y}
        (by simpa using Set.pair_subset hx hy)
    _ = expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1) {xn, yn} := by
      rw [boxSpinSupport_pair (box_mono d hNn hx) (box_mono d hNn hy)]
      symm
      simpa only [xn, yn, boxGraph_eq_sctBoxGraph] using
        (expectationJ_one_eq_isingExpectation
          (G := StatMech.FK.boxGraph d n) beta {xn, yn})


noncomputable def growingPairSourceCurrentMeasure
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (k : ℕ) : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
  let hNk : N ≤ k + N := Nat.le_add_left N k
  pairSourceBoxCurrentMeasure d (k + N) beta hbeta
    (pairSourceBoxSite x (box_mono d hNk hx))
    (pairSourceBoxSite y (box_mono d hNk hy))
    (pairSourceBoxSite_ne _ _ hxy)



theorem growingPairSourceCurrentMeasure_edge_inverse_tail_le
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (k : ℕ) (e : Sym2 (Site d)) (K : ℕ) (hK : 0 < K) :
    (growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy k :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m e} ≤
      ENNReal.ofReal
          (Real.exp beta / pairSourceBaseConstant d N beta x y hx hy) / K := by
  let n := k + N
  let xn : StatMech.FK.boxVerts d n :=
    pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)
  let yn : StatMech.FK.boxVerts d n :=
    pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy)
  let hxnyn : xn ≠ yn := pairSourceBoxSite_ne _ _ hxy
  let c := pairSourceBaseConstant d N beta x y hx hy
  have hc : 0 < c := pairSourceBaseConstant_pos d N beta hbeta x y hx hy
  by_cases he : e ∈ Set.range (boxCurrentEdgeIncl d n)
  · obtain ⟨eb, rfl⟩ := he
    have hcorr : c ≤ expectationJ (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) {xn, yn} := by
      exact pairSourceBaseConstant_le_expectation d N n beta hbeta x y hx hy hxy
        (Nat.le_add_left N k)
    have htail := sourceCurrentMeasure_edge_inverse_tail_le
      (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le
      (fun _ => by positivity) {xn, yn}
      (boxCurrentSum_pair_pos d n beta hbeta xn yn hxnyn) eb c hc hcorr K hK
    rw [show growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy k =
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



theorem growingPairSourceCurrentMeasure_subsequence
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ phi) nu := by
  apply weakCurrent_subsequence_of_uniform_inverse_tail
    (growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy)
    (ENNReal.ofReal
      (Real.exp beta / pairSourceBaseConstant d N beta x y hx hy))
    ENNReal.ofReal_ne_top
  intro k e K hK
  exact growingPairSourceCurrentMeasure_edge_inverse_tail_le
    d N beta hbeta x y hx hy hxy k e K hK


theorem growingPairSourceCurrentMeasure_subsequence_with_cylinders
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ phi) nu ∧
        ∀ (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)),
          Tendsto
            (fun k => growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy
              (phi k) (currentCylinder S A)) atTop
            (nhds (nu (currentCylinder S A))) := by
  obtain ⟨nu, phi, hphi, hweak⟩ :=
    growingPairSourceCurrentMeasure_subsequence d N beta hbeta x y hx hy hxy
  exact ⟨nu, phi, hphi, hweak, hweak.cylinder⟩


structure PairSourceCurrentLimitData
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) where
  limit : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))
  subsequence : ℕ → ℕ
  strictMono_subsequence : StrictMono subsequence
  tendsto : WeakCurrentConverges
    ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ subsequence)
    limit

noncomputable def pairSourceCurrentLimitData
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    PairSourceCurrentLimitData d N beta hbeta x y hx hy hxy := by
  exact Classical.choice
    (show Nonempty (PairSourceCurrentLimitData d N beta hbeta x y hx hy hxy) from by
      obtain ⟨nu, phi, hphi, hweak⟩ :=
        growingPairSourceCurrentMeasure_subsequence d N beta hbeta x y hx hy hxy
      exact ⟨⟨nu, phi, hphi, hweak⟩⟩)


noncomputable def infinitePairSourceCurrentMeasure
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (pairSourceCurrentLimitData d N beta hbeta x y hx hy hxy).limit

noncomputable def pairSourceCurrentBoxSubsequence
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) : ℕ → ℕ :=
  (pairSourceCurrentLimitData d N beta hbeta x y hx hy hxy).subsequence

theorem pairSourceCurrentBoxSubsequence_strictMono
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    StrictMono (pairSourceCurrentBoxSubsequence
      d N beta hbeta x y hx hy hxy) :=
  (pairSourceCurrentLimitData d N beta hbeta x y hx hy hxy).strictMono_subsequence

theorem growingPairSourceCurrentMeasure_tendsto_infinite
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘
        pairSourceCurrentBoxSubsequence d N beta hbeta x y hx hy hxy)
      (infinitePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) :=
  (pairSourceCurrentLimitData d N beta hbeta x y hx hy hxy).tendsto



theorem freeBoxCurrentMeasure_tendsto_along_pairSource
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    WeakCurrentConverges
      (fun k => freeBoxCurrentMeasure d
        (pairSourceCurrentBoxSubsequence d N beta hbeta x y hx hy hxy k + N)
        beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) := by
  have hcofinal : Tendsto
      (fun k => pairSourceCurrentBoxSubsequence
        d N beta hbeta x y hx hy hxy k + N) atTop atTop :=
    ((strictMono_id.add_const N).comp
      (pairSourceCurrentBoxSubsequence_strictMono
        d N beta hbeta x y hx hy hxy)).tendsto_atTop
  exact (freeBoxCurrentMeasure_tendsto_full d beta hbeta).comp hcofinal



theorem pairSourceBox_expectation_eq_freeIntegral
    (d n : ℕ) (beta : ℝ) (x y : Site d)
    (hx : x ∈ box d n) (hy : y ∈ box d n) :
    expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1)
        {pairSourceBoxSite x hx, pairSourceBoxSite y hy} =
      ∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  rw [integral_freeMeasure_spinProd d n beta 0 {x, y}
    (by simpa using Set.pair_subset hx hy), boxSpinSupport_pair hx hy]
  simpa only [boxGraph_eq_sctBoxGraph] using
    (expectationJ_one_eq_isingExpectation
      (G := StatMech.FK.boxGraph d n) beta
      {pairSourceBoxSite x hx, pairSourceBoxSite y hy})



theorem growingPairSource_expectation_tendsto
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) :
    Tendsto
      (fun k => expectationJ (StatMech.FK.boxGraph d (k + N)) beta (fun _ => 1)
        {pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx),
          pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy)})
      atTop
      (nhds (∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  have hfull := integral_freeMeasure_spinProd_tendsto_freeState_of_nonneg_field
    d beta 0 hbeta.le (le_refl 0) ({x, y} : Finset (Site d))
  have hshift := hfull.comp (tendsto_add_atTop_nat N)
  simpa only [pairSourceBox_expectation_eq_freeIntegral] using hshift

end StatMech.FrontierB
