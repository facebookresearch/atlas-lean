/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectAllSectorVerticalRate
import Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule



open Filter MeasureTheory Topology

namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation

noncomputable section





theorem
    tendsto_fkRectAllSectorNormalization_diagonal_zero_of_freePIMS
    {q : Real} (hq : 4 < q) (r : Nat)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (by linarith : 0 < q))
        (fkRectCriticalP_lt_one (by linarith : 0 < q))
        (by linarith : 0 < q) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0)
    (m : Nat → Nat)
    (hm : ∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) :
    Tendsto (fun k =>
      -Real.log (fkRectAllSectorNormalization
        (fkRectFixedChargeVerticalFamily r k (m k)) q) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds 0) := by
  let hq1 : 1 ≤ q := by linarith
  let c := FK.cFE (fkRectCriticalP q) q
  let p := fkRectFixedChargeFreeOneArm hq1 r
  let depth := fkRectPIMSDecayDepth (c / 4) p
  let threshold : Nat → Nat := fun k =>
    fkRectPIMSSublinearThreshold (depth k)
      (fkRectFixedChargeVerticalFamily r k (m k)).height
  have hc0 : 0 < c := by
    exact FK.cFE_pos
      (fkRectCriticalP_pos (by linarith : 0 < q))
      (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith)
  have hc1 : c ≤ 1 := fkRectCritical_cFE_le_one hq1
  have hp0 : ∀ k, 0 ≤ p k := fun _ => measureReal_nonneg
  have hp1 : ∀ k, p k ≤ 1 := fun _ => measureReal_le_one
  have hp : Tendsto p atTop (nhds 0) :=
    tendsto_fkRectFixedChargeFreeOneArm_zero_of_percolation_zero
      hq1 r hperc
  have scheduled :=
    fkRect_pimsDecay_scheduled_binomialSmallness hc0 hc1 p hp0 hp1 hp
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).width)
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).height)
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).height_pos)
      (fun k => by
        change fkRectPIMSHeightLower c
            (fkRectFixedChargeVerticalFamily r k (m k)).width ≤
          (fkRectFixedChargeVerticalFamily r k (m k)).height
        simp only [fkRectFixedChargeVerticalFamily_width,
          fkRectFixedChargeVerticalFamily_height]
        have hm' := hm k
        dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
        dsimp [c]
        omega)
  apply
    tendsto_allSectorNormalization_negLog_div_height_zero_of_boundaryIncidenceAdaptiveTail
      (fun k => fkRectFixedChargeVerticalFamily r k (m k)) hq threshold
  · intro k
    simpa [threshold, depth, p, c, fkRectFixedChargeFreeOneArm] using
      scheduled.1 k
  · have hupper : Tendsto (fun k : Nat => (1 : Real) / k)
        atTop (nhds 0) :=
      (tendsto_natCast_atTop_atTop (R := Real)).const_div_atTop 1
    apply squeeze_zero' (g := fun k : Nat => (1 : Real) / k)
    · filter_upwards [] with k
      positivity
    · filter_upwards [eventually_ge_atTop 1] with k hk
      let W := (fkRectFixedChargeVerticalFamily r k (m k)).width
      let H := (fkRectFixedChargeVerticalFamily r k (m k)).height
      have hm' := hm k
      have hmul : k * W ≤ m k := by
        dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
        exact (Nat.le_add_right _ _).trans hm'
      have hkreal : (0 : Real) < k := by exact_mod_cast hk
      have hHreal : (0 : Real) < H := by
        exact_mod_cast (fkRectFixedChargeVerticalFamily r k (m k)).height_pos
      apply (div_le_div_iff₀ hHreal hkreal).2
      have hnat : W * k ≤ H := by
        have hmk : W * k ≤ m k := by
          simpa [Nat.mul_comm] using hmul
        exact hmk.trans (by
          dsimp [H]
          omega)
      change (W : Real) * (k : Real) ≤ 1 * (H : Real)
      norm_num
      exact_mod_cast hnat
    · exact hupper
  · simpa [threshold, depth, p, c] using scheduled.2
  · refine tendsto_atTop.2 (fun N => ?_)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hm' := hm k
    dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
    have hmk : k ≤ m k := by
      have hw : 1 ≤ (fkRectFixedChargeVerticalFamily r k 0).width :=
        (fkRectFixedChargeVerticalFamily r k 0).width_pos
      exact (Nat.le_mul_of_pos_right k hw).trans
        ((Nat.le_add_right _ _).trans hm')
    simp only [fkRectFixedChargeVerticalFamily_height]
    omega



theorem tendsto_fkRectAllSectorNormalizationVerticalRate_zero_of_freePIMS
    {q : Real} (hq : 4 < q) (r : Nat)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (by linarith : 0 < q))
        (fkRectCriticalP_lt_one (by linarith : 0 < q))
        (by linarith : 0 < q) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0) :
    Tendsto (fkRectAllSectorNormalizationVerticalRate hq r)
      atTop (nhds 0) := by
  let f : Nat → Nat → Real := fun k m =>
    -Real.log (fkRectAllSectorNormalization
      (fkRectFixedChargeVerticalFamily r k m) q) /
        (fkRectFixedChargeVerticalFamily r k m).height
  let rate : Nat → Real := fkRectAllSectorNormalizationVerticalRate hq r
  have hvertical (k : Nat) : Tendsto (f k) atTop (nhds (rate k)) := by
    simpa [f, rate] using
      fkRectAllSectorNormalization_vertical_negLog_tendsto_rate hq r k
  have hchoose (k : Nat) : ∃ M : Nat, ∀ m : Nat, M ≤ m →
      dist (f k m) (rate k) < (1 : Real) / (k + 1) := by
    have heps : 0 < (1 : Real) / (k + 1) := by positivity
    have hev : ∀ᶠ m in atTop,
        f k m ∈ Metric.ball (rate k) ((1 : Real) / (k + 1)) :=
      hvertical k (Metric.ball_mem_nhds _ heps)
    obtain ⟨M, hM⟩ := eventually_atTop.1 hev
    exact ⟨M, fun m hm => by
      simpa only [Metric.mem_ball] using hM m hm⟩
  choose M hM using hchoose
  let schedule : Nat → Nat := fun k =>
    max (fkRectBoundaryIncidencePIMSHeightLower q r k) (M k)
  have hschedule (k : Nat) :
      fkRectBoundaryIncidencePIMSHeightLower q r k ≤ schedule k :=
    le_max_left _ _
  have hdiagonal : Tendsto (fun k => f k (schedule k))
      atTop (nhds 0) := by
    simpa [f] using
      tendsto_fkRectAllSectorNormalization_diagonal_zero_of_freePIMS
        hq r hperc schedule hschedule
  have herror : Tendsto (fun k => dist (rate k) (f k (schedule k)))
      atTop (nhds 0) := by
    have heps : Tendsto (fun k : Nat => (1 : Real) / (k + 1))
        atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    apply squeeze_zero (g := fun k : Nat => (1 : Real) / (k + 1))
    · intro k
      exact dist_nonneg
    · intro k
      rw [dist_comm]
      exact (hM k (schedule k) (le_max_right _ _)).le
    · exact heps
  apply (tendsto_iff_dist_tendsto_zero).2
  have hdiagDist : Tendsto (fun k => dist (f k (schedule k)) 0)
      atTop (nhds 0) :=
    (tendsto_iff_dist_tendsto_zero).1 hdiagonal
  apply squeeze_zero (g := fun k =>
      dist (rate k) (f k (schedule k)) +
        dist (f k (schedule k)) 0)
  · intro k
    exact dist_nonneg
  · intro k
    exact dist_triangle _ _ _
  · simpa using herror.add hdiagDist

end

end StatMech.FrontierD
