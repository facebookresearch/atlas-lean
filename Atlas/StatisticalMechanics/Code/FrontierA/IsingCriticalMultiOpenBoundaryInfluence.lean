/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalBoundaryInfluence










open Filter MeasureTheory Topology

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Lattice StatMech.ConfigSpace StatMech.FK

noncomputable section



theorem isingCritical_centeredBox_multiOpen_extremalGap_tendsto_zero
    (T : Finset (Site 3)) :
    Tendsto (fun n =>
      (gvPlusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
          (fmu_multiOpen T) -
        (gvMinusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
          (fmu_multiOpen T)) atTop (nhds 0) := by
  let radius : Nat -> Nat := fun n => n
  have hradius : Tendsto radius atTop atTop := tendsto_id
  have hplus :=
    (isingCritical_varyingFiniteGibbs_tendsto
      (fun _ => plusField 3) radius hradius).tendsto_integral
        (iti_monomialBcf T)
  have hminus :=
    (isingCritical_varyingFiniteGibbs_tendsto
      (fun _ => minusField 3) radius hradius).tendsto_integral
        (iti_monomialBcf T)
  have hsub := hplus.sub hminus
  simp_rw [iti_integral_monomialBcf] at hsub
  dsimp only [radius] at hsub
  change Tendsto (fun n =>
      (plusMeasure 3 n (Ising.betaC 3) 0 :
          Measure (ConfigSpace (Site 3))).real (fmu_multiOpen T) -
        (minusMeasure 3 n (Ising.betaC 3) 0 :
          Measure (ConfigSpace (Site 3))).real (fmu_multiOpen T))
      atTop (nhds (_ - _)) at hsub
  simpa only [← iptp_gvPlusMeasure_eq_plusMeasure,
    ← iptm_gvMinusMeasure_eq_minusMeasure, sub_self] using hsub



theorem image_add_image_sub_self (x : Site 3) (T : Finset (Site 3)) :
    (T.image (fun y => x + y)).image (fun y => -x + y) = T := by
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    simpa using hw
  · intro hy
    refine ⟨x + y, ⟨y, hy, rfl⟩, ?_⟩
    simp




theorem gvMeasure_multiOpen_sub_abs_le_critical_centeredGap
    (Sout : Finset (Site 3)) (eta zeta : ConfigSpace (Site 3))
    (x : Site 3) (r : Nat) (T : Finset (Site 3))
    (hcontain :
      (boxFinset 3 r).image
        (fun y => Multiplicative.ofAdd x • y) ⊆ Sout) :
    |(gvMeasure eta Sout (Ising.betaC 3) 0).real
          (fmu_multiOpen (T.image (fun y => x + y))) -
        (gvMeasure zeta Sout (Ising.betaC 3) 0).real
          (fmu_multiOpen (T.image (fun y => x + y)))| ≤
      (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          (fmu_multiOpen T) -
        (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          (fmu_multiOpen T) := by
  let Sin : Finset (Site 3) :=
    (boxFinset 3 r).image (fun y => Multiplicative.ofAdd x • y)
  let Tx : Finset (Site 3) := T.image (fun y => x + y)
  have hraw := gvMeasure_real_sub_abs_le_inner_extremal_gap
    (Sin := Sin) (Sout := Sout) hcontain
    isingBetaC_three_pos.le (by norm_num : (0 : Real) ≤ 0)
    eta zeta (fmu_multiOpen_measurable Tx)
    (fmu_multiOpen_isIncreasing Tx)
  have hplus := iptp_gvPlus_real_shift (Multiplicative.ofAdd x)
    (boxFinset 3 r) (Ising.betaC 3) 0 Tx
  have hminus := iptm_gvMinus_real_shift (Multiplicative.ofAdd x)
    (boxFinset 3 r) (Ising.betaC 3) 0 Tx
  have hsites : Tx.image
      (fun y => (Multiplicative.ofAdd x)⁻¹ • y) = T := by
    change Tx.image (fun y => -x + y) = T
    exact image_add_image_sub_self x T
  rw [hsites] at hplus hminus
  change
    (gvPlusMeasure ((boxFinset 3 r).image (fun y => x + y))
        (Ising.betaC 3) 0).real (fmu_multiOpen Tx) = _ at hplus
  change
    (gvMinusMeasure ((boxFinset 3 r).image (fun y => x + y))
        (Ising.betaC 3) 0).real (fmu_multiOpen Tx) = _ at hminus
  dsimp [Sin, Tx] at hraw ⊢
  rw [hplus, hminus] at hraw
  exact hraw




theorem isingCritical_gvBoundary_translatedMultiOpen_sub_abs_tendsto_zero
    (Sout : Nat -> Finset (Site 3))
    (eta zeta : Nat -> ConfigSpace (Site 3))
    (x : Nat -> Site 3) (radius : Nat -> Nat)
    (T : Finset (Site 3))
    (hradius : Tendsto radius atTop atTop)
    (hcontain : forall n,
      (boxFinset 3 (radius n)).image
        (fun y => Multiplicative.ofAdd (x n) • y) ⊆ Sout n) :
    Tendsto (fun n =>
      |(gvMeasure (eta n) (Sout n) (Ising.betaC 3) 0).real
            (fmu_multiOpen (T.image (fun y => x n + y))) -
        (gvMeasure (zeta n) (Sout n) (Ising.betaC 3) 0).real
            (fmu_multiOpen (T.image (fun y => x n + y)))|)
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (Filter.Eventually.of_forall fun n =>
      gvMeasure_multiOpen_sub_abs_le_critical_centeredGap
        (Sout n) (eta n) (zeta n) (x n) (radius n) T (hcontain n))
  exact (isingCritical_centeredBox_multiOpen_extremalGap_tendsto_zero T).comp
    hradius

end

end StatMech.FrontierA
