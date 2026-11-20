/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.LeeYangPressureIdentification
import Code.Ising.PressureSurfaceVolume

open Filter Topology

namespace StatMech.FrontierA

open StatMech.FK StatMech.Ising StatMech.Lattice StatMech.Sharpness



theorem isingBoxPressureSeq_eq_freeBoxFvPressure
    (d : ℕ) (beta h : ℝ) (n : ℕ) :
    isingBoxPressureSeq d beta h n =
      Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h) /
        ((boxFinset d n).card : ℝ) := by
  unfold isingBoxPressureSeq isingBoxLogZ
  rw [sct_fvZ_eq_isingZ, psv_volume_card, ecz_boxVerts_card]
  let phi : boxGraph d n ≃g sctBoxGraph d n :=
    { toEquiv := Equiv.refl (boxVerts d n)
      map_rel_iff' := by
        intro x y
        change (hypercubicLattice d).Adj (x : Site d) (y : Site d) ↔
          (hypercubicLattice d).Adj (x : Site d) (y : Site d)
        rfl }
  have hZ : isingZ (boxGraph d n) beta h =
      isingZ (sctBoxGraph d n) beta h :=
    isingZ_relabel _ _ phi.toEquiv
      (fun x y => phi.map_rel_iff.symm) beta h
  rw [hZ]



theorem freeBoxFvPressure_tendsto_isingBoxPressureLimit
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    Tendsto
      (fun n => Real.log
        (fvZ (minusField d) n (bondFinsetInternal d n) beta h) /
          ((boxFinset d n).card : ℝ))
      atTop (nhds (isingBoxPressureLimit d hd beta h)) := by
  exact (isingBoxPressure_tendsto_limit d hd beta h).congr'
    (Filter.Eventually.of_forall fun n =>
      isingBoxPressureSeq_eq_freeBoxFvPressure d beta h n)



theorem minus_free_logFvZ_sub_abs_le
    (d n : ℕ) (beta h : ℝ) :
    |Real.log (fvZ (minusField d) n (bondFinsetTouch d n) beta h) -
        Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h)| ≤
      |beta| * ((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card :=
  logFvZ_sub_abs_le (minusField d) (minusField d) n
    (bondFinsetTouch d n) (bondFinsetInternal d n) beta h
    (bondFinsetInternal_subset_touch n)
    (fun tau _e he => bond_internal_indep
      (minusField d) (minusField d) n tau he)


theorem minus_free_pressure_indep
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    Tendsto (fun n =>
        Real.log (fvZ (minusField d) n (bondFinsetTouch d n) beta h) /
            ((boxFinset d n).card : ℝ) -
          Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h) /
            ((boxFinset d n).card : ℝ))
      atTop (nhds 0) :=
  normalized_diff_tendsto_zero
    (fun n => Real.log
      (fvZ (minusField d) n (bondFinsetTouch d n) beta h))
    (fun n => Real.log
      (fvZ (minusField d) n (bondFinsetInternal d n) beta h))
    (fun n => |beta| *
      (((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card : ℝ))
    (fun n => ((boxFinset d n).card : ℝ))
    (fun n => minus_free_logFvZ_sub_abs_le d n beta h)
    (fun n => boxFinset_card_pos n)
    (psv_ratio_tendsto_zero d hd beta)



theorem plusBoxFvPressure_tendsto_isingBoxPressureLimit
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    Tendsto
      (fun n => Real.log
        (fvZ (plusField d) n (bondFinsetTouch d n) beta h) /
          ((boxFinset d n).card : ℝ))
      atTop (nhds (isingBoxPressureLimit d hd beta h)) := by
  have hdiff := psv_plus_free_pressure_indep hd beta h
  have hfree := freeBoxFvPressure_tendsto_isingBoxPressureLimit d hd beta h
  have hsum := hdiff.add hfree
  simpa only [zero_add] using hsum.congr'
    (Filter.Eventually.of_forall fun n => by ring)



theorem minusBoxFvPressure_tendsto_isingBoxPressureLimit
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    Tendsto
      (fun n => Real.log
        (fvZ (minusField d) n (bondFinsetTouch d n) beta h) /
          ((boxFinset d n).card : ℝ))
      atTop (nhds (isingBoxPressureLimit d hd beta h)) := by
  have hdiff := minus_free_pressure_indep d hd beta h
  have hfree := freeBoxFvPressure_tendsto_isingBoxPressureLimit d hd beta h
  have hsum := hdiff.add hfree
  simpa only [zero_add] using hsum.congr'
    (Filter.Eventually.of_forall fun n => by ring)

end StatMech.FrontierA
