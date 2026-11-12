/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.BoundarySourceSpin
import Code.FrontierB.PlusPairSourceBoxCurrent
import Code.FrontierB.PlusBoxCurrentParity
import Code.FrontierB.FreeBoxEvenLimit
import Code.FrontierB.PairSourceCurrentLimit

open MeasureTheory Filter

namespace StatMech.FrontierB

open Sharpness Ising Lattice
open StatMech.IsingFK

theorem spinProd_boxSiteSucc_extendInteriorPlus
    (d n : ℕ) (tau : ConfigSpace (StatMech.FK.boxVerts d n))
    (x y : StatMech.FK.boxVerts d n) :
    spinProd ({boxSiteSucc x, boxSiteSucc y} :
        Finset (StatMech.FK.boxVerts d (n + 1)))
        (extendInteriorPlus (boxCurrentInterior d (n + 1))
          ((boxCurrentInteriorConfigEquiv d n).symm tau)) =
      spinProd ({x.1, y.1} : Finset (Site d))
        (glue (plusField d) tau) := by
  have hx : spin
      (extendInteriorPlus (boxCurrentInterior d (n + 1))
        ((boxCurrentInteriorConfigEquiv d n).symm tau)) (boxSiteSucc x) =
      spin (glue (plusField d) tau) x.1 := by
    exact congrArg spinB
      (extendInteriorPlus_configEquiv_symm_eq_glue d n tau (boxSiteSucc x))
  have hy : spin
      (extendInteriorPlus (boxCurrentInterior d (n + 1))
        ((boxCurrentInteriorConfigEquiv d n).symm tau)) (boxSiteSucc y) =
      spin (glue (plusField d) tau) y.1 := by
    exact congrArg spinB
      (extendInteriorPlus_configEquiv_symm_eq_glue d n tau (boxSiteSucc y))
  by_cases hxy : x = y
  · subst y
    simpa [spinProd] using hx
  · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    rw [spinProd, Finset.prod_pair (boxSiteSucc_ne hxy), hx, hy,
      spinProd, Finset.prod_pair hval]



theorem plusPairBoundarySourceRatio_eq_plusIntegral
    (d n : ℕ) (beta : ℝ)
    (x y : StatMech.FK.boxVerts d n) :
    boundarySourceCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta
          (fun _ => 1) (boxCurrentInterior d (n + 1))
          {boxSiteSucc x, boxSiteSucc y} /
        boundaryCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta
          (fun _ => 1) (boxCurrentInterior d (n + 1)) =
      ∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  let G := StatMech.FK.boxGraph d (n + 1)
  let interior := boxCurrentInterior d (n + 1)
  let A : Finset (StatMech.FK.boxVerts d (n + 1)) :=
    {boxSiteSucc x, boxSiteSucc y}
  have hA : A ⊆ interior := by
    intro z hz
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact boxSiteSucc_interior x
    · exact boxSiteSucc_interior y
  rw [boundarySourceCurrentSum_div_boundaryCurrentSum
    G beta (fun _ => 1) interior A hA]
  let C : ℝ :=
    ((Finset.image (StatMech.FK.edgeIncl d (n + 1))
        G.edgeFinset \ bondFinsetTouch d n).card : ℝ)
  let E : ℝ := Real.exp (beta * C)
  have hE0 : E ≠ 0 := (Real.exp_pos _).ne'
  have hnum :
      (∑ s : ConfigSpace ↑interior,
        spinProd A (extendInteriorPlus interior s) *
          boltzmannJ G beta (fun _ => 1) (extendInteriorPlus interior s)) =
        E * ∑ tau : ConfigSpace (StatMech.FK.boxVerts d n),
          fvWeight (plusField d) n (bondFinsetTouch d n) beta 0 tau *
            spinProd ({x.1, y.1} : Finset (Site d))
              (glue (plusField d) tau) := by
    rw [← (boxCurrentInteriorConfigEquiv d n).symm.sum_comp,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tau htau
    rw [boltzmannJ_extendInteriorPlus_eq_fvWeight,
      spinProd_boxSiteSucc_extendInteriorPlus]
    change _ * (Real.exp (beta * C) * _) = E * (_ * _)
    rw [← show E = Real.exp (beta * C) from rfl]
    ring
  have hden : boundaryPartitionJ G beta (fun _ => 1) interior =
      E * fvZ (plusField d) n (bondFinsetTouch d n) beta 0 := by
    simpa only [G, interior, E, C] using
      boundaryPartitionJ_box_eq_fvZ d n beta
  rw [hnum, hden, mul_div_mul_left _ _ hE0]
  change _ = ∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega
    ∂fvMeasure (plusField d) n (bondFinsetTouch d n) beta 0
  rw [integral_fvMeasure_eq_sum]
  unfold fvProb
  rw [Finset.sum_div]
  congr 1
  funext tau
  ring



theorem growingPlusPairBoundarySourceRatio_tendsto
    (d N : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (x y : Site d) (hx : x ∈ box d N) (hy : y ∈ box d N) :
    Tendsto
      (fun k =>
        let n := k + N
        boundarySourceCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta
              (fun _ => 1) (boxCurrentInterior d (n + 1))
              {boxSiteSucc (pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)),
                boxSiteSucc (pairSourceBoxSite y
                  (box_mono d (Nat.le_add_left N k) hy))} /
            boundaryCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta
              (fun _ => 1) (boxCurrentInterior d (n + 1)))
      atTop
      (nhds (∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  have hbase := integral_plusMeasure_spinProd_full_tendsto
    d beta hbeta ({x, y} : Finset (Site d))
  have hshift : Tendsto (fun k : ℕ => k + N) atTop atTop :=
    (strictMono_id.add_const N).tendsto_atTop
  have hcomp := hbase.comp hshift
  simpa only [plusPairBoundarySourceRatio_eq_plusIntegral,
    pairSourceBoxSite, Function.comp_apply] using hcomp



theorem growingFreePairForPlusSwitching_expectation_tendsto
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : Site d) (hx : x ∈ box d N) (hy : y ∈ box d N) :
    Tendsto
      (fun k =>
        let n := k + N
        expectationJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
          {boxSiteSucc
              (pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)),
            boxSiteSucc
              (pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy))})
      atTop
      (nhds (∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  have hfull := integral_freeMeasure_spinProd_tendsto_freeState_of_nonneg_field
    d beta 0 hbeta.le (le_refl 0) ({x, y} : Finset (Site d))
  have hshift : Tendsto (fun k : ℕ => (k + N) + 1) atTop atTop :=
    (strictMono_id.add_const N |>.add_const 1).tendsto_atTop
  have hcomp := hfull.comp hshift
  have heq : ∀ k : ℕ,
      (∫ omega, spinProd ({x, y} : Finset (Site d)) omega
          ∂(freeMeasure d ((k + N) + 1) beta 0 :
            Measure (ConfigSpace (Site d)))) =
        expectationJ (StatMech.FK.boxGraph d ((k + N) + 1)) beta
          (fun _ => 1)
          {boxSiteSucc
              (pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)),
            boxSiteSucc
              (pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy))} := by
    intro k
    let hxk := box_mono d (Nat.le_add_left N k) hx
    let hyk := box_mono d (Nat.le_add_left N k) hy
    have h := pairSourceBox_expectation_eq_freeIntegral
      d ((k + N) + 1) beta x y
        (box_subset_succ d (k + N) hxk)
        (box_subset_succ d (k + N) hyk)
    symm
    simpa only [pairSourceBoxSite, boxSiteSucc] using h
  simpa only [Function.comp_apply] using
    hcomp.congr' (Filter.Eventually.of_forall heq)

end StatMech.FrontierB
