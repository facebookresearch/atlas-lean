/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.Z2GaugeCubicalTwoPointPrism
import Code.Sharpness.SimonPlusLimit
import Code.Ising.FVConsistencyProve

open MeasureTheory Filter Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section



theorem oddPrismPlusTwoPoint_eq_plusMeasure_pair
    (beta : Real) (n : Nat)
    (v w : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    oddPrismPlusTwoPoint 1 beta n v w =
        ∫ omega,
        spin omega (rectangularPrismSiteEquivSctBoxDobrushin n v).1 *
          spin omega (rectangularPrismSiteEquivSctBoxDobrushin n w).1
        ∂(plusMeasure 3 n beta 0 : Measure (ConfigSpace (Site 3))) := by
  rw [plusMeasure_coe, integral_fvMeasure_eq_sum]
  unfold oddPrismPlusTwoPoint fvProb
  rw [rectangularPrismPlusPartition_eq_fvZ]
  rw [← Equiv.sum_comp (rectangularPrismConfigEquivSctBoxDobrushin n)]
  rw [Finset.sum_div]
  simp only [mul_one]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [rectangularPrismPlusEnergy_eq_mul_fvEnergy,
    spin_glue_rectangularPrismConfigEquiv,
    spin_glue_rectangularPrismConfigEquiv]
  unfold fvWeight
  simp only [rectangularPrismSpin]
  ring_nf


theorem oddCubicalDualTwoPoint_eq_plusMeasure_pair
    (beta : Real) (n : Nat)
    (q r : CubicalCell (2 * n + 1) (2 * n + 1) (2 * n + 1)) :
    multibondIsingTwoPoint cubicalDualEnds
        (fun _ : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) => beta)
        (some q) (some r) =
      ∫ omega,
        spin omega
            (rectangularPrismSiteEquivSctBoxDobrushin n
              (oddCubicalCellEquivPrismSite n q)).1 *
          spin omega
            (rectangularPrismSiteEquivSctBoxDobrushin n
              (oddCubicalCellEquivPrismSite n r)).1
        ∂(plusMeasure 3 n beta 0 : Measure (ConfigSpace (Site 3))) := by
  calc
    multibondIsingTwoPoint cubicalDualEnds (fun _ => beta) (some q) (some r) =
        multibondIsingTwoPoint cubicalDualEnds
          (fun _ => beta * 1) (some q) (some r) := by simp
    _ = oddPrismPlusTwoPoint 1 beta n
          (oddCubicalCellEquivPrismSite n q)
          (oddCubicalCellEquivPrismSite n r) :=
      oddCubicalDualTwoPoint_eq_plusPrismTwoPoint 1 beta n q r
    _ = _ := oddPrismPlusTwoPoint_eq_plusMeasure_pair beta n _ _




theorem tendsto_finset_prod_one_sub
    {I : Type*} (s : Finset I) (corr : Nat -> I -> Real)
    (limitCorr : I -> Real)
    (hcorr : forall i, i ∈ s ->
      Tendsto (fun n => corr n i) atTop (nhds (limitCorr i))) :
    Tendsto (fun n => ∏ i ∈ s, (1 - corr n i)) atTop
      (nhds (∏ i ∈ s, (1 - limitCorr i))) := by
  apply tendsto_finsetProd
  intro i hi
  exact tendsto_const_nhds.sub (hcorr i hi)



theorem finiteCylinderProduct_le_of_tendsto
    {I : Type*} (s : Finset I) (corr : Nat -> I -> Real)
    (limitCorr : I -> Real) (wilson : Nat -> Real) (limitWilson : Real)
    (hcorr : forall i, i ∈ s ->
      Tendsto (fun n => corr n i) atTop (nhds (limitCorr i)))
    (hwilson : Tendsto wilson atTop (nhds limitWilson))
    (hfinite : forall n, (∏ i ∈ s, (1 - corr n i)) <= wilson n) :
    (∏ i ∈ s, (1 - limitCorr i)) <= limitWilson := by
  exact le_of_tendsto_of_tendsto
    (tendsto_finset_prod_one_sub s corr limitCorr hcorr) hwilson
    (Eventually.of_forall hfinite)

end

end StatMech.FrontierA
