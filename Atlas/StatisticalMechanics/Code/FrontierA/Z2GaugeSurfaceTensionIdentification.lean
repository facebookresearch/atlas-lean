/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionRectangularModel
import Code.FrontierA.IsingSurfaceTensionBoundaryBridge
import Code.FrontierA.Z2GaugeThermodynamicReduction

open Filter Topology

namespace StatMech.FrontierA

noncomputable section



theorem gaugeCriticalCoupling_gaugeDualCoupling
    {beta : Real} (hbeta : 0 < beta) :
    gaugeCriticalCoupling (gaugeDualCoupling beta) = beta := by
  unfold gaugeCriticalCoupling
  rw [exp_neg_two_mul_gaugeDualCoupling hbeta, Real.artanh_tanh]




theorem rectangularIsingDobrushinFreeEnergy_gaugeDualCoupling
    {beta : Real} (hbeta : 0 < beta) (m n : Nat) :
    rectangularIsingDobrushinFreeEnergy (gaugeDualCoupling beta) m n =
      cubicalRectangularWilsonFreeEnergy beta m n := by
  rw [rectangularIsingDobrushinFreeEnergy,
    rectangularDobrushinFreeEnergy,
    gaugeCriticalCoupling_gaugeDualCoupling hbeta]



theorem cubicalRectangularWilsonFreeEnergy_eq_finiteIsingDisorder
    {beta : Real} (hbeta : 0 < beta) {m n : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    cubicalRectangularWilsonFreeEnergy beta m n =
      finiteRectangularIsingDisorderFreeEnergy
        (gaugeDualCoupling beta) m n := by
  rw [← rectangularIsingDobrushinFreeEnergy_gaugeDualCoupling hbeta]
  exact rectangularIsingDobrushinFreeEnergy_eq_disorder
    (gaugeDualCoupling_pos hbeta) hm hn



theorem cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension
    {beta : Real} (hbeta : 0 < beta) :
    rectangularSurfaceRate (cubicalRectangularWilsonFreeEnergy beta) =
      rectangularIsingSurfaceTension (gaugeDualCoupling beta) := by
  unfold rectangularIsingSurfaceTension
  congr 1
  funext m n
  exact (rectangularIsingDobrushinFreeEnergy_gaugeDualCoupling
    hbeta m n).symm



theorem cubicalSquareWilsonDensity_tendsto_rectangularIsingSurfaceTension
    {beta : Real} (hbeta : 0 < beta) :
    Tendsto (cubicalSquareWilsonDensity beta) atTop
      (nhds (rectangularIsingSurfaceTension (gaugeDualCoupling beta))) := by
  rw [← cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension
    hbeta]
  exact cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate_unconditional
    hbeta



theorem cubicalSquareDisorderDensity_tendsto_rectangularIsingSurfaceTension
    {beta : Real} (hbeta : 0 < beta) :
    Tendsto (cubicalSquareDisorderDensity beta) atTop
      (nhds (rectangularIsingSurfaceTension (gaugeDualCoupling beta))) := by
  rw [← cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension
    hbeta]
  exact
    cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate_unconditional
      hbeta




theorem cubicalRectangularWilsonSurfaceRate_pos_iff_below_critical
    {beta betaIsingC : Real} (hbeta : 0 < beta) (hIsingC : 0 < betaIsingC)
    (hphase :
      0 < rectangularIsingSurfaceTension (gaugeDualCoupling beta) <->
        betaIsingC < gaugeDualCoupling beta) :
    0 < rectangularSurfaceRate (cubicalRectangularWilsonFreeEnergy beta) <->
      beta < gaugeCriticalCoupling betaIsingC := by
  rw [cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension
    hbeta, hphase]
  exact lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling hbeta hIsingC



theorem cubicalSquareWilson_eventually_areaLaw_of_rectangularIsing_phase
    {beta betaIsingC : Real} (hbeta : 0 < beta) (hIsingC : 0 < betaIsingC)
    (hphase :
      0 < rectangularIsingSurfaceTension (gaugeDualCoupling beta) <->
        betaIsingC < gaugeDualCoupling beta)
    (hbelow : beta < gaugeCriticalCoupling betaIsingC) :
    ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonExpectation beta n <=
        Real.exp
          (-(rectangularIsingSurfaceTension (gaugeDualCoupling beta) / 2) *
            ((n + 1 : Nat) : Real) ^ 2) := by
  apply cubicalSquareWilson_eventually_areaLaw hbeta
    (cubicalSquareWilsonDensity_tendsto_rectangularIsingSurfaceTension hbeta)
  exact hphase.mpr
    ((lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling
      hbeta hIsingC).mpr hbelow)




theorem standardCubicInterfaceDensity_tendsto_cubicalWilsonSurfaceRate
    {beta : Real} (hbeta : 0 < beta)
    (hprism : HasPrismCubicalSurfaceComparison beta)
    (hstandard : HasStandardPrismSurfaceComparison beta) :
    Tendsto (standardCubicInterfaceDensity beta) atTop
      (nhds (rectangularSurfaceRate
        (cubicalRectangularWilsonFreeEnergy
          (gaugeCriticalCoupling beta)))) := by
  have hlim :=
    standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension
      hbeta hprism hstandard
  have hrate :=
    cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension
      (gaugeCriticalCoupling_pos hbeta)
  rw [gaugeDualCoupling_gaugeCriticalCoupling hbeta] at hrate
  rwa [hrate]




theorem cubicalSquareWilson_eventually_areaLaw_of_weak_LebowitzPfister
    {betaGauge betaIsingC : Real}
    (hGauge : 0 < betaGauge) (hIsingC : 0 < betaIsingC)
    (hregime : StatMech.Ising.HasOrderedMagnetizationRegime
      (StatMech.Ising.magnetization 3) betaIsingC)
    (hupper : forall beta, 0 < beta ->
      rectangularIsingSurfaceTension beta <=
        2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
    (hweak : StatMech.Ising.HasWeakSurfaceTensionLowerBound 1
      (StatMech.Ising.magnetization 3) rectangularIsingSurfaceTension)
    (hbelow : betaGauge < gaugeCriticalCoupling betaIsingC) :
    ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonExpectation betaGauge n <=
        Real.exp
          (-(rectangularIsingSurfaceTension
              (gaugeDualCoupling betaGauge) / 2) *
            ((n + 1 : Nat) : Real) ^ 2) := by
  have hcriterion :=
    rectangularIsingSurfaceTension_pos_iff_ordered_of_weak_bounds_pos
      hregime hupper hweak
  have hphase :
      0 < rectangularIsingSurfaceTension (gaugeDualCoupling betaGauge) <->
        betaIsingC < gaugeDualCoupling betaGauge :=
    hcriterion _ (gaugeDualCoupling_pos hGauge)
  exact cubicalSquareWilson_eventually_areaLaw_of_rectangularIsing_phase
    hGauge hIsingC hphase hbelow




theorem cubicalSquareWilson_eventually_areaLaw_of_standard_interface_bounds
    {betaGauge betaIsingC : Real}
    (hGauge : 0 < betaGauge) (hIsingC : 0 < betaIsingC)
    (hregime : StatMech.Ising.HasOrderedMagnetizationRegime
      (StatMech.Ising.magnetization 3) betaIsingC)
    (hprism : forall beta, 0 < beta ->
      HasPrismCubicalSurfaceComparison beta)
    (hstandard : forall beta, 0 < beta ->
      HasStandardPrismSurfaceComparison beta)
    (hupper : forall n beta, 0 < beta ->
      standardCubicInterfaceDensity beta n <=
        2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
    (hweak : forall n,
      StatMech.Ising.HasWeakSurfaceTensionLowerBound 1
        (StatMech.Ising.magnetization 3)
        (fun beta => standardCubicInterfaceDensity beta n))
    (hbelow : betaGauge < gaugeCriticalCoupling betaIsingC) :
    ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonExpectation betaGauge n <=
        Real.exp
          (-(rectangularIsingSurfaceTension
              (gaugeDualCoupling betaGauge) / 2) *
            ((n + 1 : Nat) : Real) ^ 2) := by
  have hcriterion :=
    rectangularIsingSurfaceTension_pos_iff_ordered_of_standard_bounds
      hregime hprism hstandard hupper hweak
  have hphase :
      0 < rectangularIsingSurfaceTension (gaugeDualCoupling betaGauge) <->
        betaIsingC < gaugeDualCoupling betaGauge :=
    hcriterion _ (gaugeDualCoupling_pos hGauge)
  exact cubicalSquareWilson_eventually_areaLaw_of_rectangularIsing_phase
    hGauge hIsingC hphase hbelow

end

end StatMech.FrontierA
