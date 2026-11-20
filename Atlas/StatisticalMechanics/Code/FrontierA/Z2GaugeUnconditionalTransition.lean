/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.Z2GaugeSurfaceTensionIdentification
import Code.FrontierA.Z2GaugeInternalCylinderLimit
import Code.FrontierA.IsingSurfaceTensionMeanfieldLower
import Code.FrontierA.IsingSurfaceTensionSheetPositionReduction
import Code.FrontierA.IsingSurfaceTensionSheetTiling















open Filter Topology

namespace StatMech.FrontierA




theorem rectangularIsingSurfaceTension_pos_of_triple_tiling
    {beta : Real} (hcritical : StatMech.Ising.betaC 3 < beta) :
    0 < rectangularIsingSurfaceTension beta :=
  rectangularIsingSurfaceTension_pos hcritical



theorem cubicalSquareWilson_eventually_areaLaw_unconditional
    {K : Real} (hK : 0 < K)
    (hbelow : K < gaugeCriticalCoupling (StatMech.Ising.betaC 3)) :
    ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonExpectation K n <=
        Real.exp
          (-(rectangularIsingSurfaceTension (gaugeDualCoupling K) / 2) *
            ((n + 1 : Nat) : Real) ^ 2) := by
  have hdualCritical :
      StatMech.Ising.betaC 3 < gaugeDualCoupling K :=
    (lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling
      hK isingBetaC_three_pos).2 hbelow
  apply cubicalSquareWilson_eventually_areaLaw hK
    (cubicalSquareWilsonDensity_tendsto_rectangularIsingSurfaceTension hK)
  exact rectangularIsingSurfaceTension_pos_of_triple_tiling hdualCritical




theorem cubicalRectangularWilson_areaLaw_unconditional
    {K : Real} (hK : 0 < K)
    (hbelow : K < gaugeCriticalCoupling (StatMech.Ising.betaC 3))
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    0 < rectangularIsingSurfaceTension (gaugeDualCoupling K) /\
      cubicalRectangularWilsonExpectation K m n <=
        Real.exp
          (-rectangularIsingSurfaceTension (gaugeDualCoupling K) *
            (m : Real) * (n : Real)) := by
  have hdualCritical :
      StatMech.Ising.betaC 3 < gaugeDualCoupling K :=
    (lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling
      hK isingBetaC_three_pos).2 hbelow
  have htauPos :=
    rectangularIsingSurfaceTension_pos_of_triple_tiling hdualCritical
  refine ⟨htauPos, ?_⟩
  have hrate := rectangularSurfaceRate_le_density
    (fun i j => cubicalRectangularWilsonFreeEnergy_nonneg hK i j) hm hn
  rw [cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension
    hK] at hrate
  have harea : 0 < (m : Real) * (n : Real) := by positivity
  have hfreeEnergy :
      rectangularIsingSurfaceTension (gaugeDualCoupling K) *
          ((m : Real) * (n : Real)) <=
        cubicalRectangularWilsonFreeEnergy K m n := by
    exact (le_div_iff₀ harea).mp hrate
  rw [cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation] at hfreeEnergy
  have hlog :
      Real.log (cubicalRectangularWilsonExpectation K m n) <=
        -rectangularIsingSurfaceTension (gaugeDualCoupling K) *
          (m : Real) * (n : Real) := by
    nlinarith
  have hWpos := cubicalRectangularWilsonExpectation_pos hK m n
  calc
    cubicalRectangularWilsonExpectation K m n =
        Real.exp (Real.log (cubicalRectangularWilsonExpectation K m n)) :=
      (Real.exp_log hWpos).symm
    _ <= Real.exp
        (-rectangularIsingSurfaceTension (gaugeDualCoupling K) *
          (m : Real) * (n : Real)) := Real.exp_le_exp.mpr hlog




theorem cubicalSquareWilson_eventually_areaLaw_of_prismComparison
    {K : Real} (hK : 0 < K)
    (hbelow : K < gaugeCriticalCoupling (StatMech.Ising.betaC 3))
    (hprism : HasPrismCubicalSurfaceComparison (gaugeDualCoupling K)) :
    ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonExpectation K n <=
        Real.exp
          (-(rectangularIsingSurfaceTension (gaugeDualCoupling K) / 2) *
            ((n + 1 : Nat) : Real) ^ 2) := by
  have hdualCritical : StatMech.Ising.betaC 3 < gaugeDualCoupling K :=
    (lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling
      hK isingBetaC_three_pos).2 hbelow
  apply cubicalSquareWilson_eventually_areaLaw hK
    (cubicalSquareWilsonDensity_tendsto_rectangularIsingSurfaceTension hK)
  exact rectangularIsingSurfaceTension_pos_of_prismComparison
    hdualCritical hprism




theorem cubicalSquareWilson_eventually_areaLaw_of_lower_ge_central
    {K : Real} (hK : 0 < K)
    (hbelow : K < gaugeCriticalCoupling (StatMech.Ising.betaC 3))
    (hposition : forall n, 0 < n ->
      centralCubicalIsingDisorderDensity (gaugeDualCoupling K) n <=
        oddCubicalIsingDisorderDensity (gaugeDualCoupling K) n) :
    ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonExpectation K n <=
        Real.exp
          (-(rectangularIsingSurfaceTension (gaugeDualCoupling K) / 2) *
            ((n + 1 : Nat) : Real) ^ 2) := by
  have hdualCritical : StatMech.Ising.betaC 3 < gaugeDualCoupling K :=
    (lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling
      hK isingBetaC_three_pos).2 hbelow
  apply cubicalSquareWilson_eventually_areaLaw hK
    (cubicalSquareWilsonDensity_tendsto_rectangularIsingSurfaceTension hK)
  exact rectangularIsingSurfaceTension_pos_of_lower_ge_central
    hdualCritical hposition





theorem cubicalZ2Gauge_unconditional_transition_data
    (K : Real) (hK : 0 < K) :
    (0 < gaugeCriticalCoupling (StatMech.Ising.betaC 3)) /\
    (Real.cosh (gaugeCriticalCoupling (StatMech.Ising.betaC 3)) /
        Real.sinh (gaugeCriticalCoupling (StatMech.Ising.betaC 3)) =
      Real.exp (2 * StatMech.Ising.betaC 3)) /\
    Tendsto (cubicalSquareWilsonDensity K) atTop
      (nhds (rectangularIsingSurfaceTension (gaugeDualCoupling K))) /\
    (gaugeCriticalCoupling (StatMech.Ising.betaC 3) < K ->
      ∃ decay, 0 < decay ∧ ∀ n,
        Real.exp
          (-(gaugePerimeterPenalty (Real.exp (-decay)) *
              (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) *
            centralSquareSide n) <=
          cubicalInfiniteVolumeWilsonExpectation K
            (centralSquareSide n) (centralSquareSide n)) := by
  have hbetaC : 0 < StatMech.Ising.betaC 3 := isingBetaC_three_pos
  refine ⟨gaugeCriticalCoupling_pos hbetaC,
    coth_gaugeCriticalCoupling hbetaC,
    cubicalSquareWilsonDensity_tendsto_rectangularIsingSurfaceTension hK,
    ?_⟩
  exact exists_cubicalInfiniteVolumeWilson_perimeterLower_of_critical_lt K hK





theorem cubicalZ2Gauge_sharp_transition
    (K : Real) (hK : 0 < K) :
    (0 < gaugeCriticalCoupling (StatMech.Ising.betaC 3)) /\
    (Real.cosh (gaugeCriticalCoupling (StatMech.Ising.betaC 3)) /
        Real.sinh (gaugeCriticalCoupling (StatMech.Ising.betaC 3)) =
      Real.exp (2 * StatMech.Ising.betaC 3)) /\
    (rectangularSurfaceRate (cubicalRectangularWilsonFreeEnergy K) =
      rectangularIsingSurfaceTension (gaugeDualCoupling K)) /\
    Tendsto (cubicalSquareWilsonDensity K) atTop
      (nhds (rectangularIsingSurfaceTension (gaugeDualCoupling K))) /\
    (K < gaugeCriticalCoupling (StatMech.Ising.betaC 3) ->
      0 < rectangularIsingSurfaceTension (gaugeDualCoupling K) /\
        ∀ m n : Nat, 0 < m -> 0 < n ->
          cubicalRectangularWilsonExpectation K m n <=
            Real.exp
              (-rectangularIsingSurfaceTension (gaugeDualCoupling K) *
                (m : Real) * (n : Real))) /\
    (gaugeCriticalCoupling (StatMech.Ising.betaC 3) < K ->
      ∃ decay, 0 < decay ∧ ∀ n,
        Real.exp
          (-(gaugePerimeterPenalty (Real.exp (-decay)) *
              (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) *
            centralSquareSide n) <=
          cubicalInfiniteVolumeWilsonExpectation K
            (centralSquareSide n) (centralSquareSide n)) := by
  rcases cubicalZ2Gauge_unconditional_transition_data K hK with
    ⟨hcriticalPos, hcoth, hdensity, hperimeter⟩
  exact ⟨hcriticalPos, hcoth,
    cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension hK,
    hdensity,
    fun hbelow => ⟨
      rectangularIsingSurfaceTension_pos_of_triple_tiling
        ((lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling
          hK isingBetaC_three_pos).2 hbelow),
      fun m n hm hn =>
        (cubicalRectangularWilson_areaLaw_unconditional
          hK hbelow hm hn).2⟩,
    hperimeter⟩

end StatMech.FrontierA
