/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionSheetTiling
import Code.FrontierA.Z2GaugeInternalCylinderLimit

open Filter Set Topology

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section



theorem rectangularIsingSurfaceTension_ge_meanfield_increment
    {a beta : Real} (ha : betaC 3 < a) (hab : a < beta) :
    2 * (Real.sqrt (1 - (betaC 3 / a) ^ 2)) ^ 2 * (beta - a) <=
      rectangularIsingSurfaceTension beta := by
  have hbetaC : 0 < betaC 3 := isingBetaC_three_pos
  have hsharp :=
    (ising_sharpness_unconditional (d := 3) (by norm_num)).1
  let c : Real :=
    2 * (Real.sqrt (1 - (betaC 3 / a) ^ 2)) ^ 2 * (beta - a)
  have ha0 : 0 < a := hbetaC.trans ha
  have hlower : forall n, c <= oddCubicalIsingDisorderDensity beta n := by
    intro n
    calc
      c <= standardCubicInterfaceDensity beta (3 * n + 1) := by
        dsimp [c]
        exact standardCubicInterfaceDensity_ge_meanfield_increment
          hbetaC hsharp ha hab (3 * n + 1) (by omega)
      _ = centralCubicalIsingDisorderDensity beta (3 * n + 1) :=
        standardCubicInterfaceDensity_eq_centralCubicalIsingDisorderDensity
          beta (3 * n + 1) (by omega)
      _ <= oddCubicalIsingDisorderDensity beta n :=
        centralCubicalIsingDisorderDensity_triple_le_odd
          (ha0.trans hab) n
  have hlim := oddCubicalIsingDisorderDensity_tendsto (ha0.trans hab)
  have hcle : c <= rectangularIsingSurfaceTension beta :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hlower)
  simpa [c] using hcle



theorem cubicalInfiniteVolumeWilsonFreeEnergy_le_of_perimeterLower
    {K C : Real} (hK : 0 < K) (n : Nat)
    (hlower :
      Real.exp (-C * centralSquareSide n) <=
        cubicalInfiniteVolumeWilsonExpectation K
          (centralSquareSide n) (centralSquareSide n)) :
    cubicalInfiniteVolumeWilsonFreeEnergy K
        (centralSquareSide n) (centralSquareSide n) <=
      C * centralSquareSide n := by
  have hwpos := cubicalInfiniteVolumeWilsonExpectation_pos hK
    (centralSquareSide n) (centralSquareSide n)
  have hlog := Real.log_le_log (Real.exp_pos _) hlower
  rw [Real.log_exp] at hlog
  unfold cubicalInfiniteVolumeWilsonFreeEnergy
  linarith




theorem exists_cubicalInfiniteVolumeWilsonFreeEnergy_perimeterUpper_of_dual_lt_betaC
    (K : Real) (hK : 0 < K) (hlt : gaugeDualCoupling K < betaC 3) :
    ∃ C > 0, ∀ n,
      cubicalInfiniteVolumeWilsonFreeEnergy K
          (centralSquareSide n) (centralSquareSide n) <=
        C * centralSquareSide n := by
  obtain ⟨decay, hdecay, hlower⟩ :=
    exists_cubicalInfiniteVolumeWilson_perimeterLower_of_dual_lt_betaC
      K hK hlt
  let C := gaugePerimeterPenalty (Real.exp (-decay)) *
    (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)
  have hR0 : 0 < Real.exp (-decay) := Real.exp_pos _
  have hR1 : Real.exp (-decay) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hC : 0 < C := by
    dsimp [C]
    have hden : 0 < 1 - Real.exp (-decay) := sub_pos.mpr hR1
    exact mul_pos (gaugePerimeterPenalty_pos hR0 hR1)
      (mul_pos (by norm_num) (pow_pos (inv_pos.mpr hden) 3))
  refine ⟨C, hC, fun n => ?_⟩
  apply cubicalInfiniteVolumeWilsonFreeEnergy_le_of_perimeterLower hK n
  simpa [C] using hlower n




def cubicalInfiniteVolumeSquareWilsonDensity (K : Real) (n : Nat) : Real :=
  cubicalInfiniteVolumeWilsonFreeEnergy K
      (centralSquareSide n) (centralSquareSide n) /
    ((centralSquareSide n : Nat) : Real) ^ 2

theorem cubicalInfiniteVolumeSquareWilsonDensity_nonneg
    {K : Real} (hK : 0 < K) (n : Nat) :
    0 <= cubicalInfiniteVolumeSquareWilsonDensity K n := by
  have hw := cubicalInfiniteVolumeWilsonExpectation_mem_Icc hK
    (centralSquareSide n) (centralSquareSide n)
  unfold cubicalInfiniteVolumeSquareWilsonDensity
  apply div_nonneg
  · unfold cubicalInfiniteVolumeWilsonFreeEnergy
    rw [neg_nonneg]
    exact Real.log_nonpos hw.1 hw.2
  · positivity




theorem cubicalInfiniteVolumeSquareWilsonDensity_tendsto_zero_of_dual_lt_betaC
    (K : Real) (hK : 0 < K) (hlt : gaugeDualCoupling K < betaC 3) :
    Tendsto (cubicalInfiniteVolumeSquareWilsonDensity K) atTop (nhds 0) := by
  obtain ⟨C, hC, hfree⟩ :=
    exists_cubicalInfiniteVolumeWilsonFreeEnergy_perimeterUpper_of_dual_lt_betaC
      K hK hlt
  have hupper : ∀ n,
      cubicalInfiniteVolumeSquareWilsonDensity K n <=
        C / ((centralSquareSide n : Nat) : Real) := by
    intro n
    have hs : (0 : Real) < (centralSquareSide n : Nat) := by
      positivity
    unfold cubicalInfiniteVolumeSquareWilsonDensity
    calc
      cubicalInfiniteVolumeWilsonFreeEnergy K
            (centralSquareSide n) (centralSquareSide n) /
          ((centralSquareSide n : Nat) : Real) ^ 2 <=
        (C * (centralSquareSide n : Nat)) /
          ((centralSquareSide n : Nat) : Real) ^ 2 := by
            exact div_le_div_of_nonneg_right (hfree n) (sq_nonneg _)
      _ = C / ((centralSquareSide n : Nat) : Real) := by
        field_simp
  have hvanish : Tendsto
      (fun n : Nat => C / ((centralSquareSide n : Nat) : Real))
      atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat C).comp
      (tendsto_add_atTop_nat 1)
    simpa [centralSquareSide, Function.comp_def] using h
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      cubicalInfiniteVolumeSquareWilsonDensity_nonneg hK n)
    (Filter.Eventually.of_forall hupper)
    hvanish

end

end StatMech.FrontierA
