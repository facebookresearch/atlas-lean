/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionMeanfieldLower

open Filter Set Topology

namespace StatMech.FrontierA

noncomputable section


def oddCubicalLowerSheetFreeEnergy (beta : Real) (n : Nat) : Real :=
  let L := 2 * n + 1
  multibondDisorderFreeEnergy
    (cubicalDualEnds (a := L) (b := L) (c := L))
    (fun _ : CubicalPlaquette L L L => beta)
    (cubicalXYSheet (a := L) (b := L) (c := L) (0 : Fin (L + 1)))


def oddCubicalCentralSheetFreeEnergy (beta : Real) (n : Nat) : Real :=
  let L := 2 * n + 1
  multibondDisorderFreeEnergy
    (cubicalDualEnds (a := L) (b := L) (c := L))
    (fun _ : CubicalPlaquette L L L => beta)
    (cubicalXYSheet (a := L) (b := L) (c := L)
      (⟨n + 1, by omega⟩ : Fin (L + 1)))

theorem oddCubicalIsingDisorderDensity_eq_lowerSheetFreeEnergy_div
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    oddCubicalIsingDisorderDensity beta n =
      oddCubicalLowerSheetFreeEnergy beta n /
        (((2 * n + 1 : Nat) : Real) ^ 2) := by
  unfold oddCubicalIsingDisorderDensity rectangularSurfaceDensity
  rw [rectangularIsingDobrushinFreeEnergy_eq_disorder hbeta
    (by omega) (by omega)]
  unfold finiteRectangularIsingDisorderFreeEnergy
    oddCubicalLowerSheetFreeEnergy
  rw [Nat.max_self]
  rw [show (((2 * n + 1 : Nat) : Real) ^ 2) =
    ((2 * n + 1 : Nat) : Real) * ((2 * n + 1 : Nat) : Real) by ring]

theorem centralCubicalIsingDisorderDensity_eq_centralSheetFreeEnergy_div
    (beta : Real) (n : Nat) :
    centralCubicalIsingDisorderDensity beta n =
      oddCubicalCentralSheetFreeEnergy beta n /
        (((2 * n + 1 : Nat) : Real) ^ 2) := by
  rfl




theorem hasPrismCubicalSurfaceComparison_of_perimeter_bound
    {beta C : Real} (hbeta : 0 < beta)
    (hbound : forall n, 0 < n ->
      |oddCubicalCentralSheetFreeEnergy beta n -
          oddCubicalLowerSheetFreeEnergy beta n| <=
        C * ((2 * n + 1 : Nat) : Real)) :
    HasPrismCubicalSurfaceComparison beta := by
  rw [hasPrismCubicalSurfaceComparison_iff_centralSheet]
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  have hdenNat : Tendsto (fun n : Nat => 2 * n + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  have hden : Tendsto (fun n : Nat => (((2 * n + 1 : Nat) : Real)))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hdenNat
  have hupper : Tendsto (fun n : Nat => C / (((2 * n + 1 : Nat) : Real)))
      atTop (nhds 0) := hden.const_div_atTop C
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => abs_nonneg _)
    ?_ hupper
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [centralCubicalIsingDisorderDensity_eq_centralSheetFreeEnergy_div,
    oddCubicalIsingDisorderDensity_eq_lowerSheetFreeEnergy_div hbeta]
  have hL : (0 : Real) < ((2 * n + 1 : Nat) : Real) := by positivity
  rw [div_sub_div_same, abs_div, abs_of_pos (sq_pos_of_pos hL)]
  rw [div_le_iff₀ (sq_pos_of_pos hL)]
  convert hbound n (by omega) using 1
  field_simp



theorem rectangularIsingSurfaceTension_pos_of_lower_ge_central
    {beta : Real} (hcritical : StatMech.Ising.betaC 3 < beta)
    (hposition : forall n, 0 < n ->
      centralCubicalIsingDisorderDensity beta n <=
        oddCubicalIsingDisorderDensity beta n) :
    0 < rectangularIsingSurfaceTension beta := by
  have hbetaC : 0 < StatMech.Ising.betaC 3 := by
    have hbdd := StatMech.Sharpness.tildeBetaCIsingSet_bddAbove
      (d := 3) (by norm_num)
    have hcrit := StatMech.Sharpness.tildeBetaCIsing_pos
      (d := 3) (by norm_num)
    have hsqrt : forall gamma, StatMech.Sharpness.tildeBetaCIsing 3 <= gamma ->
        Real.sqrt (1 - (StatMech.Sharpness.tildeBetaCIsing 3 / gamma) ^ 2) <=
          StatMech.Ising.magnetization 3 gamma := fun gamma hgamma =>
      StatMech.Sharpness.sct_magnetization_meanfield_lower_bound_integrated
        3 hbdd hcrit hgamma
    rw [StatMech.Sharpness.bc_eq_ising_of_sqrt_and_susceptibility
      (d := 3) (by norm_num) hsqrt]
    exact hcrit
  have hsharp :=
    (StatMech.Sharpness.ising_sharpness_unconditional
      (d := 3) (by norm_num)).1
  let a : Real := (StatMech.Ising.betaC 3 + beta) / 2
  let c : Real :=
    2 * (Real.sqrt (1 - (StatMech.Ising.betaC 3 / a) ^ 2)) ^ 2 * (beta - a)
  have ha : StatMech.Ising.betaC 3 < a := by dsimp [a]; linarith
  have hab : a < beta := by dsimp [a]; linarith
  have ha0 : 0 < a := hbetaC.trans ha
  have hratio0 : 0 <= StatMech.Ising.betaC 3 / a :=
    div_nonneg hbetaC.le ha0.le
  have hratio1 : StatMech.Ising.betaC 3 / a < 1 := (div_lt_one ha0).2 ha
  have hrad : 0 < 1 - (StatMech.Ising.betaC 3 / a) ^ 2 := by nlinarith
  have hc : 0 < c := by
    dsimp [c]
    rw [Real.sq_sqrt hrad.le]
    positivity
  have hlower : forall n, 0 < n -> c <= oddCubicalIsingDisorderDensity beta n := by
    intro n hn
    calc
      c <= standardCubicInterfaceDensity beta n := by
        dsimp [c]
        exact standardCubicInterfaceDensity_ge_meanfield_increment
          hbetaC hsharp ha hab n hn
      _ = centralCubicalIsingDisorderDensity beta n :=
        standardCubicInterfaceDensity_eq_centralCubicalIsingDisorderDensity
          beta n hn
      _ <= oddCubicalIsingDisorderDensity beta n := hposition n hn
  have hlim := oddCubicalIsingDisorderDensity_tendsto
    (hbetaC.trans hcritical)
  have hcle : c <= rectangularIsingSurfaceTension beta :=
    ge_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact hlower n (by omega))
  exact hc.trans_le hcle

end

end StatMech.FrontierA
