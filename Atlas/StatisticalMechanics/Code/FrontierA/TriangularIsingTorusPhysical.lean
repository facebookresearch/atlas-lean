/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusShiftedAssembly
import Code.FrontierA.TriangularIsingTorusSectorSandwich
import Code.FrontierA.TriangularIsingSymbol
import Code.Onsager.KWDetLimit









open scoped BigOperators
open MeasureTheory

namespace StatMech.FrontierA

open StatMech.Onsager

theorem triangular_spinPhase_spaceRoot_mul_cos
    (L m n : Nat) [NeZero L] (a b : Fin 2) :
    (ons_spinPhase L a * ons_spaceRoot L ^ m) *
          (ons_spinPhase L b * ons_spaceRoot L ^ n) +
        ((ons_spinPhase L a * ons_spaceRoot L ^ m) *
          (ons_spinPhase L b * ons_spaceRoot L ^ n))⁻¹ =
      2 * (Real.cos
        (2 * Real.pi *
          ((m + (a.val : Real) / 2) + (n + (b.val : Real) / 2)) / L) :
        Complex) := by
  rw [ons_spinPhase_mul_spaceRoot_pow,
    ons_spinPhase_mul_spaceRoot_pow, ← Complex.exp_add]
  have hinv :
      (Complex.exp (Complex.I *
        ((2 * Real.pi *
          ((m + (a.val : Real) / 2) + (n + (b.val : Real) / 2)) / L :
            Real) : Complex)))⁻¹ =
        Complex.exp (-(Complex.I *
          ((2 * Real.pi *
            ((m + (a.val : Real) / 2) + (n + (b.val : Real) / 2)) / L :
              Real) : Complex))) :=
    (Complex.exp_neg _).symm
  rw [show Complex.I *
        ((2 * Real.pi * (m + (a.val : Real) / 2) / L : Real) : Complex) +
      Complex.I *
        ((2 * Real.pi * (n + (b.val : Real) / 2) / L : Real) : Complex) =
      Complex.I *
        ((2 * Real.pi *
          ((m + (a.val : Real) / 2) + (n + (b.val : Real) / 2)) / L :
            Real) : Complex) by push_cast; ring]
  rw [hinv, Complex.ofReal_cos, Complex.two_cos]
  congr 2 <;> ring



theorem triangularTorus_sector_tanh_sq_eq_highTempProduct
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I) :
    triangularTorusWeightedSpinCharacterSum L
        (triangularTorusEdgeWeight L
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (triangularIsingHighTempSymbol J1 J2 J3
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
  letI : NeZero L :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt (Fact.out : 2 < L))⟩
  rw [triangularTorus_sector_sq_eq_det L
    (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) rho a b hrho]
  rw [triangularTorusKWMatrix_det L
    (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) rho
    (ons_spinPhase L a) (ons_spinPhase L b) (ons_spaceRoot L)
    hrho (ons_spaceRoot_primitive L (NeZero.ne L))
    (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b)]
  apply Finset.prod_congr rfl
  intro j _
  rw [ons_spinPhase_spaceRoot_cos, ons_spinPhase_spaceRoot_cos,
    triangular_spinPhase_spaceRoot_mul_cos]
  norm_cast
  unfold triangularIsingHighTempSymbol
  ring



theorem triangularTorus_normalizedSector_sq_eq_symbolProduct
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I) :
    (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) *
        triangularTorusWeightedSpinCharacterSum L
          (triangularTorusEdgeWeight L
            (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b) ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (triangularIsingSymbol J1 J2 J3
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
  let C : Real := Real.cosh J1 * Real.cosh J2 * Real.cosh J3
  let W : Complex := triangularTorusWeightedSpinCharacterSum L
    (triangularTorusEdgeWeight L
      (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b
  have hW := triangularTorus_sector_tanh_sq_eq_highTempProduct
    L J1 J2 J3 rho a b hrho
  have hfactor (j : ZMod L × ZMod L) :
      (triangularIsingSymbol J1 J2 J3
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) =
        (C ^ 2 : Real) *
          triangularIsingHighTempSymbol J1 J2 J3
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) := by
    have hnorm := triangularIsingHighTempSymbol_mul_cosh_sq J1 J2 J3
      (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
      (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)
    have hreal :
        triangularIsingSymbol J1 J2 J3
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) =
          C ^ 2 * triangularIsingHighTempSymbol J1 J2 J3
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) := by
      rw [← hnorm]
      dsimp only [C]
      ring
    exact_mod_cast hreal
  change ((((C ^ (L * L) : Real) : Complex) * W) ^ 2) = _
  rw [mul_pow, hW]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    ZMod.card]
  push_cast
  have hpow : ((C : Complex) ^ (L * L)) ^ 2 =
      ((C : Complex) ^ 2) ^ (L * L) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hpow]




theorem triangularTorus_normalizedSector_log_norm_eq
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Real.log ‖
        (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) :
          Complex) *
          triangularTorusWeightedSpinCharacterSum L
            (triangularTorusEdgeWeight L
              (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b‖ =
      (1 / 2 : Real) *
        ∑ j : ZMod L × ZMod L,
          Real.log (triangularIsingSymbol J1 J2 J3
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)) := by
  let N : Complex :=
    (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) :
      Complex) *
      triangularTorusWeightedSpinCharacterSum L
        (triangularTorusEdgeWeight L
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b
  let factor : ZMod L × ZMod L -> Real := fun j =>
    triangularIsingSymbol J1 J2 J3
      (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
      (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)
  have hfactor (j : ZMod L × ZMod L) : 0 < factor j := hpos _ _
  have hsq : N ^ 2 = ((∏ j, factor j : Real) : Complex) := by
    rw [show (((∏ j, factor j : Real) : Real) : Complex) =
        ∏ j, (factor j : Complex) by push_cast; rfl]
    dsimp only [N, factor]
    exact triangularTorus_normalizedSector_sq_eq_symbolProduct
      L J1 J2 J3 rho a b hrho
  have hprod : 0 < ∏ j, factor j := Finset.prod_pos fun j _ => hfactor j
  have hnormsq : ‖N‖ ^ 2 = ∏ j, factor j := by
    calc
      ‖N‖ ^ 2 = ‖N ^ 2‖ := (norm_pow N 2).symm
      _ = ‖(((∏ j, factor j : Real) : Complex))‖ := congrArg norm hsq
      _ = ∏ j, factor j := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hprod]
  have hlog := congrArg Real.log hnormsq
  rw [Real.log_pow] at hlog
  have hlogprod : Real.log (∏ j, factor j) =
      ∑ j, Real.log (factor j) := by
    exact Real.log_prod fun j _ => (hfactor j).ne'
  rw [hlogprod] at hlog
  norm_num at hlog
  change Real.log ‖N‖ = _
  calc
    Real.log ‖N‖ = (1 / 2 : Real) * (2 * Real.log ‖N‖) := by ring
    _ = (1 / 2 : Real) * ∑ j, Real.log (factor j) := by rw [hlog]
    _ = _ := by rfl

theorem triangularTorus_normalizedSector_ne_zero
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) :
        Complex) *
        triangularTorusWeightedSpinCharacterSum L
          (triangularTorusEdgeWeight L
            (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b ≠ 0 := by
  intro hzero
  have hsq := triangularTorus_normalizedSector_sq_eq_symbolProduct
    L J1 J2 J3 rho a b hrho
  rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hsq
  have hprod :
      (∏ j : ZMod L × ZMod L,
        triangularIsingSymbol J1 J2 J3
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _ => (hpos _ _).ne'
  exact hprod (by exact_mod_cast hsq.symm)



theorem triangularIsingSymbol_riemann_tendsto_spinShift
    (J1 J2 J3 : Real) (a b : Fin 2)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun L : Nat => (2 * Real.pi / L) ^ 2 *
        ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          Real.log (triangularIsingSymbol J1 J2 J3
            (2 * Real.pi * (i + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j + (b.val : Real) / 2) / L)))
      Filter.atTop
      (nhds (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  have hs : (a.val : Real) / 2 ∈ Set.Icc (0 : Real) 1 := by
    fin_cases a <;> norm_num
  have ht : (b.val : Real) / 2 ∈ Set.Icc (0 : Real) 1 := by
    fin_cases b <;> norm_num
  have h := StatMech.Onsager.ons_riemann_periodic_two_shift
    (fun k1 k2 => Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))
    (continuous_log_triangularIsingSymbol_of_pos J1 J2 J3 hpos)
    (periodic_log_triangularIsingSymbol_left J1 J2 J3)
    ((a.val : Real) / 2) ((b.val : Real) / 2) hs ht
  rw [integral_log_triangularIsingSymbol_square_shift] at h
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h


noncomputable def triangularTorusNormalizedSectorSequence
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2) (n : Nat) : Complex := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  exact
    (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) :
      Complex) *
      triangularTorusWeightedSpinCharacterSum L
        (triangularTorusEdgeWeight L
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b


noncomputable def triangularTorusNormalizedSectorMaxSequence
    (J1 J2 J3 : Real) (rho : Complex) (n : Nat) : Real :=
  arfSectorNormMax fun a b =>
    triangularTorusNormalizedSectorSequence J1 J2 J3 rho a b n



noncomputable def triangularTorusRealEdgeWeight
    (L : Nat) (t1 t2 t3 : Real) :
    Sym2 (ZMod L × ZMod L) -> Real := fun edge =>
  if squareTorusHorizontalEdge L edge then t1
  else if triangularTorusVerticalEdge L edge then t2
  else t3

@[simp] theorem triangularTorusRealEdgeWeight_cast
    (L : Nat) (t1 t2 t3 : Real)
    (edge : Sym2 (ZMod L × ZMod L)) :
    (triangularTorusRealEdgeWeight L t1 t2 t3 edge : Complex) =
      triangularTorusEdgeWeight L t1 t2 t3 edge := by
  by_cases hhorizontal : squareTorusHorizontalEdge L edge
  · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight,
      hhorizontal]
  · by_cases hvertical : triangularTorusVerticalEdge L edge
    · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight,
        hhorizontal, hvertical]
    · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight,
        hhorizontal, hvertical]

private theorem real_tanh_nonneg {x : Real} (hx : 0 ≤ x) :
    0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le



theorem triangularTorusNormalizedEvenSubgraph_log_sandwich
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 : Real) (rho : Complex)
    (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2) (hJ3 : 0 ≤ J3) :
    let C := (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L)
    let weight := triangularTorusRealEdgeWeight L
      (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)
    let sector : Fin 2 -> Fin 2 -> Complex := fun a b =>
      (C : Complex) * triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) a b
    Real.log (arfSectorNormMax sector) ≤
        Real.log (C *
          inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) ∧
      Real.log (C *
          inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) ≤
        Real.log (arfSectorNormMax sector) + Real.log 2 := by
  dsimp only
  let weight := triangularTorusRealEdgeWeight L
    (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)
  let C := (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L)
  let E := inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight
  let sector : Fin 2 -> Fin 2 -> Complex := fun a b =>
    (C : Complex) * triangularTorusWeightedSpinCharacterSum L
      (fun edge => (weight edge : Complex)) a b
  have hweight : forall edge, 0 ≤ weight edge := by
    intro edge
    by_cases hhorizontal : squareTorusHorizontalEdge L edge
    · simp [weight, triangularTorusRealEdgeWeight, hhorizontal,
        real_tanh_nonneg hJ1]
    · by_cases hvertical : triangularTorusVerticalEdge L edge
      · simp [weight, triangularTorusRealEdgeWeight, hhorizontal, hvertical,
          real_tanh_nonneg hJ2]
      · simp [weight, triangularTorusRealEdgeWeight, hhorizontal, hvertical,
          real_tanh_nonneg hJ3]
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hE : 0 < E :=
    inhomogeneousEvenSubgraphSum_pos_of_nonneg
      (triangularTorusGraph L) weight hweight
  apply arfSector_log_sandwich (C * E) sector (mul_pos hC hE)
  · intro a b
    dsimp only [sector]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    exact mul_le_mul_of_nonneg_left
      (triangularTorusWeightedSpin_norm_le_evenSubgraphSum
        L hweight a b) hC.le
  · have harf := two_mul_triangularTorusEvenSubgraphSum_eq_spin L weight
    change (2 : Complex) * (E : Complex) = _ at harf
    dsimp only [sector]
    calc
      ((2 * (C * E) : Real) : Complex) = (C : Complex) * (2 * E) := by
        push_cast
        ring
      _ = (C : Complex) *
          (triangularTorusWeightedSpinCharacterSum L
              (fun edge => (weight edge : Complex)) 1 1 +
            triangularTorusWeightedSpinCharacterSum L
              (fun edge => (weight edge : Complex)) 0 1 +
            triangularTorusWeightedSpinCharacterSum L
              (fun edge => (weight edge : Complex)) 1 0 -
            triangularTorusWeightedSpinCharacterSum L
              (fun edge => (weight edge : Complex)) 0 0) := by rw [harf]
      _ = _ := by ring



theorem triangularTorusNormalizedSector_logDensity_tendsto
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        Real.log ‖triangularTorusNormalizedSectorSequence
          J1 J2 J3 rho a b n‖ / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  have hgrid := triangularIsingSymbol_riemann_tendsto_spinShift
    J1 J2 J3 a b hpos
  have hshift := hgrid.comp (Filter.tendsto_add_atTop_nat 3)
  have hscaled := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => (1 / (8 * Real.pi ^ 2) : Real))
      Filter.atTop (nhds (1 / (8 * Real.pi ^ 2)))).mul hshift
  apply hscaled.congr'
  filter_upwards [] with n
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  letI : NeZero L := ⟨by dsimp only [L]; omega⟩
  dsimp only [Function.comp_apply]
  simp only [triangularTorusNormalizedSectorSequence]
  rw [triangularTorus_normalizedSector_log_norm_eq
    (n + 3) J1 J2 J3 rho a b hrho hpos]
  have hsum := sum_zmod_prod_eq_sum_range (n + 3) (fun i j =>
    Real.log (triangularIsingSymbol J1 J2 J3
      (2 * Real.pi * (i + (a.val : Real) / 2) / (n + 3))
      (2 * Real.pi * (j + (b.val : Real) / 2) / (n + 3))))
  have hsum' :
      (∑ j : ZMod (n + 3) × ZMod (n + 3),
        Real.log (triangularIsingSymbol J1 J2 J3
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / (n + 3))
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / (n + 3)))) =
        ∑ i ∈ Finset.range (n + 3), ∑ j ∈ Finset.range (n + 3),
          Real.log (triangularIsingSymbol J1 J2 J3
            (2 * Real.pi * (i + (a.val : Real) / 2) / (n + 3))
            (2 * Real.pi * (j + (b.val : Real) / 2) / (n + 3))) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hsum
  simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [hsum']
  have hL : (L : Real) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring



theorem triangularTorusNormalizedSectorMax_logDensity_tendsto
    (J1 J2 J3 : Real) (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        Real.log (triangularTorusNormalizedSectorMaxSequence
          J1 J2 J3 rho n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  let limit : Real := (1 / (8 * Real.pi ^ 2)) *
    ∫ k1 in (-Real.pi)..Real.pi,
      ∫ k2 in (-Real.pi)..Real.pi,
        Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)
  have h11 := triangularTorusNormalizedSector_logDensity_tendsto
    J1 J2 J3 rho 1 1 hrho hpos
  have h01 := triangularTorusNormalizedSector_logDensity_tendsto
    J1 J2 J3 rho 0 1 hrho hpos
  have h10 := triangularTorusNormalizedSector_logDensity_tendsto
    J1 J2 J3 rho 1 0 hrho hpos
  have h00 := triangularTorusNormalizedSector_logDensity_tendsto
    J1 J2 J3 rho 0 0 hrho hpos
  have hmax := (h11.max h01).max (h10.max h00)
  have hmax' : Filter.Tendsto
      (fun n : Nat =>
        max
          (max
            (Real.log ‖triangularTorusNormalizedSectorSequence
                J1 J2 J3 rho 1 1 n‖ / (n + 3 : Real) ^ 2)
            (Real.log ‖triangularTorusNormalizedSectorSequence
                J1 J2 J3 rho 0 1 n‖ / (n + 3 : Real) ^ 2))
          (max
            (Real.log ‖triangularTorusNormalizedSectorSequence
                J1 J2 J3 rho 1 0 n‖ / (n + 3 : Real) ^ 2)
            (Real.log ‖triangularTorusNormalizedSectorSequence
                J1 J2 J3 rho 0 0 n‖ / (n + 3 : Real) ^ 2)))
      Filter.atTop (nhds limit) := by
    simpa only [max_self] using hmax
  apply hmax'.congr'
  filter_upwards [] with n
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  let sector : Fin 2 -> Fin 2 -> Complex := fun a b =>
    triangularTorusNormalizedSectorSequence J1 J2 J3 rho a b n
  have hsector (a b : Fin 2) : 0 < ‖sector a b‖ := by
    rw [norm_pos_iff]
    dsimp only [sector, triangularTorusNormalizedSectorSequence]
    exact triangularTorus_normalizedSector_ne_zero
      L J1 J2 J3 rho a b hrho hpos
  have hlogmax (x y : Real) (hx : 0 < x) (hy : 0 < y) :
      Real.log (max x y) = max (Real.log x) (Real.log y) :=
    Real.strictMonoOn_log.monotoneOn.map_max hx hy
  have hden : 0 ≤ (n + 3 : Real) ^ 2 := sq_nonneg _
  dsimp only [triangularTorusNormalizedSectorMaxSequence,
    arfSectorNormMax]
  rw [hlogmax _ _ (lt_of_lt_of_le (hsector 1 1) (le_max_left _ _))
      (lt_of_lt_of_le (hsector 1 0) (le_max_left _ _)),
    hlogmax _ _ (hsector 1 1) (hsector 0 1),
    hlogmax _ _ (hsector 1 0) (hsector 0 0),
    max_div_div_right hden, max_div_div_right hden,
    max_div_div_right hden]

theorem triangularTorusEdgeWeight_real_cast
    (L : Nat) (x y z : Real) :
    (fun edge => (triangularTorusRealEdgeWeight L x y z edge : Complex)) =
      triangularTorusEdgeWeight L x y z := by
  funext edge
  by_cases hx : squareTorusHorizontalEdge L edge
  · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight, hx]
  · by_cases hy : triangularTorusVerticalEdge L edge
    · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight,
        hx, hy]
    · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight,
        hx, hy]

theorem triangularTorusRealEdgeWeight_nonneg
    (L : Nat) {x y z : Real} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ∀ edge, 0 ≤ triangularTorusRealEdgeWeight L x y z edge := by
  intro edge
  unfold triangularTorusRealEdgeWeight
  split_ifs <;> assumption

theorem arfSectorNormMax_nonneg_real_mul
    (c : Real) (hc : 0 ≤ c)
    (sector : Fin 2 → Fin 2 → Complex) :
    arfSectorNormMax (fun a b => (c : Complex) * sector a b) =
      c * arfSectorNormMax sector := by
  simp only [arfSectorNormMax, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc]
  rw [mul_max_of_nonneg _ _ hc, mul_max_of_nonneg _ _ hc,
    mul_max_of_nonneg _ _ hc]


noncomputable def triangularTorusNormalizedEvenSequence
    (J1 J2 J3 : Real) (n : Nat) : Real := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  exact (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) *
    inhomogeneousEvenSubgraphSum (triangularTorusGraph L)
      (triangularTorusRealEdgeWeight L
        (Real.tanh J1) (Real.tanh J2) (Real.tanh J3))

theorem triangularTorusNormalizedSectorMaxSequence_eq
    (J1 J2 J3 : Real) (rho : Complex) (n : Nat) :
    triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n =
      (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^
          ((n + 3) * (n + 3)) *
        arfSectorNormMax (triangularTorusSectorSequence
          (fun L => triangularTorusRealEdgeWeight L
            (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) n) := by
  let C : Real := (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^
    ((n + 3) * (n + 3))
  letI : Fact (2 < n + 3) := ⟨by omega⟩
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  unfold triangularTorusNormalizedSectorMaxSequence
    triangularTorusNormalizedSectorSequence triangularTorusSectorSequence
  change arfSectorNormMax (fun a b => (C : Complex) *
      triangularTorusWeightedSpinCharacterSum (n + 3)
        (triangularTorusEdgeWeight (n + 3)
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b) = _
  rw [← triangularTorusEdgeWeight_real_cast]
  exact arfSectorNormMax_nonneg_real_mul C hC _



theorem triangularTorusNormalizedEven_log_gap_tendsto_zero
    (J1 J2 J3 : Real) (rho : Complex)
    (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2) (hJ3 : 0 ≤ J3) :
    Filter.Tendsto
      (fun n : Nat =>
        (Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
          Real.log (triangularTorusNormalizedSectorMaxSequence
            J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2)
      Filter.atTop (nhds 0) := by
  let weight : (L : Nat) → Sym2 (ZMod L × ZMod L) → Real :=
    fun L => triangularTorusRealEdgeWeight L
      (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)
  have htanh1 : 0 ≤ Real.tanh J1 := real_tanh_nonneg hJ1
  have htanh2 : 0 ≤ Real.tanh J2 := real_tanh_nonneg hJ2
  have htanh3 : 0 ≤ Real.tanh J3 := real_tanh_nonneg hJ3
  have hbase := triangularTorusEvenSubgraphSum_normalizedLog_gap_tendsto_zero
    weight (fun L => triangularTorusRealEdgeWeight_nonneg
      L htanh1 htanh2 htanh3)
  apply hbase.congr'
  filter_upwards [] with n
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  let C : Real := (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L)
  let E : Real := inhomogeneousEvenSubgraphSum (triangularTorusGraph L)
    (weight L)
  let M : Real := arfSectorNormMax (triangularTorusSectorSequence weight n)
  have hweight : ∀ edge, 0 ≤ weight L edge :=
    triangularTorusRealEdgeWeight_nonneg L htanh1 htanh2 htanh3
  have hE : 0 < E :=
    inhomogeneousEvenSubgraphSum_pos_of_nonneg
      (triangularTorusGraph L) (weight L) hweight
  have hM : 0 < M := by
    let sector : Fin 2 -> Fin 2 -> Complex :=
      triangularTorusSectorSequence weight n
    have hdom : forall a b, ‖sector a b‖ ≤ E := by
      intro a b
      dsimp only [sector, triangularTorusSectorSequence, E]
      exact triangularTorusWeightedSpin_norm_le_evenSubgraphSum
        L hweight a b
    have harf := two_mul_triangularTorusEvenSubgraphSum_eq_spin L (weight L)
    have harf' : ((2 * E : Real) : Complex) =
        sector 1 1 + sector 0 1 + sector 1 0 - sector 0 0 := by
      dsimp only [sector, E]
      simpa only [Nat.cast_ofNat, Complex.ofReal_mul] using harf
    have hbound := arfSectorNormMax_le_and_le_two_mul E sector hE hdom harf'
    dsimp only [M]
    nlinarith [hbound.2]
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hmax := triangularTorusNormalizedSectorMaxSequence_eq
    J1 J2 J3 rho n
  simp only [triangularTorusNormalizedEvenSequence,
    triangularTorusEvenSubgraphSequence]
  change (Real.log E - Real.log M) / (n + 3 : Real) ^ 2 =
    (Real.log (C * E) -
      Real.log (triangularTorusNormalizedSectorMaxSequence
        J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2
  rw [hmax]
  rw [Real.log_mul hC.ne' hE.ne', Real.log_mul hC.ne' hM.ne']
  ring



theorem triangularTorusNormalizedEven_logDensity_tendsto
    (J1 J2 J3 : Real) (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2) (hJ3 : 0 ≤ J3)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) /
          (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  have hgap := triangularTorusNormalizedEven_log_gap_tendsto_zero
    J1 J2 J3 rho hJ1 hJ2 hJ3
  have hmax := triangularTorusNormalizedSectorMax_logDensity_tendsto
    J1 J2 J3 rho hrho hpos
  have hadd := hgap.add hmax
  have hadd' : Filter.Tendsto
      (fun n : Nat =>
        (Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
            Real.log (triangularTorusNormalizedSectorMaxSequence
              J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2 +
          Real.log (triangularTorusNormalizedSectorMaxSequence
            J1 J2 J3 rho n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
    simpa only [zero_add] using hadd
  apply hadd'.congr'
  filter_upwards [] with n
  ring

theorem prod_triangularPositiveEdgeSources
    {A : Type*} [CommMonoid A]
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ⊆ (triangularTorusGraph L).edgeFinset)
    (f : Sym2 (ZMod L × ZMod L) → A) :
    (∏ edge ∈ F, f edge) =
      ∏ a : Fin 3, ∏ p ∈ triangularPositiveEdgeSources L F a,
        f (triangularPositiveEdge L a p) := by
  simpa only using
    (sum_triangularPositiveEdgeSources (A := Additive A) L F hF
      (fun edge => Additive.ofMul (f edge)))

theorem triangularPositiveEdgeSources_edgeFinset
    (L : Nat) [Fact (2 < L)] (a : Fin 3) :
    triangularPositiveEdgeSources L (triangularTorusGraph L).edgeFinset a =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro p
  rw [triangularPositiveEdgeSources, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [SimpleGraph.mem_edgeFinset]
  unfold triangularPositiveEdge
  exact (triangularTorusDartEquiv L
    (p, triangularTorusPositiveDirection a)).adj

theorem triangularTorusRealEdgeWeight_positiveEdge
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (a : Fin 3) (p : ZMod L × ZMod L) :
    triangularTorusRealEdgeWeight L J1 J2 J3
        (triangularPositiveEdge L a p) =
      ![J1, J2, J3] a := by
  apply Complex.ofReal_injective
  rw [triangularTorusRealEdgeWeight_cast]
  unfold triangularPositiveEdge
  rw [triangularTorusEdgeWeight_dart]
  fin_cases a <;>
    simp [triangularTorusPositiveDirection,
      triangularTorusDirectionWeight]

theorem prod_cosh_triangularTorusRealEdgeWeight
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    (∏ edge ∈ (triangularTorusGraph L).edgeFinset,
      Real.cosh (triangularTorusRealEdgeWeight L J1 J2 J3 edge)) =
      (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) := by
  rw [prod_triangularPositiveEdgeSources L
    (triangularTorusGraph L).edgeFinset (fun _ h => h) (fun edge =>
      Real.cosh (triangularTorusRealEdgeWeight L J1 J2 J3 edge))]
  simp_rw [triangularPositiveEdgeSources_edgeFinset,
    triangularTorusRealEdgeWeight_positiveEdge]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    ZMod.card]
  rw [show (∏ x : Fin 3, Real.cosh (![J1, J2, J3] x) ^ (L * L)) =
      Real.cosh J1 ^ (L * L) *
        (Real.cosh J2 ^ (L * L) * Real.cosh J3 ^ (L * L)) by
      simp]
  rw [mul_pow, mul_pow]
  ring

noncomputable def triangularTorusIsingPartitionSequence
    (J1 J2 J3 : Real) (n : Nat) : Real := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  exact StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
    (triangularTorusRealEdgeWeight L J1 J2 J3) (fun _ => 0)

theorem triangularTorusIsingPartitionSequence_eq
    (J1 J2 J3 : Real) (n : Nat) :
    triangularTorusIsingPartitionSequence J1 J2 J3 n =
      2 ^ ((n + 3) * (n + 3)) *
        triangularTorusNormalizedEvenSequence J1 J2 J3 n := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  rw [triangularTorusIsingPartitionSequence,
    triangularTorusIsingPartition_highTemperature]
  rw [prod_cosh_triangularTorusRealEdgeWeight]
  have hcard : Fintype.card (ZMod L × ZMod L) = L * L := by
    simp [Fintype.card_prod, ZMod.card]
  rw [hcard]
  simp only [triangularTorusNormalizedEvenSequence]
  have htanh :
      (fun edge => Real.tanh
        (triangularTorusRealEdgeWeight L J1 J2 J3 edge)) =
        triangularTorusRealEdgeWeight L
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) := by
    funext edge
    unfold triangularTorusRealEdgeWeight
    split_ifs <;> rfl
  rw [htanh]
  ring



theorem triangularTorusIsingPartition_freeEnergy_tendsto
    (J1 J2 J3 : Real) (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2) (hJ3 : 0 ≤ J3)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence J1 J2 J3 n) /
          (n + 3 : Real) ^ 2)
      Filter.atTop (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
  have heven := triangularTorusNormalizedEven_logDensity_tendsto
    J1 J2 J3 rho hrho hJ1 hJ2 hJ3 hpos
  have hlog2 : Filter.Tendsto
      (fun n : Nat =>
        Real.log (2 ^ ((n + 3) * (n + 3)) : Real) /
          (n + 3 : Real) ^ 2)
      Filter.atTop (nhds (Real.log 2)) := by
    have heq : ∀ n : Nat,
        Real.log (2 ^ ((n + 3) * (n + 3)) : Real) /
            (n + 3 : Real) ^ 2 = Real.log 2 := by
      intro n
      rw [Real.log_pow]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      field_simp
    exact (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => Real.log 2) Filter.atTop (nhds (Real.log 2))).congr'
        (Filter.Eventually.of_forall fun n => (heq n).symm)
  have hsum := hlog2.add heven
  have hneg := hsum.neg
  have hneg' : Filter.Tendsto
      (fun (x : Nat) =>
        -(Real.log (2 ^ ((x + 3) * (x + 3)) : Real) /
            (x + 3 : Real) ^ 2 +
          Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 x) /
            (x + 3 : Real) ^ 2))
      Filter.atTop (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
    convert hneg using 1 <;> unfold triangularIsingFreeEnergyValue <;> ring
  apply hneg'.congr'
  filter_upwards [] with n
  rw [triangularTorusIsingPartitionSequence_eq]
  have htwo : (2 ^ ((n + 3) * (n + 3)) : Real) ≠ 0 := by positivity
  have hevenPos : 0 < triangularTorusNormalizedEvenSequence
      J1 J2 J3 n := by
    let L := n + 3
    letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
    unfold triangularTorusNormalizedEvenSequence
    exact mul_pos (by positivity)
      (inhomogeneousEvenSubgraphSum_pos_of_nonneg
        (triangularTorusGraph L)
        (triangularTorusRealEdgeWeight L
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) (by
            intro edge
            unfold triangularTorusRealEdgeWeight
            split_ifs <;> exact real_tanh_nonneg (by assumption)))
  rw [Real.log_mul htwo hevenPos.ne']
  ring

end StatMech.FrontierA
