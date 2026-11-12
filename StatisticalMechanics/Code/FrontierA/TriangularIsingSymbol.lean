/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.RiemannPeriodic2D










open scoped BigOperators
open MeasureTheory

namespace StatMech.FrontierA



noncomputable def triangularIsingSymbol
    (J1 J2 J3 k1 k2 : ℝ) : ℝ :=
  Real.cosh (2 * J1) * Real.cosh (2 * J2) * Real.cosh (2 * J3) +
    Real.sinh (2 * J1) * Real.sinh (2 * J2) * Real.sinh (2 * J3) -
    (Real.sinh (2 * J1) * Real.cos k1 +
      Real.sinh (2 * J2) * Real.cos k2 +
      Real.sinh (2 * J3) * Real.cos (k1 + k2))



noncomputable def triangularIsingHighTempSymbol
    (J1 J2 J3 k1 k2 : ℝ) : ℝ :=
  (1 + Real.tanh J1 ^ 2) * (1 + Real.tanh J2 ^ 2) *
      (1 + Real.tanh J3 ^ 2) +
    8 * Real.tanh J1 * Real.tanh J2 * Real.tanh J3 -
    2 * (Real.tanh J1 * (1 - Real.tanh J2 ^ 2) *
          (1 - Real.tanh J3 ^ 2) * Real.cos k1 +
      Real.tanh J2 * (1 - Real.tanh J1 ^ 2) *
          (1 - Real.tanh J3 ^ 2) * Real.cos k2 +
      Real.tanh J3 * (1 - Real.tanh J1 ^ 2) *
          (1 - Real.tanh J2 ^ 2) * Real.cos (k1 + k2))

private theorem one_add_tanh_sq_mul_cosh_sq (x : ℝ) :
    (1 + Real.tanh x ^ 2) * Real.cosh x ^ 2 = Real.cosh (2 * x) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.cosh_two_mul]
  field_simp [(Real.cosh_pos x).ne']

private theorem one_sub_tanh_sq_mul_cosh_sq (x : ℝ) :
    (1 - Real.tanh x ^ 2) * Real.cosh x ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos x).ne']
  exact Real.cosh_sq_sub_sinh_sq x

private theorem two_tanh_mul_cosh_sq (x : ℝ) :
    2 * Real.tanh x * Real.cosh x ^ 2 = Real.sinh (2 * x) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul]
  field_simp [(Real.cosh_pos x).ne']



theorem triangularIsingHighTempSymbol_mul_cosh_sq
    (J1 J2 J3 k1 k2 : ℝ) :
    triangularIsingHighTempSymbol J1 J2 J3 k1 k2 *
        (Real.cosh J1 ^ 2 * Real.cosh J2 ^ 2 * Real.cosh J3 ^ 2) =
      triangularIsingSymbol J1 J2 J3 k1 k2 := by
  rw [triangularIsingHighTempSymbol, triangularIsingSymbol]
  have hplus1 := one_add_tanh_sq_mul_cosh_sq J1
  have hplus2 := one_add_tanh_sq_mul_cosh_sq J2
  have hplus3 := one_add_tanh_sq_mul_cosh_sq J3
  have hminus1 := one_sub_tanh_sq_mul_cosh_sq J1
  have hminus2 := one_sub_tanh_sq_mul_cosh_sq J2
  have hminus3 := one_sub_tanh_sq_mul_cosh_sq J3
  have htanh1 := two_tanh_mul_cosh_sq J1
  have htanh2 := two_tanh_mul_cosh_sq J2
  have htanh3 := two_tanh_mul_cosh_sq J3
  calc
    ((1 + Real.tanh J1 ^ 2) * (1 + Real.tanh J2 ^ 2) *
          (1 + Real.tanh J3 ^ 2) +
        8 * Real.tanh J1 * Real.tanh J2 * Real.tanh J3 -
        2 * (Real.tanh J1 * (1 - Real.tanh J2 ^ 2) *
              (1 - Real.tanh J3 ^ 2) * Real.cos k1 +
          Real.tanh J2 * (1 - Real.tanh J1 ^ 2) *
              (1 - Real.tanh J3 ^ 2) * Real.cos k2 +
          Real.tanh J3 * (1 - Real.tanh J1 ^ 2) *
              (1 - Real.tanh J2 ^ 2) * Real.cos (k1 + k2))) *
          (Real.cosh J1 ^ 2 * Real.cosh J2 ^ 2 * Real.cosh J3 ^ 2) =
        ((1 + Real.tanh J1 ^ 2) * Real.cosh J1 ^ 2) *
          ((1 + Real.tanh J2 ^ 2) * Real.cosh J2 ^ 2) *
          ((1 + Real.tanh J3 ^ 2) * Real.cosh J3 ^ 2) +
        (2 * Real.tanh J1 * Real.cosh J1 ^ 2) *
          (2 * Real.tanh J2 * Real.cosh J2 ^ 2) *
          (2 * Real.tanh J3 * Real.cosh J3 ^ 2) -
        ((2 * Real.tanh J1 * Real.cosh J1 ^ 2) *
            ((1 - Real.tanh J2 ^ 2) * Real.cosh J2 ^ 2) *
            ((1 - Real.tanh J3 ^ 2) * Real.cosh J3 ^ 2) * Real.cos k1 +
          (2 * Real.tanh J2 * Real.cosh J2 ^ 2) *
            ((1 - Real.tanh J1 ^ 2) * Real.cosh J1 ^ 2) *
            ((1 - Real.tanh J3 ^ 2) * Real.cosh J3 ^ 2) * Real.cos k2 +
          (2 * Real.tanh J3 * Real.cosh J3 ^ 2) *
            ((1 - Real.tanh J1 ^ 2) * Real.cosh J1 ^ 2) *
            ((1 - Real.tanh J2 ^ 2) * Real.cosh J2 ^ 2) *
              Real.cos (k1 + k2)) := by ring
    _ = _ := by
      rw [hplus1, hplus2, hplus3, hminus1, hminus2,
        hminus3, htanh1, htanh2, htanh3]
      ring


noncomputable def triangularIsingFreeEnergyValue (J1 J2 J3 : ℝ) : ℝ :=
  -Real.log 2 - (1 / (8 * Real.pi ^ 2)) *
    ∫ k1 in (-Real.pi)..Real.pi,
      ∫ k2 in (-Real.pi)..Real.pi,
        Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)

theorem continuous_triangularIsingSymbol (J1 J2 J3 : ℝ) :
    Continuous fun p : ℝ × ℝ =>
      triangularIsingSymbol J1 J2 J3 p.1 p.2 := by
  unfold triangularIsingSymbol
  fun_prop

theorem periodic_triangularIsingSymbol_left (J1 J2 J3 k2 : ℝ) :
    Function.Periodic
      (fun k1 => triangularIsingSymbol J1 J2 J3 k1 k2)
      (2 * Real.pi) := by
  intro k1
  change triangularIsingSymbol J1 J2 J3 (k1 + 2 * Real.pi) k2 =
    triangularIsingSymbol J1 J2 J3 k1 k2
  unfold triangularIsingSymbol
  rw [Real.cos_add_two_pi]
  have hsum : k1 + 2 * Real.pi + k2 = (k1 + k2) + 2 * Real.pi := by ring
  rw [hsum, Real.cos_add_two_pi]

theorem periodic_triangularIsingSymbol_right (J1 J2 J3 k1 : ℝ) :
    Function.Periodic
      (fun k2 => triangularIsingSymbol J1 J2 J3 k1 k2)
      (2 * Real.pi) := by
  intro k2
  change triangularIsingSymbol J1 J2 J3 k1 (k2 + 2 * Real.pi) =
    triangularIsingSymbol J1 J2 J3 k1 k2
  unfold triangularIsingSymbol
  rw [Real.cos_add_two_pi]
  have hsum : k1 + (k2 + 2 * Real.pi) = (k1 + k2) + 2 * Real.pi := by ring
  rw [hsum, Real.cos_add_two_pi]

theorem continuous_log_triangularIsingSymbol_of_pos
    (J1 J2 J3 : ℝ)
    (hpos : ∀ k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Continuous fun p : ℝ × ℝ =>
      Real.log (triangularIsingSymbol J1 J2 J3 p.1 p.2) := by
  apply Continuous.log (continuous_triangularIsingSymbol J1 J2 J3)
  intro p
  exact (hpos p.1 p.2).ne'

theorem periodic_log_triangularIsingSymbol_left
    (J1 J2 J3 k2 : ℝ) :
    Function.Periodic
      (fun k1 => Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))
      (2 * Real.pi) := by
  intro k1
  exact congrArg Real.log
    (periodic_triangularIsingSymbol_left J1 J2 J3 k2 k1)

theorem periodic_log_triangularIsingSymbol_right
    (J1 J2 J3 k1 : ℝ) :
    Function.Periodic
      (fun k2 => Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))
      (2 * Real.pi) := by
  intro k2
  exact congrArg Real.log
    (periodic_triangularIsingSymbol_right J1 J2 J3 k1 k2)

theorem integral_log_triangularIsingSymbol_right_shift
    (J1 J2 J3 k1 : ℝ) :
    (∫ k2 in (0 : ℝ)..(2 * Real.pi),
        Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)) =
      ∫ k2 in (-Real.pi)..Real.pi,
        Real.log (triangularIsingSymbol J1 J2 J3 k1 k2) := by
  have hshift :=
    (periodic_log_triangularIsingSymbol_right J1 J2 J3 k1).intervalIntegral_add_eq
      0 (-Real.pi)
  convert hshift using 1 <;> ring

theorem integral_log_triangularIsingSymbol_square_shift
    (J1 J2 J3 : ℝ) :
    (∫ k1 in (0 : ℝ)..(2 * Real.pi),
      ∫ k2 in (0 : ℝ)..(2 * Real.pi),
        Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)) =
      ∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Real.log (triangularIsingSymbol J1 J2 J3 k1 k2) := by
  let g : ℝ → ℝ := fun k1 =>
    ∫ k2 in (-Real.pi)..Real.pi,
      Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)
  have hgper : Function.Periodic g (2 * Real.pi) := by
    intro k1
    apply intervalIntegral.integral_congr
    intro k2 _
    exact congrArg Real.log
      (periodic_triangularIsingSymbol_left J1 J2 J3 k2 k1)
  calc
    (∫ k1 in (0 : ℝ)..(2 * Real.pi),
      ∫ k2 in (0 : ℝ)..(2 * Real.pi),
        Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)) =
        ∫ k1 in (0 : ℝ)..(2 * Real.pi), g k1 := by
      apply intervalIntegral.integral_congr
      intro k1 _
      exact integral_log_triangularIsingSymbol_right_shift J1 J2 J3 k1
    _ = ∫ k1 in (-Real.pi)..Real.pi, g k1 := by
      have hshift := hgper.intervalIntegral_add_eq 0 (-Real.pi)
      convert hshift using 1 <;> ring
    _ = _ := rfl



theorem triangularIsingSymbol_riemann_tendsto_of_pos
    (J1 J2 J3 : ℝ)
    (hpos : ∀ k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun L : ℕ => (2 * Real.pi / L) ^ 2 *
        ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          Real.log (triangularIsingSymbol J1 J2 J3
            (2 * Real.pi * i / L) (2 * Real.pi * j / L)))
      Filter.atTop
      (nhds (∫ k1 in (0 : ℝ)..(2 * Real.pi),
        ∫ k2 in (0 : ℝ)..(2 * Real.pi),
          Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  exact StatMech.Onsager.ons_riemann_periodic_two
    (fun k1 k2 => Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))
    (continuous_log_triangularIsingSymbol_of_pos J1 J2 J3 hpos)
    (periodic_log_triangularIsingSymbol_left J1 J2 J3)



theorem triangularIsingSymbol_riemann_tendsto_symmetric_of_pos
    (J1 J2 J3 : ℝ)
    (hpos : ∀ k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun L : ℕ => (2 * Real.pi / L) ^ 2 *
        ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          Real.log (triangularIsingSymbol J1 J2 J3
            (2 * Real.pi * i / L) (2 * Real.pi * j / L)))
      Filter.atTop
      (nhds (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  rw [← integral_log_triangularIsingSymbol_square_shift]
  exact triangularIsingSymbol_riemann_tendsto_of_pos J1 J2 J3 hpos

end StatMech.FrontierA
