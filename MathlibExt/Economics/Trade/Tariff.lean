/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Small-country tariff with linear schedules (Atlas AP01.T02)

A small open economy takes the world price `Pw` as given. Domestic demand and
supply are linear, `D P = a - b P` and `S P = c + d P` with `b, d > 0`. A specific
tariff `t ≥ 0` raises the domestic price to `Pw + t`. Imports are excess demand,
truncated at zero.

In the interior (non-prohibitive) regime `S (Pw + t) ≤ D (Pw + t)`:

* production rises by `d t` (production distortion);
* consumption falls by `b t` (consumption distortion);
* imports fall by `(b + d) t`;
* the change in consumer surplus plus producer surplus plus tariff revenue is
  `-(d t² / 2 + b t² / 2)`: the production and consumption deadweight triangles.

Surplus changes are the areas `∫_{Pw}^{Pw+t} D` and `∫_{Pw}^{Pw+t} S` to the left
of the schedules.
-/

@[expose] public section

namespace MathlibExt.Economics.Tariff

/-- Linear domestic demand `D P = a - b P` and supply `S P = c + d P`. -/
structure LinearMarket where
  /-- Demand intercept. -/
  a : ℝ
  /-- Demand slope (magnitude). -/
  b : ℝ
  /-- Supply intercept. -/
  c : ℝ
  /-- Supply slope. -/
  d : ℝ
  b_pos : 0 < b
  d_pos : 0 < d

/-- Domestic demand at price `P`. -/
def demand (m : LinearMarket) (P : ℝ) : ℝ := m.a - m.b * P

/-- Domestic supply at price `P`. -/
def supply (m : LinearMarket) (P : ℝ) : ℝ := m.c + m.d * P

/-- Imports at domestic price `P`: excess demand, truncated at zero. -/
noncomputable def imports (m : LinearMarket) (P : ℝ) : ℝ := max (demand m P - supply m P) 0

/-- Change in consumer surplus when the domestic price rises from `Pw` to `Pw + t`. -/
noncomputable def consumerSurplusChange (m : LinearMarket) (Pw t : ℝ) : ℝ :=
  -∫ P in Pw..(Pw + t), demand m P

/-- Change in producer surplus when the domestic price rises from `Pw` to `Pw + t`. -/
noncomputable def producerSurplusChange (m : LinearMarket) (Pw t : ℝ) : ℝ :=
  ∫ P in Pw..(Pw + t), supply m P

/-- Tariff revenue: the tariff times imports at the tariff-inclusive price. -/
noncomputable def tariffRevenue (m : LinearMarket) (Pw t : ℝ) : ℝ := t * imports m (Pw + t)

/-- Production distortion: domestic output rises by `d t`. -/
theorem supply_tariff_sub (m : LinearMarket) (Pw t : ℝ) :
    supply m (Pw + t) - supply m Pw = m.d * t := by
  simp only [supply]
  ring

/-- Consumption distortion: domestic consumption falls by `b t`. -/
theorem demand_sub_tariff (m : LinearMarket) (Pw t : ℝ) :
    demand m Pw - demand m (Pw + t) = m.b * t := by
  simp only [demand]
  ring

/-- In the non-prohibitive regime, imports fall by `(b + d) t`. -/
theorem imports_sub_tariff (m : LinearMarket) {Pw t : ℝ} (ht : 0 ≤ t)
    (hint : supply m (Pw + t) ≤ demand m (Pw + t)) :
    imports m Pw - imports m (Pw + t) = (m.b + m.d) * t := by
  have h2 : (0 : ℝ) ≤ demand m (Pw + t) - supply m (Pw + t) := sub_nonneg.mpr hint
  have hdecomp : demand m Pw - supply m Pw
      = (demand m (Pw + t) - supply m (Pw + t)) + (m.b + m.d) * t := by
    simp only [demand, supply]
    ring
  have h1 : (0 : ℝ) ≤ demand m Pw - supply m Pw := by
    rw [hdecomp]
    exact add_nonneg h2 (mul_nonneg (le_of_lt (add_pos m.b_pos m.d_pos)) ht)
  simp only [imports, max_eq_left h1, max_eq_left h2]
  linear_combination hdecomp

/-- Integral of demand over a price interval. -/
theorem integral_demand (m : LinearMarket) (u v : ℝ) :
    ∫ P in u..v, demand m P = m.a * (v - u) - m.b * ((v ^ 2 - u ^ 2) / 2) := by
  have hconst : IntervalIntegrable (fun _ : ℝ => m.a) MeasureTheory.volume u v :=
    intervalIntegrable_const
  have hlin : IntervalIntegrable (fun P : ℝ => m.b * P) MeasureTheory.volume u v :=
    intervalIntegral.intervalIntegrable_id.const_mul m.b
  have hsub : ∫ P in u..v, demand m P
      = (∫ P in u..v, m.a) - ∫ P in u..v, m.b * P := by
    have h := intervalIntegral.integral_sub hconst hlin
    simpa only [demand] using h
  rw [hsub, intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
    smul_eq_mul]
  ring

/-- Integral of supply over a price interval. -/
theorem integral_supply (m : LinearMarket) (u v : ℝ) :
    ∫ P in u..v, supply m P = m.c * (v - u) + m.d * ((v ^ 2 - u ^ 2) / 2) := by
  have hconst : IntervalIntegrable (fun _ : ℝ => m.c) MeasureTheory.volume u v :=
    intervalIntegrable_const
  have hlin : IntervalIntegrable (fun P : ℝ => m.d * P) MeasureTheory.volume u v :=
    intervalIntegral.intervalIntegrable_id.const_mul m.d
  have hadd : ∫ P in u..v, supply m P
      = (∫ P in u..v, m.c) + ∫ P in u..v, m.d * P := by
    have h := intervalIntegral.integral_add hconst hlin
    simpa only [supply] using h
  rw [hadd, intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
    smul_eq_mul]
  ring

/-- **Tariff welfare loss.** In the non-prohibitive regime, the change in total
surplus (consumer surplus + producer surplus + tariff revenue) is minus the sum of
the production and consumption deadweight triangles. -/
theorem welfare_change_tariff (m : LinearMarket) {Pw t : ℝ} (ht : 0 ≤ t)
    (hint : supply m (Pw + t) ≤ demand m (Pw + t)) :
    consumerSurplusChange m Pw t + producerSurplusChange m Pw t + tariffRevenue m Pw t =
      -(m.d * t ^ 2 / 2 + m.b * t ^ 2 / 2) := by
  have h2 : (0 : ℝ) ≤ demand m (Pw + t) - supply m (Pw + t) := sub_nonneg.mpr hint
  have hD := integral_demand m Pw (Pw + t)
  have hS := integral_supply m Pw (Pw + t)
  simp only [consumerSurplusChange, producerSurplusChange, tariffRevenue, imports,
    max_eq_left h2]
  rw [hD, hS]
  simp only [demand, supply]
  ring

end MathlibExt.Economics.Tariff
