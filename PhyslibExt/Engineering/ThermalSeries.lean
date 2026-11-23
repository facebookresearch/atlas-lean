/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.BigOperators.SumRangeDrop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Thermal resistance of layers and films in series

## i. Overview

For `n` planar layers and two surface films in series at common
area `A`, with interface temperatures satisfying the supplied
common-heat-rate drop laws (film drops `Q / (h * A)`, layer
drops `Q * (L i / (k i * A))`), the heat rate is recovered as
the total temperature difference divided by the total series
resistance, equivalently `Q = A * U * ΔT` for the overall
coefficient `U = 1 / (A * R)`. The films-only case `n = 0` is
included.

## ii. Key results

- `thermalSeriesResistance_pos`: positivity of the total
  resistance.
- `thermalSeriesHeatRate_of_drops`: heat-rate recovery from the
  interface drop laws.
- `thermalSeriesHeatRate_eq_area_mul_U`: the overall-coefficient
  form.

## iii. Table of contents

- A. Series resistance and heat rate

## iv. References

- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine,
  *Fundamentals of Heat and Mass Transfer*, 6th edition, Wiley,
  2007, Section 3.1 (composite plane wall, overall heat transfer
  coefficient).
-/

@[expose] public section

/-! ## A. Series resistance and heat rate -/

/-- Total resistance of `n` planar layers and two films in
series at common area `A`: inside film `1 / (hin * A)`, layer
resistances `L i / (k i * A)`, and outside film
`1 / (hout * A)`. -/
noncomputable def thermalSeriesResistance {n : ℕ} (A hin hout : ℝ)
    (L k : ℕ → ℝ) : ℝ :=
  1 / (hin * A) + (∑ i ∈ Finset.range n, L i / (k i * A))
    + 1 / (hout * A)

/-- Overall heat-transfer coefficient `U = 1 / (A * R)` for the
series resistance. -/
noncomputable def thermalOverallCoefficient {n : ℕ}
    (A hin hout : ℝ) (L k : ℕ → ℝ) : ℝ :=
  1 / (A * thermalSeriesResistance (n := n) A hin hout L k)

/-- The series resistance is positive for positive area, film
coefficients, thicknesses, and conductivities. -/
theorem thermalSeriesResistance_pos {n : ℕ} {A hin hout : ℝ}
    {L k : ℕ → ℝ} (hA : 0 < A) (hhin : 0 < hin)
    (hhout : 0 < hout) (hL : ∀ i < n, 0 < L i)
    (hk : ∀ i < n, 0 < k i) :
    0 < thermalSeriesResistance (n := n) A hin hout L k := by
  unfold thermalSeriesResistance
  have h1 : 0 < 1 / (hin * A) := by positivity
  have h3 : 0 < 1 / (hout * A) := by positivity
  have h2 : 0 ≤ ∑ i ∈ Finset.range n, L i / (k i * A) := by
    apply Finset.sum_nonneg
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hLi := hL i hi'
    have hki := hk i hi'
    positivity
  linarith

/-- Series heat-rate recovery from interface drop laws. Let
`Temp 0` be the inside air temperature, `Temp 1, ..., Temp (n+1)`
the successive interface temperatures after the inside film and
each layer, and `Temp (n+2)` the outside air temperature. If a
common steady heat rate `Q` produces the film and layer drops
`Q * (1 / (h * A))` and `Q * (L i / (k i * A))`, then `Q` is the
total temperature difference divided by the total series
resistance. -/
theorem thermalSeriesHeatRate_of_drops {n : ℕ} {A hin hout Q : ℝ}
    {L k Temp : ℕ → ℝ} (hA : 0 < A) (hhin : 0 < hin)
    (hhout : 0 < hout) (hL : ∀ i < n, 0 < L i)
    (hk : ∀ i < n, 0 < k i)
    (hfilm_in : Temp 0 - Temp 1 = Q * (1 / (hin * A)))
    (hlayer : ∀ i < n, Temp (i + 1) - Temp (i + 2)
      = Q * (L i / (k i * A)))
    (hfilm_out : Temp (n + 1) - Temp (n + 2)
      = Q * (1 / (hout * A))) :
    Q = (Temp 0 - Temp (n + 2))
      / thermalSeriesResistance (n := n) A hin hout L k := by
  have hmid : Temp 1 - Temp (n + 1)
      = Q * ∑ i ∈ Finset.range n, L i / (k i * A) := by
    have h := MathlibExt.sub_eq_mul_sum_range
      (R := fun i => L i / (k i * A)) (P := fun j => Temp (j + 1))
      (q := Q) (n := n) (fun i hi => by
        show Temp (i + 1) - Temp (i + 1 + 1) = Q * (L i / (k i * A))
        rw [show i + 1 + 1 = i + 2 from by omega]
        exact hlayer i hi)
    simpa using h
  have htot : Temp 0 - Temp (n + 2)
      = Q * thermalSeriesResistance (n := n) A hin hout L k := by
    unfold thermalSeriesResistance
    have htele : Temp 0 - Temp (n + 2)
        = (Temp 0 - Temp 1) + (Temp 1 - Temp (n + 1))
          + (Temp (n + 1) - Temp (n + 2)) := by linarith
    rw [htele, hfilm_in, hmid, hfilm_out]
    simp only [mul_add]
  have hRne : thermalSeriesResistance (n := n) A hin hout L k ≠ 0 :=
    ne_of_gt (thermalSeriesResistance_pos hA hhin hhout hL hk)
  rw [eq_div_iff hRne]
  exact htot.symm

/-- In overall-coefficient form, the recovered heat rate is
`Q = A * U * (Temp 0 - Temp (n + 2))`. -/
theorem thermalSeriesHeatRate_eq_area_mul_U {n : ℕ}
    {A hin hout Q : ℝ} {L k Temp : ℕ → ℝ} (hA : 0 < A)
    (hhin : 0 < hin) (hhout : 0 < hout)
    (hL : ∀ i < n, 0 < L i) (hk : ∀ i < n, 0 < k i)
    (hfilm_in : Temp 0 - Temp 1 = Q * (1 / (hin * A)))
    (hlayer : ∀ i < n, Temp (i + 1) - Temp (i + 2)
      = Q * (L i / (k i * A)))
    (hfilm_out : Temp (n + 1) - Temp (n + 2)
      = Q * (1 / (hout * A))) :
    Q = A * thermalOverallCoefficient (n := n) A hin hout L k
      * (Temp 0 - Temp (n + 2)) := by
  have hQ := thermalSeriesHeatRate_of_drops hA hhin hhout hL hk
    hfilm_in hlayer hfilm_out
  have hRne : thermalSeriesResistance (n := n) A hin hout L k ≠ 0 :=
    ne_of_gt (thermalSeriesResistance_pos hA hhin hhout hL hk)
  have hAne : A ≠ 0 := ne_of_gt hA
  unfold thermalOverallCoefficient
  rw [hQ]
  field_simp
