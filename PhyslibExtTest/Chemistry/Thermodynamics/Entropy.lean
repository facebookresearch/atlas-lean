/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Thermodynamics.Entropy

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!

# Tests for entropy, heat engines and the third law

-/

@[expose] public section

open Chemistry.Thermodynamics

namespace PhyslibExtTest.Chemistry.Thermodynamics

/-!

## A. Carnot efficiency and the second-law bound

-/

/-- `Th = 600`, `Tc = 300`: the Carnot efficiency is `1 / 2`. -/
example : carnotEfficiency 300 600 = 1 / 2 := by
  unfold carnotEfficiency
  norm_num

/-- A reversible cycle with `V₂ / V₁ = V₃ / V₄` and `n = 1` has heat ratio `300 / 600`. -/
example (R V1 V2 V3 V4 : ℝ) (hR : 0 < R)
    (hV1 : 0 < V1) (hV4 : 0 < V4) (hexp : V1 < V2) (hcomp : V4 < V3)
    (hV : V2 / V1 = V3 / V4) :
    (1 * R * 300 * Real.log (V3 / V4)) / (1 * R * 600 * Real.log (V2 / V1))
      = 300 / 600 := by
  have hT1 : (0:ℝ) < 300 := by norm_num
  have hT2 : (300:ℝ) < 600 := by norm_num
  exact (carnot_heat_ratio hT1 hT2 one_pos hR hV1 hV4 hexp hcomp hV rfl rfl).2.2

/-- With `V₂ / V₁ = 2` the hot heat is `R * 600 * log 2` for `n = 1`. -/
example (R : ℝ) (V1 V2 : ℝ) (hratio : V2 / V1 = 2) :
    1 * R * 600 * Real.log (V2 / V1) = R * 600 * Real.log 2 := by
  rw [hratio]
  ring

/-- With `V₃ / V₄ = 2` the cold heat is `R * 300 * log 2` for `n = 1`. -/
example (R : ℝ) (V3 V4 : ℝ) (hratio : V3 / V4 = 2) :
    1 * R * 300 * Real.log (V3 / V4) = R * 300 * Real.log 2 := by
  rw [hratio]
  ring

/-- The reversible-cycle efficiency at `Th = 600`, `Tc = 300` is `1 / 2`. -/
example (R : ℝ) (hR : 0 < R) :
    1 - (1 * R * 300 * Real.log 2) / (1 * R * 600 * Real.log 2) = 1 / 2 := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hR0 : R ≠ 0 := hR.ne'
  field_simp
  ring

/-- A consistent engine set satisfies the Clausius inequality: `1000 / 600 - 550 / 300`,
equal to `-1 / 6`, is nonpositive. -/
example : (1000 / 600 - 550 / 300 : ℝ) = -1 / 6 := by norm_num

example : (1000 / 600 - 550 / 300 : ℝ) ≤ 0 := by norm_num

/-- The consistent set `Qh = 1000`, `Qc = 550`, `W = 450` obeys the second-law bound. -/
example : (450 / 1000 : ℝ) ≤ carnotEfficiency 300 600 := by
  have h := engine_efficiency_le_carnotEfficiency (Qh := 1000) (Qc := 550) (W := 450)
    (Tc := 300) (Th := 600)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h

/-- Its efficiency `0.45` is below `1 / 2`. -/
example : (450 / 1000 : ℝ) ≤ 1 / 2 := by norm_num

/-- A reversible engine attains the bound: `Qh = 1000`, `Qc = 500`, `W = 500`. -/
example : (500 / 1000 : ℝ) = carnotEfficiency 300 600 := by
  have h := engine_efficiency_eq_carnotEfficiency (Qh := 1000) (Qc := 500) (W := 500)
    (Tc := 300) (Th := 600)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h

/-- Countermodel: `Qh = 1000`, `Qc = 100`, `W = 900` violates Clausius
(`1000 / 600 - 100 / 300 = 4 / 3 > 0`), so the bound correctly excludes its `0.9`
efficiency. -/
example : (1000 / 600 - 100 / 300 : ℝ) = 4 / 3 := by norm_num

example : ¬ ((1000 / 600 - 100 / 300 : ℝ) ≤ 0) := by norm_num

/-- Its efficiency `900 / 1000` exceeds the Carnot bound, as the violated Clausius inequality
allows. -/
example : ¬ ((900 / 1000 : ℝ) ≤ carnotEfficiency 300 600) := by
  unfold carnotEfficiency
  norm_num

/-!

## B. Ideal-gas entropy changes

-/

/-- `n = 1`, `cv = 3 / 2 * R`, isochoric doubling `300 → 600`: `ΔS = 3 / 2 * R * log 2`. -/
example (R V : ℝ) (hV : 0 < V) :
    idealGasEntropyChange 1 (3 / 2 * R) R 300 V 600 V
      = (3 / 2) * R * Real.log 2 := by
  unfold idealGasEntropyChange
  have h1 : (600 / 300 : ℝ) = 2 := by norm_num
  rw [h1, div_self hV.ne', Real.log_one]
  ring

/-- The `totalCV` form: with `n = 2` and `CV = 2 * cv` there is no double counting. -/
example (cv R : ℝ) :
    idealGasEntropyChange 2 cv R 300 1 600 1
      = (2 * cv) * Real.log (600 / 300) + 2 * R * Real.log (1 / 1) :=
  idealGasEntropyChange_totalCV rfl

/-- The double-counted value differs from the correct one for the doubling case. -/
example (cv R V : ℝ) (hcv : 0 < cv) (hV : 0 < V) :
    (2 * cv) * Real.log (600 / 300) + 2 * R * Real.log (V / V)
      ≠ 2 * (2 * cv) * Real.log (600 / 300) + 2 * R * Real.log (V / V) := by
  have h1 : (600 / 300 : ℝ) = 2 := by norm_num
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hCV : 0 < 2 * cv := by linarith
  rw [h1, div_self hV.ne', Real.log_one]
  intro hcon
  have hA : (2 * cv) * Real.log 2 = 0 := by linarith
  have hpos : 0 < (2 * cv) * Real.log 2 := mul_pos hCV hL
  linarith

/-- Isothermal case: with `T₂ = T₁` only the volume term survives. -/
example (R V1 V2 : ℝ) :
    idealGasEntropyChange 1 2 R 300 V1 300 V2 = 1 * R * Real.log (V2 / V1) :=
  idealGasEntropyChange_isothermal (by norm_num) rfl

/-- Sign reversal at `300 → 600` against `600 → 300`. -/
example (R cv V : ℝ) (hV : 0 < V) :
    idealGasEntropyChange 1 cv R 300 V 600 V
      = -idealGasEntropyChange 1 cv R 600 V 300 V :=
  idealGasEntropyChange_symm (by norm_num) (by norm_num) hV hV

/-!

## C. Entropy of mixing

-/

/-- 50/50 binary mixing with `n = 1` unfolds to `-1 * R * (1 / 2 * log (1 / 2) + …)`. -/
example (R : ℝ) :
    entropyOfMixing 1 R (![1/2, 1 - 1/2] : Fin 2 → ℝ)
      = -1 * R * ((1/2) * Real.log (1/2) + (1 - 1/2) * Real.log (1 - 1/2)) :=
  entropyOfMixing_binary 1 R (1/2)

/-- …which simplifies to `R * log 2`. -/
example (R : ℝ) :
    entropyOfMixing 1 R (![1/2, 1 - 1/2] : Fin 2 → ℝ) = R * Real.log 2 := by
  rw [entropyOfMixing_binary]
  have h12 : (1 - 1/2 : ℝ) = 1/2 := by norm_num
  rw [h12]
  have hlog : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

/-- The 50/50 mixture has nonnegative mixing entropy for `0 ≤ R`. -/
example (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ entropyOfMixing 1 R (![1/2, 1 - 1/2] : Fin 2 → ℝ) := by
  have hx : ∀ i, 0 ≤ (![1/2, 1-1/2] : Fin 2 → ℝ) i := by
    rw [Fin.forall_fin_two]
    constructor
    · rw [Matrix.cons_val_zero]
      norm_num
    · rw [Matrix.cons_val_one, Matrix.cons_val_zero]
      norm_num
  have hsum : ∑ i, (![1/2, 1-1/2] : Fin 2 → ℝ) i = 1 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  exact entropyOfMixing_nonneg (by norm_num) hR hx hsum

/-- Single component `x = ![1, 0]`: the mixing entropy is `0`. -/
example (R : ℝ) : entropyOfMixing 1 R (![1, 0] : Fin 2 → ℝ) = 0 := by
  rw [entropyOfMixing_eq_neg_sum, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.log_one, mul_zero, zero_mul,
    add_zero]

/-- Three components `x = ![1 / 2, 1 / 2, 0]`: the zero component contributes `0` and the
mixing entropy is `R * log 2`. -/
example (R : ℝ) :
    entropyOfMixing 1 R (![1/2, 1/2, 0] : Fin 3 → ℝ) = R * Real.log 2 := by
  rw [entropyOfMixing_eq_neg_sum, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, zero_mul, add_zero]
  have hlog : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

/-!

## D. Absolute entropy and the third law

-/

/-- Debye-like `Cp t = a * t ^ 3` with no transitions: `S(T) = a * T ^ 3 / 3` (physical
reading at `a > 0`, `T ≥ 0`; the equation holds unconditionally). -/
example (a T : ℝ) :
    absoluteEntropy (fun t => a * t ^ 3) (∅ : Finset (Fin 1)) (fun _ => 1) (fun _ => 0) T
      = a * T ^ 3 / 3 := by
  have hCp : ∀ t : ℝ, (a * t ^ 3) / t = a * t ^ 2 := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp
    · field_simp
  have hcongr : (fun t : ℝ => (a * t ^ 3) / t) = (fun t : ℝ => a * t ^ 2) :=
    funext hCp
  simp only [absoluteEntropy]
  have hfilter : (∅ : Finset (Fin 1)).filter (fun _ => (1:ℝ) ≤ T) = ∅ :=
    Finset.filter_false_of_mem (fun _ hk => by simp at hk)
  rw [hfilter, Finset.sum_empty, add_zero, hcongr,
    intervalIntegral.integral_const_mul, integral_pow, show (2 + 1 : ℕ) = 3 from rfl]
  push_cast
  ring

/-- The Debye integrand `a * t ^ 3 / t` is interval integrable on every `0..T`, so the value
above is a genuine entropy, not a junk value. -/
example (a T : ℝ) :
    IntervalIntegrable (fun t : ℝ => a * t ^ 3 / t) MeasureTheory.volume 0 T := by
  have hcongr : (fun t : ℝ => a * t ^ 3 / t) = (fun t : ℝ => a * t ^ 2) := by
    funext t
    by_cases ht : t = 0
    · subst ht
      simp
    · field_simp
  rw [hcongr]
  exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable 0 T

/-- One transition at `Tt = 100` with `ΔH = 600` and zero heat capacity: below it, at
`T = 50`, the transition does not contribute and `S = 0`. -/
example :
    absoluteEntropy (fun _ => 0) ({0} : Finset (Fin 1)) (fun _ => 100) (fun _ => 600) 50
      = 0 := by
  norm_num [absoluteEntropy, Finset.filter_singleton]

/-- At the transition temperature, `T = Tt = 100`, the transition counts (the filter is
`Tt k ≤ T`): `S = 600 / 100 = 6`. -/
example :
    absoluteEntropy (fun _ => 0) ({0} : Finset (Fin 1)) (fun _ => 100) (fun _ => 600) 100
      = 6 := by
  norm_num [absoluteEntropy, Finset.filter_singleton]

/-- Above it, at `T = 150`, `S = 6`. -/
example :
    absoluteEntropy (fun _ => 0) ({0} : Finset (Fin 1)) (fun _ => 100) (fun _ => 600) 150
      = 6 := by
  norm_num [absoluteEntropy, Finset.filter_singleton]

/-- Two transitions, `Tt = ![100, 300]` and `ΔH = ![600, 900]`: at `T = 200` only the first
counts, `S = 6`. -/
example :
    absoluteEntropy (fun _ => 0) (Finset.univ : Finset (Fin 2)) ![100, 300] ![600, 900] 200
      = 6 := by
  norm_num [absoluteEntropy, Finset.sum_filter, Fin.sum_univ_two]

/-- At `T = 300` both count: `S = 6 + 3 = 9`. -/
example :
    absoluteEntropy (fun _ => 0) (Finset.univ : Finset (Fin 2)) ![100, 300] ![600, 900] 300
      = 9 := by
  norm_num [absoluteEntropy, Finset.sum_filter, Fin.sum_univ_two]

/-- Heat capacity and a transition together: Debye `Cp t = a * t ^ 3` with one transition at
`Tt = 100`, `ΔH = 600`, gives `S(T) = a * T ^ 3 / 3 + 6` for `100 ≤ T`. -/
example (a T : ℝ) (hT : 100 ≤ T) :
    absoluteEntropy (fun t => a * t ^ 3) ({0} : Finset (Fin 1)) (fun _ => 100) (fun _ => 600) T
      = a * T ^ 3 / 3 + 6 := by
  have hcongr : (fun t : ℝ => (a * t ^ 3) / t) = (fun t : ℝ => a * t ^ 2) := by
    funext t
    by_cases ht : t = 0
    · subst ht
      simp
    · field_simp
  have hfilter : ({0} : Finset (Fin 1)).filter (fun _ => (100:ℝ) ≤ T) = {0} :=
    Finset.filter_true_of_mem (fun _ _ => hT)
  simp only [absoluteEntropy]
  rw [hfilter, Finset.sum_singleton, hcongr, intervalIntegral.integral_const_mul, integral_pow,
    show (2 + 1 : ℕ) = 3 from rfl]
  push_cast
  ring

/-- `S(0) = 0` with no transitions. -/
example (Cp : ℝ → ℝ) :
    absoluteEntropy Cp (∅ : Finset (Fin 1)) (fun _ => 1) (fun _ => 0) 0 = 0 :=
  absoluteEntropy_zero Cp ∅ _ _ (fun _ hk => by simp at hk)

/-!

## E. Boundary checks

-/

/-- (e) Boundary case: `Tc = Th` gives efficiency `0` — no work from a single reservoir. -/
example : carnotEfficiency 300 300 = 0 := by
  unfold carnotEfficiency
  norm_num

/-- (e) Boundary case: at `Tc = 0` the formula would give efficiency `1`, which is why the
Carnot-cycle lemmas assume `0 < Tc`. -/
example : carnotEfficiency 0 600 = 1 := by
  unfold carnotEfficiency
  norm_num

/-- (e) Outside the domain: at `Th = 0`, Lean's `x / 0 = 0` gives `carnotEfficiency 300 0 = 1`.
This is a junk value, not an efficiency; the lemmas that read `carnotEfficiency` assume
`0 < Th`. -/
example : carnotEfficiency 300 0 = 1 := by
  unfold carnotEfficiency
  simp

/-- (e) Outside the domain: with constant `cv`, heating from `T₁ → 0` to `300` has a divergent
entropy change, but at `T₁ = 0` Lean's `300 / 0 = 0` and `Real.log 0 = 0` give the junk value
`0`, which is not an entropy change. The lemmas that read `idealGasEntropyChange` physically
have hypotheses that keep `T₂ / T₁` and `V₂ / V₁` positive. -/
example : idealGasEntropyChange 1 1 1 0 1 300 1 = 0 := by
  unfold idealGasEntropyChange
  simp

/-- (e) Outside the domain: a constant heat capacity `Cp = 1` down to `0 K` makes
`Cp t / t = 1 / t`, which is not interval integrable on `0..1` (`∫₀¹ dt / t` diverges). -/
example : ¬ IntervalIntegrable (fun t : ℝ => (1:ℝ) / t) MeasureTheory.volume 0 1 := by
  simp only [one_div, intervalIntegrable_inv_iff]
  norm_num

/-- (e) …so `absoluteEntropy` returns Lean's junk value `0` for it
(`intervalIntegral.integral_undef`). This `0` is not an entropy; `hasDerivAt_absoluteEntropy`
and `absoluteEntropy_mono` assume integrability and do not apply. -/
example :
    absoluteEntropy (fun _ => (1:ℝ)) (∅ : Finset (Fin 1)) (fun _ => 1) (fun _ => 0) 1 = 0 := by
  have h : ¬ IntervalIntegrable (fun t : ℝ => (1:ℝ) / t) MeasureTheory.volume 0 1 := by
    simp only [one_div, intervalIntegrable_inv_iff]
    norm_num
  simp only [absoluteEntropy, intervalIntegral.integral_undef h, Finset.filter_empty,
    Finset.sum_empty, add_zero]

/-- (e) Boundary case: `x = ![2, -1]` sums to `1` but has a negative fraction. -/
example : ∑ i, (![2, -1] : Fin 2 → ℝ) i = 1 := by
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- (e) Countermodel: for `x = ![2, -1]` the mixing entropy is `-2 * log 2 < 0`, so the
hypothesis `∀ i, 0 ≤ x i` of `entropyOfMixing_nonneg` cannot be dropped. Such an `x` is not a
mole-fraction vector, and the value (which uses Lean's `Real.log (-1) = Real.log 1 = 0`) is not
an entropy. -/
example : entropyOfMixing 1 1 (![2, -1] : Fin 2 → ℝ) < 0 := by
  rw [entropyOfMixing_eq_neg_sum, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.log_neg_eq_log, Real.log_one]
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  linarith

end PhyslibExtTest.Chemistry.Thermodynamics
