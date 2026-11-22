/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Steady-state unemployment in the two-state employment-flow model

The labour force is normalized to `1`, so employment is `1 - u` and unemployment is `u`.
A fraction `s` of the employed separate per period and a fraction `f` of the unemployed
find jobs per period. Steady state means flow balance: `s * (1 - u) = f * u`. When
`s + f > 0`, the unique steady-state unemployment rate is `u = s / (s + f)`. No
labour-force growth, entry, or exit is modelled. The case `s = f = 0` is excluded: with
no flows every `u` is steady.

In the source (Mankiw), `s` and `f` are the fractions of the employed and of the
unemployed who separate and find jobs each month, so `0 ≤ s ≤ 1` and `0 ≤ f ≤ 1` there.
The results need no upper bound: uniqueness uses only flow balance and `0 < s + f`, and
the verification uses only `0 ≤ s`, `0 ≤ f`, and `0 < s + f`. They therefore also cover
continuous-time flow intensities, whose steady state solves the same balance equation.

## Main results

* `steady_unemployment`: flow balance plus `0 < s + f` gives `u = s / (s + f)`.
* `steady_unemployment_satisfies`: `s / (s + f)` satisfies flow balance and lies in `[0, 1]`.
* `steady_unemployment_example`: `s = 0.02`, `f = 0.38`, `u = 1 / 20`.

## References

* N. G. Mankiw, *Macroeconomics*, 11th ed., Chapter 7 (Unemployment and the Labor Market),
  section "Job Loss, Job Finding, and the Natural Rate of Unemployment": the steady-state
  condition `f U = s E` and the natural rate `U / L = s / (s + f)`.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.EmploymentFlows

/-- **Steady-state unemployment in the two-state flow model.** The labour force is
normalized to `1`, so employment is `1 - u` and unemployment is `u`. In each period a
fraction `s` of the employed separate and a fraction `f` of the unemployed find jobs.
Steady state means flows balance: `s * (1 - u) = f * u`. When `s + f > 0`, the unique
steady-state unemployment rate is `u = s / (s + f)`. No labour-force growth, entry, or
exit is modelled. The calculation needs neither nonnegativity nor an upper bound on `s`
and `f`. The case `s = f = 0` is excluded: with no flows every `u` is steady. -/
theorem steady_unemployment {s f u : ℝ} (hpos : 0 < s + f)
    (hflow : s * (1 - u) = f * u) : u = s / (s + f) := by
  have hne : s + f ≠ 0 := ne_of_gt hpos
  field_simp
  linarith [hflow]

/-- **Verification.** The rate `s / (s + f)` satisfies the steady-state flow-balance
equation, and it lies in `[0, 1]` when `s, f ≥ 0` and `s + f > 0`. -/
theorem steady_unemployment_satisfies {s f : ℝ} (hs : 0 ≤ s) (hf : 0 ≤ f)
    (hpos : 0 < s + f) :
    s * (1 - s / (s + f)) = f * (s / (s + f)) ∧ 0 ≤ s / (s + f) ∧ s / (s + f) ≤ 1 := by
  have hne : s + f ≠ 0 := ne_of_gt hpos
  refine ⟨?_, div_nonneg hs (le_of_lt hpos), ?_⟩
  · field_simp
    ring
  · apply div_le_one_of_le₀ _ (le_of_lt hpos)
    linarith

/-- Concrete steady state: separation rate `s = 0.02`, finding rate `f = 0.38`, so
`u = 0.02 / 0.40 = 1 / 20 = 0.05`. The flow-balance equation holds at `u = 1 / 20`. -/
theorem steady_unemployment_example :
    (0.02 : ℝ) * (1 - 1 / 20) = 0.38 * (1 / 20) := by
  norm_num

end MathlibExt.Economics.Macro.EmploymentFlows
