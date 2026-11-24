/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Normed
import MathlibExt.Algebra.AffineRecurrenceConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Constant-deficit debt-ratio convergence

An affine recursion `b[t+1] = a * b[t] + d` with `|a| < 1` converges to its
fixed point `d / (1 - a)`. Applied to the debt ratio: with a constant deficit
ratio and a stable coefficient `|(1+r)/(1+g)| < 1`, the debt ratio converges
to `d / (1 - (1+r)/(1+g))`.

## Main results

* `MathlibExt.Economics.Macro.GovernmentDebtConvergence.affineRecurrence_tendsto`:
  affine recursions with `|a| < 1` converge to `d / (1 - a)`.
* `MathlibExt.Economics.Macro.GovernmentDebtConvergence.debtRatio_tendsto_of_stable`:
  the constant-deficit debt ratio converges to its fixed point.

## References

Atlas roadmap target MA07.T03.
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Economics.Macro.GovernmentDebtConvergence

/-- Debt-to-output ratio `b[t] = B[t] / Y[t]`: nominal government debt over output. With the
convention `x / 0 = 0`, `b(t) = 0` when `Y(t) = 0`. -/
noncomputable def debtRatio (B Y : ℕ → ℝ) (t : ℕ) : ℝ := B t / Y t

/-- Primary-deficit-to-output ratio `d[t] = D[t] / Y[t]`, against the same-period output denominator
as `debtRatio`. With the convention `x / 0 = 0`, `d(t) = 0` when `Y(t) = 0`. -/
noncomputable def deficitRatio (D Y : ℕ → ℝ) (t : ℕ) : ℝ := D t / Y t

/-- **Affine recurrence convergence.** An affine recursion `b[t+1] = a * b[t] + d`
with `|a| < 1` converges to the fixed point `d / (1 - a)`. This is a
specialization of geometric decay (`tendsto_pow_atTop_nhds_zero_of_abs_lt_one`). -/
theorem affineRecurrence_tendsto {a d : ℝ} (ha : |a| < 1) {b : ℕ → ℝ}
    (hb : ∀ t, b (t + 1) = a * b t + d) :
    Tendsto b atTop (𝓝 (d / (1 - a))) :=
  MathlibExt.AffineRecurrence.affine_tendsto_fixedPoint hb ha

/-- **Constant-deficit debt-ratio convergence (MA07.T03).** If output is nonzero and grows as
`Y[t+1] = (1+g) * Y[t]` with `1 + g ≠ 0`, debt follows `B[t+1] = (1+r) * B[t] + D[t+1]`, the
deficit ratio `d[t+1] = d` is constant and the coefficient is stable,
`|(1+r)/(1+g)| < 1`, then the debt ratio converges to
`d / (1 - (1+r)/(1+g))`. -/
theorem debtRatio_tendsto_of_stable {r g d : ℝ} {B D Y : ℕ → ℝ}
    (hg : 1 + g ≠ 0) (hY : ∀ t, Y t ≠ 0)
    (hYg : ∀ t, Y (t + 1) = (1 + g) * Y t)
    (hB : ∀ t, B (t + 1) = (1 + r) * B t + D (t + 1))
    (hD : ∀ t, deficitRatio D Y (t + 1) = d)
    (hstable : |(1 + r) / (1 + g)| < 1) :
    Tendsto (debtRatio B Y) atTop (𝓝 (d / (1 - (1 + r) / (1 + g)))) := by
  have hrec : ∀ t, debtRatio B Y (t + 1)
      = (1 + r) / (1 + g) * debtRatio B Y t + d := by
    intro t
    have hYt := hY t
    have hYt1 := hY (t + 1)
    have hprod : (1 + g) * Y t ≠ 0 := mul_ne_zero hg hYt
    have hD' : D (t + 1) = d * Y (t + 1) := by
      have h := hD t
      simp only [deficitRatio] at h
      rwa [div_eq_iff hYt1] at h
    simp only [debtRatio]
    rw [hB t, hD', hYg t]
    field_simp
  exact affineRecurrence_tendsto (a := (1 + r) / (1 + g)) (d := d)
    (b := debtRatio B Y) hstable hrec

end MathlibExt.Economics.Macro.GovernmentDebtConvergence
