/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two-period overlapping generations

A specified Diamond-style two-period overlapping generations economy:
population grows at rate `n`; the technology is Cobb-Douglas
`F(K, L) = A * K^(1/2) * L^(1/2)`, so the per-worker wage is the marginal
product of labour `w = A/2 * sqrt k`; young workers have log utility
`log (w - s) + β * log (R * s)`; capital fully depreciates, so capital
market clearing gives per-worker `k[t+1] = s[t] / (1+n)`. The proved
optimal savings rule is `s = β/(1+β) * w`, and capital per worker obeys
`k[t+1] = olgCapitalFactor A β n * sqrt (k[t])`.

This is the frozen specification of the result, not the general Diamond
model: general Cobb-Douglas exponents, partial depreciation, and general
utility are not claimed. The steady state is a fixed point of the
recurrence, not a stability claim.

## Main results

* `MathlibExt.Economics.Macro.OverlappingGenerations.logUtility_optimalSavings`:
  log-utility savings are maximized at `β/(1+β) * w`, independent of `R`.
* `MathlibExt.Economics.Macro.OverlappingGenerations.olg_capitalRecurrence`:
  the derived capital-market recurrence.
* `MathlibExt.Economics.Macro.OverlappingGenerations.olg_steadyState`:
  `k = (olgCapitalFactor A β n)^2` is a fixed point of the recurrence.

## References

Atlas roadmap target MA08.T03. Diamond (1965), overlapping generations;
Blanchard–Fischer, *Lectures on Macroeconomics* (OLG model).
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.OverlappingGenerations

/-- Wage per young worker in the specified OLG economy: the marginal product of
labour of the Cobb-Douglas technology `F(K, L) = A * K ^ (1/2) * L ^ (1/2)`,
so in per-worker terms `w = (1 - 1/2) * A * sqrt k = A / 2 * sqrt k`, where `k`
is capital per worker. -/
noncomputable def olgWage (A k : ℝ) : ℝ := A / 2 * Real.sqrt k

/-- Savings per young worker under log utility: the optimal savings rule
`β / (1 + β) * w` proved in `logUtility_optimalSavings` below. -/
noncomputable def olgSavings (β w : ℝ) : ℝ := β / (1 + β) * w

/-- Capital-market factor: with population growth `n` (`N[t+1] = (1+n) * N[t]`),
full depreciation (two-period lives: capital lasts one generation), and capital
market clearing `K[t+1] = N[t] * s[t]`, capital per worker obeys
`k[t+1] = olgCapitalFactor A β n * sqrt (k[t])`. -/
noncomputable def olgCapitalFactor (A β n : ℝ) : ℝ :=
  β * A / (2 * (1 + β) * (1 + n))

/-- **Optimal savings under log utility.** A young worker with wage `w > 0`,
discount factor `β > 0`, and gross return `R = 1 + r > 0` on savings chooses
`s` in `(0, w)` to maximize `log (w - s) + β * log (R * s)` (log consumption
when young plus discounted log consumption when old). The maximum is attained
at `s = olgSavings β w = β / (1 + β) * w`, independent of `R`. The proof uses
the weighted log inequality from `Real.log_le_sub_one_of_pos`: the weighted
average of the ratios `(w - s) / (w - s*)` and `s / s*` with weights
`1 / (1 + β)` and `β / (1 + β)` equals `1`; no calculus is used. -/
theorem logUtility_optimalSavings {w β R : ℝ} (hw : 0 < w) (hβ : 0 < β) (hR : 0 < R)
    {s : ℝ} (hs0 : 0 < s) (hsw : s < w) :
    Real.log (w - s) + β * Real.log (R * s) ≤
      Real.log (w - olgSavings β w) + β * Real.log (R * olgSavings β w) := by
  have h1β : (0:ℝ) < 1 + β := by linarith
  have h1βne : (1:ℝ) + β ≠ 0 := ne_of_gt h1β
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hwne : w ≠ 0 := ne_of_gt hw
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hRne : R ≠ 0 := ne_of_gt hR
  have hws : (0:ℝ) < w - s := by linarith
  have hwsne : w - s ≠ 0 := ne_of_gt hws
  have hsstar : olgSavings β w = β / (1 + β) * w := rfl
  have hsstar_pos : (0:ℝ) < olgSavings β w := by
    rw [hsstar]
    positivity
  have hsstar_ne : olgSavings β w ≠ 0 := ne_of_gt hsstar_pos
  have hwsstar_eq : w - olgSavings β w = w / (1 + β) := by
    unfold olgSavings
    field_simp
    ring
  have hwss : (0:ℝ) < w - olgSavings β w := by
    rw [hwsstar_eq]
    positivity
  have hwssne : w - olgSavings β w ≠ 0 := ne_of_gt hwss
  have ha_pos : (0:ℝ) < (w - s) / (w - olgSavings β w) := by positivity
  have hb_pos : (0:ℝ) < s / olgSavings β w := by positivity
  have hlog1 : Real.log ((w - s) / (w - olgSavings β w))
      ≤ (w - s) / (w - olgSavings β w) - 1 :=
    Real.log_le_sub_one_of_pos ha_pos
  have hlog2 : Real.log (s / olgSavings β w) ≤ s / olgSavings β w - 1 :=
    Real.log_le_sub_one_of_pos hb_pos
  have hdw : (w:ℝ) / (1 + β) ≠ 0 := div_ne_zero hwne h1βne
  have hds : β / (1 + β) * (w:ℝ) ≠ 0 := mul_ne_zero (div_ne_zero hβne h1βne) hwne
  have havg : 1 / (1 + β) * ((w - s) / (w - olgSavings β w))
      + β / (1 + β) * (s / olgSavings β w) = 1 := by
    rw [hwsstar_eq, hsstar]
    field_simp
    ring
  have hw1_nonneg : (0:ℝ) ≤ 1 / (1 + β) := by positivity
  have hwβ_nonneg : (0:ℝ) ≤ β / (1 + β) := by positivity
  have e1 := mul_le_mul_of_nonneg_left hlog1 hw1_nonneg
  have e2 := mul_le_mul_of_nonneg_left hlog2 hwβ_nonneg
  have hweights : 1 / (1 + β) + β / (1 + β) = (1:ℝ) := by
    field_simp
  have hsum : 1 / (1 + β) * ((w - s) / (w - olgSavings β w) - 1)
      + β / (1 + β) * (s / olgSavings β w - 1) = 0 := by
    linear_combination havg - hweights
  have hcomb : 1 / (1 + β) * Real.log ((w - s) / (w - olgSavings β w))
      + β / (1 + β) * Real.log (s / olgSavings β w) ≤ 0 := by
    calc 1 / (1 + β) * Real.log ((w - s) / (w - olgSavings β w))
          + β / (1 + β) * Real.log (s / olgSavings β w)
        ≤ 1 / (1 + β) * ((w - s) / (w - olgSavings β w) - 1)
          + β / (1 + β) * (s / olgSavings β w - 1) := add_le_add e1 e2
      _ = 0 := hsum
  have elog1 : Real.log ((w - s) / (w - olgSavings β w))
      = Real.log (w - s) - Real.log (w - olgSavings β w) :=
    Real.log_div hwsne hwssne
  have elog2 : Real.log (s / olgSavings β w)
      = Real.log s - Real.log (olgSavings β w) :=
    Real.log_div hsne hsstar_ne
  have elogR1 : Real.log (R * s) = Real.log R + Real.log s :=
    Real.log_mul hRne hsne
  have elogR2 : Real.log (R * olgSavings β w)
      = Real.log R + Real.log (olgSavings β w) :=
    Real.log_mul hRne hsstar_ne
  have hkey : Real.log (w - s) + β * Real.log (R * s)
      - (Real.log (w - olgSavings β w) + β * Real.log (R * olgSavings β w))
      = (1 + β) * (1 / (1 + β) * Real.log ((w - s) / (w - olgSavings β w))
        + β / (1 + β) * Real.log (s / olgSavings β w)) := by
    rw [elog1, elog2, elogR1, elogR2]
    field_simp
    ring
  have hnonpos : (1 + β) * (1 / (1 + β) * Real.log ((w - s) / (w - olgSavings β w))
      + β / (1 + β) * Real.log (s / olgSavings β w)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt h1β) hcomb
  linarith

/-- **OLG capital-market recurrence (MA08.T03).** In the specified two-period
OLG economy (log utility, Cobb-Douglas exponent `1/2`, full depreciation,
population growth `n`, capital market clearing), capital per worker satisfies
`k[t+1] = olgCapitalFactor A β n * sqrt (k[t])`. -/
theorem olg_capitalRecurrence {A β n : ℝ} (hn : 1 + n ≠ 0) (hβ : 1 + β ≠ 0)
    {k : ℕ → ℝ}
    (hk : ∀ t, k (t + 1) = olgSavings β (olgWage A (k t)) / (1 + n)) (t : ℕ) :
    k (t + 1) = olgCapitalFactor A β n * Real.sqrt (k t) := by
  rw [hk t]
  unfold olgSavings olgWage olgCapitalFactor
  field_simp

/-- **OLG steady state.** `k = (olgCapitalFactor A β n) ^ 2` is a fixed point of
the capital-market recurrence: `C * sqrt (C ^ 2) = C ^ 2` for `C ≥ 0`. -/
theorem olg_steadyState {A β n : ℝ} (hC : 0 ≤ olgCapitalFactor A β n) :
    olgCapitalFactor A β n * Real.sqrt ((olgCapitalFactor A β n) ^ 2) =
      (olgCapitalFactor A β n) ^ 2 := by
  rw [Real.sqrt_sq hC]
  ring

end MathlibExt.Economics.Macro.OverlappingGenerations
