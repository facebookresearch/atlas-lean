/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Government debt ratio recurrence

Nominal government debt `B`, output `Y`, primary deficit `D`. With output
growing at the frozen ratio timing `Y[t+1] = (1+g) * Y[t]` and the nominal
debt law `B[t+1] = (1+r) * B[t] + D[t+1]`, the debt-to-output ratio obeys a
one-step recurrence with coefficient `(1+r)/(1+g)`.

## Main results

* `MathlibExt.Economics.Macro.GovernmentDebtRatio.debtRatio_succ`: the debt
  ratio satisfies `b[t+1] = ((1+r)/(1+g)) * b[t] + d[t+1]`, where `d[t+1]`
  is the primary-deficit ratio against the same-period output denominator.

## References

Atlas roadmap target MA07.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.GovernmentDebtRatio

/-- Debt-to-output ratio `b[t] = B[t] / Y[t]`: nominal government debt over output. -/
noncomputable def debtRatio (B Y : ℕ → ℝ) (t : ℕ) : ℝ := B t / Y t

/-- Primary-deficit-to-output ratio `d[t] = D[t] / Y[t]`, against the same-period
output denominator as `debtRatio`. -/
noncomputable def deficitRatio (D Y : ℕ → ℝ) (t : ℕ) : ℝ := D t / Y t

/-- **Debt-ratio recurrence (MA07.T02).** Under the frozen ratio timing, with
output growth `Y[t+1] = (1+g) * Y[t]` and the nominal debt law
`B[t+1] = (1+r) * B[t] + D[t+1]`, the debt ratio satisfies
`b[t+1] = ((1+r)/(1+g)) * b[t] + d[t+1]`, where `d[t+1]` is the primary-deficit
ratio against the same-period output denominator `Y[t+1]`. -/
theorem debtRatio_succ {r g : ℝ} {B D Y : ℕ → ℝ} (hg : 1 + g ≠ 0)
    (hY : ∀ t, Y t ≠ 0) (hYg : ∀ t, Y (t + 1) = (1 + g) * Y t)
    (hB : ∀ t, B (t + 1) = (1 + r) * B t + D (t + 1)) (t : ℕ) :
    debtRatio B Y (t + 1) = ((1 + r) / (1 + g)) * debtRatio B Y t +
      deficitRatio D Y (t + 1) := by
  unfold debtRatio deficitRatio
  rw [hB t, hYg t]
  have hYt : Y t ≠ 0 := hY t
  have hprod : (1 + g) * Y t ≠ 0 := mul_ne_zero hg hYt
  field_simp

end MathlibExt.Economics.Macro.GovernmentDebtRatio
