/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Exact Fisher rate identity

With real rate `r` and inflation `pi`, the nominal rate is defined by the
exact gross relation `1 + i = (1 + r) * (1 + pi)`. The additive form
`i = r + pi` is only an approximation: it drops exactly the cross term
`r * pi`. The adjacent `MathlibExt.Economics.Finance.RealNominal` assumes
this relation to prove an NPV equality; this file proves the identity
itself, the approximation error, and a concrete counterexample.

## Main results

* `MathlibExt.Economics.Macro.FisherRate.fisher_exact`: `1 + i = (1 + r) * (1 + pi)`.
* `MathlibExt.Economics.Macro.FisherRate.fisher_approx_error`:
  `i - (r + pi) = r * pi`.
* `MathlibExt.Economics.Macro.FisherRate.fisher_example`: at `r = pi = 1/10`
  the exact rate is `21/100`, not `1/5`.

## References

* I. Fisher, *The Theory of Interest*, Macmillan (1930).
* Atlas roadmap target MA02.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.FisherRate

/-- The nominal rate implied by the exact Fisher relation. -/
noncomputable def fisherNominalRate (r π : ℝ) : ℝ :=
  (1 + r) * (1 + π) - 1

/-- The gross nominal return factor. -/
noncomputable def fisherGrossNominal (r π : ℝ) : ℝ :=
  (1 + r) * (1 + π)

/-- **Exact Fisher identity:** `1 + i = (1 + r) * (1 + π)`. -/
theorem fisher_exact (r π : ℝ) :
    1 + fisherNominalRate r π = (1 + r) * (1 + π) := by
  unfold fisherNominalRate
  ring

/-- **Approximation error:** the additive approximation `i ≈ r + π` drops
exactly the cross term `r * π`. -/
theorem fisher_approx_error (r π : ℝ) :
    fisherNominalRate r π - (r + π) = r * π := by
  unfold fisherNominalRate
  ring

/-- **Concrete failure of the approximation.** At `r = π = 1/10` the exact
nominal rate is `21/100`, not `1/5`, and the dropped cross term is `1/100`. -/
theorem fisher_example :
    fisherNominalRate (1 / 10) (1 / 10) = 21 / 100 ∧
      fisherNominalRate (1 / 10) (1 / 10) - (1 / 10 + 1 / 10) = 1 / 100 ∧
      fisherNominalRate (1 / 10) (1 / 10) ≠ 1 / 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold fisherNominalRate <;> norm_num

end MathlibExt.Economics.Macro.FisherRate
