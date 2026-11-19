/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Exact Fisher rate identity

The Fisher relation links a nominal rate `i`, a real rate `r` and inflation
`π` by the exact gross relation `1 + i = (1 + r) * (1 + π)`. For an arbitrary
`i`, the relation holds exactly when `i = r + π + r * π`, so the additive
form `i = r + π` is only an approximation: it drops exactly the cross term
`r * π`. The adjacent `MathlibExt.Economics.Finance.RealNominal` assumes
this relation to prove an NPV equality.

`fisherNominalRate r π` is the conversion definition `(1 + r) * (1 + π) - 1`,
the nominal rate that the relation determines. That it satisfies the relation
(`fisher_exact`) holds by construction and is not a separate economic claim;
`fisher_approx_error` and `fisher_example` specialize the results to it.

## Main results

* `MathlibExt.Economics.Macro.FisherRate.fisher_relation_iff`: for any `i`,
  `1 + i = (1 + r) * (1 + π) ↔ i = r + π + r * π`.
* `MathlibExt.Economics.Macro.FisherRate.fisher_approx_error_of_relation`:
  if `1 + i = (1 + r) * (1 + π)`, then `i - (r + π) = r * π`.
* `MathlibExt.Economics.Macro.FisherRate.fisher_exact`: the conversion
  definition satisfies the relation, by construction.
* `MathlibExt.Economics.Macro.FisherRate.fisher_approx_error`: the same error
  for the converted rate, derived from the relation.
* `MathlibExt.Economics.Macro.FisherRate.fisher_example`: at `r = π = 1/10`
  the exact rate is `21/100`, not `1/5`.

## References

* I. Fisher, *The Theory of Interest*, Macmillan (1930).
* Atlas roadmap target MA02.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.FisherRate

/-- **Fisher relation for an arbitrary nominal rate.** A nominal rate `i`
satisfies the exact gross relation `1 + i = (1 + r) * (1 + π)` if and only if
`i = r + π + r * π`. -/
theorem fisher_relation_iff (i r π : ℝ) :
    1 + i = (1 + r) * (1 + π) ↔ i = r + π + r * π := by
  constructor <;> intro h <;> linear_combination h

/-- **Approximation error for an arbitrary nominal rate.** If
`1 + i = (1 + r) * (1 + π)`, the additive approximation `i ≈ r + π` drops
exactly the cross term: `i - (r + π) = r * π`. -/
theorem fisher_approx_error_of_relation {i r π : ℝ}
    (h : 1 + i = (1 + r) * (1 + π)) : i - (r + π) = r * π := by
  rw [(fisher_relation_iff i r π).mp h]
  ring

/-- Conversion definition: the nominal rate `(1 + r) * (1 + π) - 1` that the
Fisher relation determines from the real rate `r` and inflation `π`
(see `fisher_relation_iff`). -/
noncomputable def fisherNominalRate (r π : ℝ) : ℝ :=
  (1 + r) * (1 + π) - 1

/-- The gross nominal return factor. -/
noncomputable def fisherGrossNominal (r π : ℝ) : ℝ :=
  (1 + r) * (1 + π)

/-- **The conversion definition satisfies the Fisher relation:**
`1 + fisherNominalRate r π = (1 + r) * (1 + π)`. This holds by construction
of `fisherNominalRate` and is not an economic claim; for an independently
given nominal rate, see `fisher_relation_iff`. -/
theorem fisher_exact (r π : ℝ) :
    1 + fisherNominalRate r π = (1 + r) * (1 + π) := by
  unfold fisherNominalRate
  ring

/-- **Approximation error for the converted rate:** the additive
approximation `i ≈ r + π` drops exactly the cross term `r * π`. Derived from
the relation via `fisher_approx_error_of_relation`. -/
theorem fisher_approx_error (r π : ℝ) :
    fisherNominalRate r π - (r + π) = r * π :=
  fisher_approx_error_of_relation (fisher_exact r π)

/-- **Concrete failure of the approximation.** At `r = π = 1/10` the exact
nominal rate is `21/100`, not `1/5`, and the dropped cross term is `1/100`. -/
theorem fisher_example :
    fisherNominalRate (1 / 10) (1 / 10) = 21 / 100 ∧
      fisherNominalRate (1 / 10) (1 / 10) - (1 / 10 + 1 / 10) = 1 / 100 ∧
      fisherNominalRate (1 / 10) (1 / 10) ≠ 1 / 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold fisherNominalRate <;> norm_num

end MathlibExt.Economics.Macro.FisherRate
