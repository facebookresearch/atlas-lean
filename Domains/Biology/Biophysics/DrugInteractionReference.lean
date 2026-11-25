/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Interaction reference models are not interchangeable

Two common normalized references for a combined effect of two agents are
Bliss independence, `a + b - a * b` for single-agent effects `a` and `b`,
and same-curve dose addition, `E (dA + dB)` for a normalized response
curve `E`. They obey different conventions and are not interchangeable:
for `E (d) = d / (1 + d)` at unit doses they give `3 / 4` and `2 / 3`,
and the effect `17 / 24` lies strictly between them.

This is a statement about the reference models only. It is not a general
Loewe solver and carries no clinical synergy or efficacy claim.
-/

@[expose] public section

namespace MathlibExt.Biology.Biophysics.DrugInteractionReference

/-- **Interaction references are not interchangeable.** For the normalized
response curve `E(d) = d / (1 + d)` and unit doses of the same agent, the
Bliss reference for the two single effects `E(1) = 1/2` is `3/4`, while the
same-curve dose-addition reference `E(1 + 1)` is `2/3`. The observed effect
`17/24` lies strictly between them, so it departs from the two references
with opposite signs. -/
theorem interact_references_disagree :
    ((1 / 2 : ℝ) + 1 / 2 - (1 / 2 : ℝ) * (1 / 2)) = 3 / 4 ∧
    ((1 + 1 : ℝ) / (1 + (1 + 1))) = 2 / 3 ∧
    (2 / 3 : ℝ) < 17 / 24 ∧ (17 / 24 : ℝ) < 3 / 4 ∧
    (17 / 24 : ℝ) - 3 / 4 < 0 ∧ 0 < (17 / 24 : ℝ) - 2 / 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end MathlibExt.Biology.Biophysics.DrugInteractionReference
