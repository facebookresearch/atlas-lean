/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.DecoupledTwoPointRefutation

/-!
# Tests for the failure of the two-point inequality at `p = 9/10`

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.DecoupledTwoPointRefutation`:

* `dtpc_pbiasedHCLib_nine_tenths_false` next to the proved `p = 1/2` case `htl_lib_half`, so the
  predicate `PBiasedHCLib` is neither vacuous nor trivial;
* at `p = 9/10` and `ρ = 0` the two-point inequality still holds (`htl_lib_rho_zero`): the
  refutation needs the noise parameter `ρ > 0`;
* `dtpc_remainingGoal_false` at `q = 1`, and the consequence that no window `(1/2, q)` with
  `q > 9/10` satisfies the hypothesis of the window-conditional theorems of `HCTensorLib`;
* `stw_RemainingGoal q` holds for `q ≤ 1/2` only because the window is empty; this library
  proves it for no `q > 1/2`;
* the witness numbers: at `u = 1, v = 0, ρ = 1/2` the coupled left side `181/10000`, the norm
  `(1/10)^(8/5)` and the decoupled left side `13/400` are in increasing order
  (`dtpc_coupled_true_at_witness`, `dtpc_witness_rhs_lt_lhs`).
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.DecoupledTwoPointRefutation

open StatMech StatMech.Probability

example : ¬ PBiasedHCLib (9 / 10) := dtpc_pbiasedHCLib_nine_tenths_false

example : PBiasedHCLib (1 / 2) := htl_lib_half

/-- At `ρ = 0` the two-point inequality holds at `p = 9/10` for every `u, v`. -/
example (u v : ℝ) :
    ((1 - (9 / 10 : ℝ)) * u + (9 / 10) * v) ^ 2
        + (0 : ℝ) ^ 2 * ((9 / 10) * (1 - 9 / 10)) * (u - v) ^ 2
      ≤ ((1 - (9 / 10 : ℝ)) * |u| ^ (1 + (0 : ℝ) ^ 2) + (9 / 10) * |v| ^ (1 + (0 : ℝ) ^ 2))
          ^ (2 / (1 + (0 : ℝ) ^ 2)) :=
  htl_lib_rho_zero (by norm_num) (by norm_num) u v

example : ¬ stw_RemainingGoal 1 := dtpc_remainingGoal_false (by norm_num)

/-- No window `(1/2, q)` with `q > 9/10` carries the two-point inequality. -/
example {q : ℝ} (hq : 9 / 10 < q) : ¬ ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p :=
  fun H => dtpc_pbiasedHCLib_nine_tenths_false (H _ ⟨by norm_num, hq⟩)

/-- `stw_RemainingGoal q` for `q ≤ 1/2` holds because `(1/2, q)` is empty. -/
lemma stw_remainingGoal_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : stw_RemainingGoal q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : stw_RemainingGoal (1 / 2) := stw_remainingGoal_of_le_half le_rfl

example : (181 / 10000 : ℝ) ≤ ((1 : ℝ) / 10) ^ ((8 : ℝ) / 5)
    ∧ ((1 : ℝ) / 10) ^ ((8 : ℝ) / 5) < 13 / 400 := by
  refine ⟨?_, dtpc_witness_rhs_lt_lhs⟩
  have h := dtpc_coupled_true_at_witness
  norm_num at h ⊢
  exact h

end StatMechTest.BooleanFunctions.DecoupledTwoPointRefutation
