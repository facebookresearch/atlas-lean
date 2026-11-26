/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.LanderGreenLikelihoodEqForward
import Mathlib.Tactic.NormNum

/-!
# Tests for `Domains.Biology.StatisticalGenetics.LanderGreenLikelihoodEqForward`

The forward recursion holds on one-meiosis one-locus and two-locus instances with uniform
data, and at `m = 0` the likelihood unfolds to the uniform prior times the data likelihood.
-/

@[expose] public section

namespace DomainsTest.Biology.StatisticalGenetics.LanderGreenLikelihoodEqForward

open WantedExt.Biology.StatisticalGenetics.LanderGreenWanted

example : likelihood (n := 1) 0 (fun _ : ℕ => (1 / 4 : ℝ))
    (fun _ : ℕ => fun _ : InheritanceVector 1 => (1 / 2 : ℝ)) =
    ∑ w : InheritanceVector 1, forward (fun _ : ℕ => (1 / 4 : ℝ))
      (fun _ : ℕ => fun _ : InheritanceVector 1 => (1 / 2 : ℝ)) 0 w := by
  apply likelihood_eq_forward
  · intro i
    norm_num
  · intro i _ w
    norm_num

example : likelihood (n := 1) 1 (fun _ : ℕ => (1 / 4 : ℝ))
    (fun _ : ℕ => fun _ : InheritanceVector 1 => (1 / 2 : ℝ)) =
    ∑ w : InheritanceVector 1, forward (fun _ : ℕ => (1 / 4 : ℝ))
      (fun _ : ℕ => fun _ : InheritanceVector 1 => (1 / 2 : ℝ)) 1 w := by
  apply likelihood_eq_forward
  · intro i
    norm_num
  · intro i _ w
    norm_num

example (n : ℕ) (θ : ℕ → ℝ) (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1 / 2)
    (q : ℕ → InheritanceVector n → ℝ) (hq : ∀ i ≤ 0, ∀ w, 0 ≤ q i w ∧ q i w ≤ 1) :
    likelihood (n := n) 0 θ q = ∑ w : InheritanceVector n, uniformPrior n * q 0 w := by
  rw [likelihood_eq_forward n 0 θ hθ q hq]
  rfl

end DomainsTest.Biology.StatisticalGenetics.LanderGreenLikelihoodEqForward
