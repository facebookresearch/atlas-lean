/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.StickyKernel
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Equal jump rates on a finite state space

On `n + 1` states, suppose the total rate of leaving a state is `μ`, with equal rates
`μ / n` to the `n` other states. The transition matrix is the uniform sticky kernel with
persistence `exp (-(n + 1) μ t / n)`. Its off-diagonal mass is
`n / (n + 1) * (1 - exp (-(n + 1) μ t / n))`.

For `n > 0`, `equalRatesDistance` inverts this last expression to recover `μ t`.
A probabilistic interpretation requires `μ, t ≥ 0`; as usual, the real logarithm and division
are totalized outside the model's parameter range.
-/

@[expose] public section

namespace ProbabilityTheory

/-- The transition probability on `n + 1` states when all `n` possible jumps are equally likely. -/
noncomputable def equalRatesProb (n : ℕ) (μ t : ℝ) (i j : Fin (n + 1)) : ℝ :=
  let m : ℝ := ((n + 1 : ℕ) : ℝ)
  let c := Real.exp (-m * μ * t / n)
  if i = j then 1 / m + n / m * c else 1 / m - 1 / m * c

/-- Equal jump rates give the sticky kernel with uniform redraw probabilities. -/
theorem equalRatesProb_eq_stickyKernel (n : ℕ) (μ t : ℝ) :
    Matrix.of (equalRatesProb n μ t) = stickyKernel (fun _ => 1 / ((n + 1 : ℕ) : ℝ))
      (Real.exp (-((n + 1 : ℕ) : ℝ) * μ * t / n)) := by
  ext i j
  simp only [Matrix.of_apply, equalRatesProb, stickyKernel_apply, Nat.cast_add, Nat.cast_one]
  split_ifs <;> field_simp <;> ring

/-- Recover mean jump count from the mismatch probability, below saturation `n / (n + 1)`. -/
noncomputable def equalRatesDistance (n : ℕ) (p : ℝ) : ℝ :=
  let m : ℝ := ((n + 1 : ℕ) : ℝ)
  (-(n / m)) * Real.log (1 - m / n * p)

end ProbabilityTheory
