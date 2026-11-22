/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.HybridArgument
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Boundary check: constant distribution sequences have zero
distinguishing advantage on any event. -/
example (p : PMF Bool) (E : Finset Bool) (k : ℕ) :
    |(∑ a ∈ E, (p a).toReal) - (∑ a ∈ E, (p a).toReal)| ≤ k * (0 : ℝ) :=
  hybrid_argument (fun _ => p) E (ε := 0) k (fun i _ => by simp)

/-- Hybrids that agree up to index `2` and change at index `3`. -/
private noncomputable def switchAtThree (i : ℕ) : PMF Bool :=
  if i ≤ 2 then PMF.pure true else PMF.pure false

/-- Finite hybrid range: the bound for `k = 2` uses only the steps `i < 2`,
although the step from `2` to `3` changes the event probability by `1`. -/
example : |(∑ a ∈ ({true} : Finset Bool), (switchAtThree 0 a).toReal) -
    (∑ a ∈ ({true} : Finset Bool), (switchAtThree 2 a).toReal)| ≤ 0 := by
  have h := hybrid_argument switchAtThree {true} (ε := 0) 2 (fun i hi => by
    have h1 : i ≤ 2 := by omega
    have h2 : i + 1 ≤ 2 := by omega
    simp [switchAtThree, h1, h2])
  simpa using h

/-- Prefix form: steps bounded below `k = 3` bound the hybrid `p 2` by `2 * ε`. -/
example (p : ℕ → PMF Bool) (E : Finset Bool) (ε : ℝ)
    (hstep : ∀ i < 3, |(∑ a ∈ E, (p i a).toReal) - (∑ a ∈ E, (p (i + 1) a).toReal)| ≤ ε) :
    |(∑ a ∈ E, (p 0 a).toReal) - (∑ a ∈ E, (p 2 a).toReal)| ≤ (2 : ℕ) * ε :=
  hybrid_argument_le p E (by norm_num) hstep
