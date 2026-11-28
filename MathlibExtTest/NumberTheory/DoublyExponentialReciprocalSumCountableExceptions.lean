/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Real.Cardinality
import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumCountableExceptions

open Filter Topology MetaMathlibExt

namespace MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumCountableExceptions

-- The public theorem retains the exact set of exceptions, including the zero-based exponent.
example : Set.Countable {α : ℝ | 1 < α ∧ ¬∀ b : ℕ → ℕ, (∀ n, 0 < b n) →
    Tendsto (fun n => (b n : ℝ) / ⌊α ^ 2 ^ (n + 1)⌋₊) atTop (𝓝 1) →
      ∀ q : ℚ, ¬HasSum (fun n => 1 / (b n : ℝ)) q} :=
  countable_not_type2IrrationalitySequence_floor_pow_two_pow

-- Every nonempty open interval above one contains a base with the Type 2 property.
example {x y : ℝ} (hx : 1 ≤ x) (hxy : x < y) :
    ∃ α ∈ Set.Ioo x y, ∀ b : ℕ → ℕ, (∀ n, 0 < b n) →
      Tendsto (fun n => (b n : ℝ) / ⌊α ^ 2 ^ (n + 1)⌋₊) atTop (𝓝 1) →
        ∀ q : ℚ, ¬HasSum (fun n => 1 / (b n : ℝ)) q := by
  by_contra h
  apply hxy.not_ge
  apply Cardinal.Real.Ioo_countable_iff.mp
  refine countable_not_type2IrrationalitySequence_floor_pow_two_pow.mono ?_
  intro α hα
  exact ⟨hx.trans_lt hα.1, fun hgood => h ⟨α, hα, hgood⟩⟩

end MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumCountableExceptions
