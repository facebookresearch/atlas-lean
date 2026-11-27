/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.BinomialEventCount
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for the number of independent events that occur

For independent events of probability `p`: none of `n` occur with probability `(1 - p) ^ n`,
exactly one of two occurs with probability `2 p (1 - p)`, all `n` occur with probability `p ^ n`,
at least one of two occurs with probability `1 - (1 - p) ^ 2`, and more than `n` of them never
occur.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Probability.Distributions.BinomialEventCount

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {p : ℝ}

/-- None of `n` independent events of probability `p` occur with probability `(1 - p) ^ n`. -/
example {n : ℕ} {E : Fin n → Set Ω} (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = p) :
    μ.real {ω | {i | ω ∈ E i}.ncard = 0} = (1 - p) ^ n := by
  rw [h.measureReal_ncard_eq hE hp 0]
  simp

/-- Exactly one of two independent events of probability `p` occurs with probability
`2 p (1 - p)`. -/
example {E : Fin 2 → Set Ω} (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = p) :
    μ.real {ω | {i | ω ∈ E i}.ncard = 1} = 2 * p * (1 - p) := by
  rw [h.measureReal_ncard_eq hE hp 1]
  norm_num

/-- All `n` independent events of probability `p` occur with probability `p ^ n`. -/
example {n : ℕ} {E : Fin n → Set Ω} (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = p) :
    μ.real {ω | n ≤ {i | ω ∈ E i}.ncard} = p ^ n := by
  rw [h.measureReal_le_ncard hE hp n]
  simp

/-- At least one of two independent events of probability `p` occurs with probability
`1 - (1 - p) ^ 2`. -/
example {E : Fin 2 → Set Ω} (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = p) :
    μ.real {ω | 1 ≤ {i | ω ∈ E i}.ncard} = 1 - (1 - p) ^ 2 := by
  rw [h.measureReal_le_ncard hE hp 1, show Icc 1 2 = {1, 2} from rfl, sum_pair (by norm_num)]
  norm_num
  ring

/-- More than `n` of `n` events never occur. -/
example {n : ℕ} {E : Fin n → Set Ω} (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = p) :
    μ.real {ω | n + 1 ≤ {i | ω ∈ E i}.ncard} = 0 := by
  rw [h.measureReal_le_ncard hE hp (n + 1)]
  simp

end MathlibExtTest.Probability.Distributions.BinomialEventCount
