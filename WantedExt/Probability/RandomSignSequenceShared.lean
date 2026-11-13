/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Independent uniform random signs (Erdős Problems 523 and 527)

Shared definition for the random-sign problems: a sequence of measurable, independent random
variables on a probability space, each almost surely `±1` and equal to `1` with probability `1/2`.
Erdős Problem 523 uses it for random polynomials, Erdős Problem 527 for random power series.
-/

module

public import Mathlib.Probability.Independence.Basic

@[expose] public section

namespace MathlibExt.Probability.RandomSignSequenceShared

open MeasureTheory ProbabilityTheory in
/-- `ε 0, ε 1, …` are independent uniform random signs: measurable, independent, `±1` almost
surely, and each equal to `1` with probability `1/2`. -/
def IsRandomSignSequence {Ω : Type*} [MeasureSpace Ω] (ε : ℕ → Ω → ℝ) : Prop :=
  (∀ k, Measurable (ε k)) ∧ iIndepFun ε ∧ (∀ k, ∀ᵐ ω, ε k ω = 1 ∨ ε k ω = -1) ∧
    ∀ k, volume {ω | ε k ω = 1} = 1 / 2

end MathlibExt.Probability.RandomSignSequenceShared
