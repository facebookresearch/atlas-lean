/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

/-!
# Erdős Problem #997

For every `α`, the fractional parts `{α * pₙ}` are not well-distributed.
-/

namespace MathlibExt.NumberTheory.ErdosProblem997Wanted

open Classical in
/-- Well-distributed sequences (EP-997 (Erdős Problem #997) [Erdős Problems]):
block frequencies converge uniformly to the lengths of half-open subintervals
of `[0, 1)`. No pointwise range condition is imposed, so finite changes to a
sequence do not affect this property. -/
def WellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in Filter.atTop, ∀ n : ℕ,
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      let I := Set.Ico a b
      let count := (Finset.Ioc n (n + k)).filter (fun m ↦ x m ∈ I)
      abs ((count.card : ℝ) - (b - a) * k) < ε * k

/-- Prime-indexed fractional parts (EP-997 (Erdős Problem #997) [Erdős Problems]):
`primeFract α n` is the fractional part `{α * pₙ}`, where `(pₙ)` is the sequence
of primes. -/
noncomputable def primeFract (α : ℝ) (n : ℕ) : ℝ :=
  Int.fract (α * (Nat.nth Nat.Prime n : ℝ))

/-- Erdős Problem #997 (EP-997 (Erdős Problem #997) [Erdős Problems]): is it true
that for every `α`, the sequence of fractional parts `{α * pₙ}` is not
well-distributed? -/
noncomputable def Statement : Prop :=
  ∀ α : ℝ, ¬ WellDistributed (primeFract α)

/--
Resolved true: Alexeev, Putterman, Sawhney, Sellke, and Valiant proved that the prime-indexed
fractional-part sequence is never well-distributed. Source: Boris Alexeev, Mark Putterman,
Mehtaab Sawhney, Mark Sellke, and Gregory Valiant, Short proofs in combinatorics and number
theory, arXiv:2603.29961 (2026), https://arxiv.org/abs/2603.29961. Moved from
`OpenConjectures/NumberTheory/ErdosProblem997`.
-/
public theorem_wanted Statement_holds : Statement

end MathlibExt.NumberTheory.ErdosProblem997Wanted
