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
public import Mathlib.Data.Real.Basic
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
/-- **Well-distributed sequences.** A sequence $(x_m)_{m \in \mathbb{N}}$ of real numbers is
well-distributed if for every $\varepsilon > 0$ there is a $K$ such that for all $k \ge K$, all
$n \in \mathbb{N}$ and all real numbers $a, b$ with $0 \le a \le b \le 1$, the number $N$ of
indices $m$ with $n < m \le n + k$ and $x_m \in [a, b)$ satisfies $|N - (b - a)k| < \varepsilon k$.

No condition $x_m \in [0, 1)$ is imposed, so finite changes to a sequence do not affect this
property.

Source: EP-997 (Erdős Problem #997) [Erdős Problems]. -/
def WellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in Filter.atTop, ∀ n : ℕ,
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      let I := Set.Ico a b
      let count := (Finset.Ioc n (n + k)).filter (fun m ↦ x m ∈ I)
      abs ((count.card : ℝ) - (b - a) * k) < ε * k

/-- **Fractional parts of multiples of the primes.** For a real number $\alpha$, this is the
sequence taking $n \in \mathbb{N}$ to the fractional part $\{\alpha p_n\} = \alpha p_n -
\lfloor \alpha p_n \rfloor$, where $p_0 = 2, p_1 = 3, p_2 = 5, \dots$ are the primes in
increasing order.

Source: EP-997 (Erdős Problem #997) [Erdős Problems]. -/
noncomputable def primeFract (α : ℝ) (n : ℕ) : ℝ :=
  Int.fract (α * (Nat.nth Nat.Prime n : ℝ))

/-- **Statement of Erdős Problem 997.** For every real number $\alpha$, the sequence
$n \mapsto \{\alpha p_n\}$ of fractional parts of $\alpha$ times the primes
$p_0 = 2, p_1 = 3, p_2 = 5, \dots$ is not well-distributed.

Source: EP-997 (Erdős Problem #997) [Erdős Problems]. -/
noncomputable def Statement : Prop :=
  ∀ α : ℝ, ¬ WellDistributed (primeFract α)

/--
**Erdős Problem 997 holds.** For every real number $\alpha$, the sequence
$n \mapsto \{\alpha p_n\}$ of fractional parts of $\alpha$ times the primes
$p_0 = 2, p_1 = 3, p_2 = 5, \dots$ is not well-distributed.

Source: Boris Alexeev, Mark Putterman,
Mehtaab Sawhney, Mark Sellke, and Gregory Valiant, Short proofs in combinatorics and number
theory, arXiv:2603.29961 (2026), https://arxiv.org/abs/2603.29961. Moved from
`OpenConjectures/NumberTheory/ErdosProblem997`. Resolved true: Alexeev, Putterman, Sawhney,
Sellke, and Valiant proved that the prime-indexed fractional-part sequence is never
well-distributed.
-/
public theorem_wanted Statement_holds : Statement

end MathlibExt.NumberTheory.ErdosProblem997Wanted
