/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Primes maximize the Erdős sum of primitive sets (Erdős Problem 164)

Erdős Problem 164: a set `A ⊆ ℕ` is primitive if no member divides another. Is `∑_{n ∈ A} 1/(n log
n)` maximized over all primitive sets when `A` is the set of primes?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.PrimitiveSetErdosSumErdosProblem164Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #164, https://www.erdosproblems.com/164 (status PROVED
(LEAN)). UnsolvedMath record UM-30006746 (`EP-164`), dataset ulamai/UnsolvedMath v1.8.0.

Elements are `≥ 2` (for `1` the term is undefined, and `{1}` is the only primitive set containing
it). The target also asserts that the sum over `A` converges (Erdős 1935), so the inequality is
between genuine sums. Compared with the formal-conjectures statement `ErdosProblems/164.lean` (the
target adds the convergence clause to `erdos_164`; no code imported).
-/

/-- Erdős Problem 164: for every primitive set `A` of integers `≥ 2` (no element divides another),
the Erdős sum `∑_{a ∈ A} 1/(a log a)` converges and is at most `∑_p 1/(p log p)` over the
primes. -/
def primesMaximizeErdosSum : Prop :=
  ∀ A : Set ℕ, (∀ a ∈ A, 2 ≤ a) → (∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b) →
    Summable (fun a : A => 1 / ((a : ℝ) * Real.log a)) ∧
      ∑' a : A, 1 / ((a : ℝ) * Real.log a) ≤
        ∑' p : {p : ℕ | p.Prime}, 1 / ((p : ℝ) * Real.log p)

/--
Resolved true: Erdős proved in 1935 that the sum converges for every primitive set, and Lichtman
proved that it is maximized by the primes (a simpler proof is due to Alexeev, Barreto, Li, Lichtman,
Price, Shah, Tang and Tao); erdosproblems.com/164 lists the problem as proved. Source: T. F. Bloom,
Erdős Problems, Problem #164, https://www.erdosproblems.com/164 (status PROVED (LEAN)); resolution:
J. D. Lichtman, A proof of the Erdős primitive set conjecture, arXiv:2202.02384 (2022), abstract:
answers Erdős's question in the affirmative; convergence for every primitive set: P. Erdős, J.
London Math. Soc. (1935), 126-128; erdosproblems.com/164, https://arxiv.org/abs/2202.02384.
-/
public theorem_wanted primesMaximizeErdosSum_holds : primesMaximizeErdosSum

end MathlibExt.NumberTheory.PrimitiveSetErdosSumErdosProblem164Wanted
