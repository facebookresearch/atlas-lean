/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integers `2^k + m` with few prime factors (Erdős Problem 205)

Erdős Problem 205: can every sufficiently large `n` be written `2^k + m` with `Ω(m) < log log m`?
What about `< ε log log m`, or a more slowly growing function?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

namespace MathlibExt.NumberTheory.PowerOfTwoPlusFewPrimeFactorsErdosProblem205Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #205, https://www.erdosproblems.com/205 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006763 (`EP-205`), dataset ulamai/UnsolvedMath v1.8.0.

`m` is a positive integer (the source's `log log m` presupposes it). Each of the three questions is
a separate target. The second is stated for some `ε > 0`, so its refutation covers every `ε > 0`;
"more slowly growing" is `g = o(log log m)`. Compared with the formal-conjectures statements
`ErdosProblems/205.lean` (no code imported; there the second part is the weaker `¬ ∀ ε`).
-/

open Filter Asymptotics

/-- `n = 2 ^ k + m` for some `k ≥ 0` and positive `m` with `Ω(m) < g(m)`, where `Ω(m)` counts the
prime factors of `m` with multiplicity. -/
def IsRepresentable (g : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ k m : ℕ, 0 < m ∧ n = 2 ^ k + m ∧ (ArithmeticFunction.cardFactors m : ℝ) < g m

/-- Erdős Problem 205, first question: every sufficiently large `n` is `2 ^ k + m` with
`Ω(m) < log log m`. -/
def eventuallyRepresentableLogLog : Prop :=
  ∀ᶠ n in atTop, IsRepresentable (fun m => Real.log (Real.log m)) n

/-- Erdős Problem 205, second question: for some `ε > 0`, every sufficiently large `n` is
`2 ^ k + m` with `Ω(m) < ε log log m`. -/
def eventuallyRepresentableEpsLogLog : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop, IsRepresentable (fun m => ε * Real.log (Real.log m)) n

/-- Erdős Problem 205, third question: for some function `g(m) = o(log log m)`, every sufficiently
large `n` is `2 ^ k + m` with `Ω(m) < g(m)`. -/
def eventuallyRepresentableSlowerFunction : Prop :=
  ∃ g : ℕ → ℝ, g =o[atTop] (fun m => Real.log (Real.log m)) ∧
    ∀ᶠ n in atTop, IsRepresentable g n

/--
Resolved false: erdosproblems.com/205 records the negative answer of Barreto and Leeham, quantified
by Tao and Alexeev: for infinitely many `n`, every `n - 2^k` with `2^k < n` has at least `c (log n /
log log n)^{1/2}` prime factors, which exceeds `log log n` for large `n` (formal proof in
plby/lean-proofs, `Erdos205.lean`). Source: T. F. Bloom, Erdős Problems, Problem #205,
https://www.erdosproblems.com/205 (status DISPROVED (LEAN)); resolution: K. Barreto and Leeham (with
ChatGPT and Aristotle), negative answer, quantified by T. Tao and B. Alexeev in the
erdosproblems.com/205 comments; formal proof plby/lean-proofs,
src/v4.29.1/ErdosProblems/Erdos205.lean, infinitely many n such that n - 2^k has ≫ (log n / log log
n)^{1/2} prime factors for every k with 2^k < n,
https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos205.lean.
-/
public theorem_wanted eventuallyRepresentableLogLog_refuted : ¬ eventuallyRepresentableLogLog

/--
Resolved false: the same `n` defeat `ε log log m` for every `ε > 0`, since `(log n / log log
n)^{1/2}` eventually exceeds `ε log log n ≥ ε log log m`. Source: T. F. Bloom, Erdős Problems,
Problem #205, https://www.erdosproblems.com/205 (status DISPROVED (LEAN)); resolution: K. Barreto
and Leeham (with ChatGPT and Aristotle), negative answer, quantified by T. Tao and B. Alexeev in the
erdosproblems.com/205 comments; formal proof plby/lean-proofs,
src/v4.29.1/ErdosProblems/Erdos205.lean, infinitely many n such that n - 2^k has ≫ (log n / log log
n)^{1/2} prime factors for every k with 2^k < n,
https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos205.lean.
-/
public theorem_wanted eventuallyRepresentableEpsLogLog_refuted : ¬ eventuallyRepresentableEpsLogLog

/--
Resolved false: for `g = o(log log m)` the same `n` are not representable: each `m = n - 2^k ≥ 1`
has `m ≥ 2^Ω(m)`, so `m → ∞` uniformly in `k`, and then `g(m) ≤ log log m < Ω(m)`. Source: T. F.
Bloom, Erdős Problems, Problem #205, https://www.erdosproblems.com/205 (status DISPROVED (LEAN));
resolution: K. Barreto and Leeham (with ChatGPT and Aristotle), negative answer, quantified by T.
Tao and B. Alexeev in the erdosproblems.com/205 comments; formal proof plby/lean-proofs,
src/v4.29.1/ErdosProblems/Erdos205.lean, infinitely many n such that n - 2^k has ≫ (log n / log log
n)^{1/2} prime factors for every k with 2^k < n,
https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos205.lean.
-/
public theorem_wanted eventuallyRepresentableSlowerFunction_refuted :
    ¬ eventuallyRepresentableSlowerFunction

end MathlibExt.NumberTheory.PowerOfTwoPlusFewPrimeFactorsErdosProblem205Wanted
