/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdos Problem #351: strong completeness of polynomial shifts
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Batteries.Util.ProofWanted

open scoped BigOperators

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem351Wanted

/-! Source record `EP-351`. -/

namespace EP351

/-!
# Clause inventory for [EP-351] Erdős Problem #351

- `p ∈ ℚ[x]`: rational polynomial domain.
- `p` has positive leading coefficient (`0 < p.leadingCoeff`).
- `n ∈ ℕ` with `n ≠ 0` so that `1 / n` is defined.
- `A = { p(n) + 1 / n : n ∈ ℕ }`.
- `B` ranges over finite sets.
- `X` ranges over finite subsets of `A \ B`.
- The set of finite subset-sums of `A \ B` contains every sufficiently
  large integer.
-/

/-- Strong completeness from [EP-351]: `A` is strongly complete when, for every
finite set `B`, the finite subset-sums of `A \ B` contain all sufficiently
large integers. -/
def StronglyComplete (A : Set ℚ) : Prop :=
  ∀ B : Set ℚ, B.Finite →
    ∃ N₀ : ℤ, ∀ m : ℤ, N₀ ≤ m →
      (m : ℚ) ∈ { s : ℚ | ∃ X : Finset ℚ, (↑X : Set ℚ) ⊆ A \ B ∧ ∑ a ∈ X, a = s }

/-- The set `A = { p(n) + 1 / n : n ∈ ℕ }` from [EP-351], for `p ∈ ℚ[x]`. -/
def ErdosSet351 (p : Polynomial ℚ) : Set ℚ :=
  { q : ℚ | ∃ n : ℕ, n ≠ 0 ∧ q = p.eval (n : ℚ) + 1 / (n : ℚ) }

/-- The question of [EP-351] Erdős Problem #351 as a proposition: is
`A = { p(n) + 1 / n }` strongly complete for every `p ∈ ℚ[x]` with
positive leading coefficient? -/
def StrongCompletenessQuestion : Prop :=
  ∀ p : Polynomial ℚ, 0 < p.leadingCoeff → StronglyComplete (ErdosSet351 p)

end EP351

/--
Resolved true: The maintained Erdős Problems page marks Problem 351 proved in the affirmative
and records that the positive solution follows from the positive solution of Problem 283.
Source: plby/lean-proofs, src/latest/Util/PolynomialEgyptianSums.lean (theorem
corollary_7_pos_leading, used by src/latest/ErdosProblems/Erdos351.lean), pinned revision
8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Util/PolynomialEgyptianSums.lean#L10266.
Moved from `OpenConjectures/NumberTheory/ErdosProblem351`.
-/
public theorem_wanted StrongCompletenessQuestion_holds : EP351.StrongCompletenessQuestion

end MathlibExt.NumberTheory.ErdosProblem351Wanted
