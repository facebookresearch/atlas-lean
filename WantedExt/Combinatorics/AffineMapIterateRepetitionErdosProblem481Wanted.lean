/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Repetitions under iterated affine expansion (Erdős Problem 481)

Erdős Problem 481: for `a₁, …, a_r, b₁, …, b_r ∈ ℕ` with `∑ 1/aᵢ > 1`, let `T(x₁, …, xₙ) = (aᵢ xⱼ +
bᵢ)_{i, j}`. Starting from `A₁ = (1)` with `A_{k+1} = T(A_k)`, must some `A_k` have a repeated
entry?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.AffineMapIterateRepetitionErdosProblem481Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #481, https://www.erdosproblems.com/481 (status PROVED
(LEAN)). UnsolvedMath record UM-30006892 (`EP-481`), dataset ulamai/UnsolvedMath v1.8.0.

`∑ 1/aᵢ > 1` presupposes `aᵢ ≥ 1`. Sequences are lists of natural numbers (all entries stay in `ℕ`),
`A_k = T^[k - 1] (1)`; the order of entries in `T(A)` does not affect repetitions. Compared with the
formal-conjectures statement `ErdosProblems/481.lean` (equivalent; no code imported).
-/

/-- `T(A)`: the sequence `(a i * x + b i)` over `i < r` and the entries `x` of `A`, listed block by
block (the order does not affect whether an entry repeats). -/
def affineExpand {r : ℕ} (a b : Fin r → ℕ) (A : List ℕ) : List ℕ :=
  (List.finRange r).flatMap fun i => A.map fun x => a i * x + b i

/-- Erdős Problem 481: if `a, b : Fin r → ℕ` with every `a i ≥ 1` and `∑ 1 / a i > 1`, then
starting from `A₁ = (1)` some iterate `A_k = T^[k - 1] (1)` has a repeated entry. -/
def affineIterateHasRepetition : Prop :=
  ∀ (r : ℕ) (a b : Fin r → ℕ), (∀ i, 0 < a i) → 1 < ∑ i, (1 : ℝ) / a i →
    ∃ k : ℕ, ¬ ((affineExpand a b)^[k] [1]).Nodup

/--
Resolved true: erdosproblems.com/481 records that some `A_k` must repeat an entry, first shown by
Klarner, with a generalization by Kolpakov and Talambutsa. Source: T. F. Bloom, Erdős Problems,
Problem #481, https://www.erdosproblems.com/481 (status PROVED (LEAN)); resolution: D. A. Klarner, A
sufficient condition for certain semigroups to be free, J. Algebra (1982), 140-148; A. Kolpakov and
A. Talambutsa, On free semigroups of affine maps on the real line, Proc. Amer. Math. Soc. (2022),
2301-2307, erdosproblems.com/481: true, first shown by Klarner; generalized by Kolpakov and
Talambutsa, https://www.erdosproblems.com/481.
-/
public theorem_wanted affineIterateHasRepetition_holds : affineIterateHasRepetition

end MathlibExt.Combinatorics.AffineMapIterateRepetitionErdosProblem481Wanted
