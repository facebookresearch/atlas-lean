/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small overshoots of harmonic blocks over `1` (Erdős Problem 314)

Erdős Problem 314: for `n ≥ 1` let `m` be minimal with `∑_{n ≤ k ≤ m} 1/k ≥ 1` and `ε(n) = ∑_{n ≤ k
≤ m} 1/k - 1`. How small can `ε(n)` be? Is `liminf n² ε(n) = 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.HarmonicBlockOvershootErdosProblem314Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #314, https://www.erdosproblems.com/314 (status PROVED
(LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980), p. 41. UnsolvedMath record UM-30006822 (`EP-314`), dataset ulamai/UnsolvedMath v1.8.0.

"How small" is open-ended; the liminf question is stated. As `ε(n) ≥ 0`, `liminf n² ε(n) = 0` is
stated as: for every `δ > 0`, `n² ε(n) < δ` for infinitely many `n` (this avoids `liminf` junk
values). Compared with the formal-conjectures statement `ErdosProblems/314.lean` (equivalent; no
code imported).
-/

open Filter

/-- `∑_{n ≤ k ≤ m} 1/k` as a rational number. -/
def harmonicBlock (n m : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc n m, (1 : ℚ) / k

/-- The least `m` with `∑_{n ≤ k ≤ m} 1/k ≥ 1` (it exists for `n ≥ 1`). -/
noncomputable def leastBlockEnd (n : ℕ) : ℕ :=
  sInf {m | 1 ≤ harmonicBlock n m}

/-- `ε(n) = ∑_{n ≤ k ≤ m} 1/k - 1` for that least `m` (so `ε(n) ≥ 0` for `n ≥ 1`). -/
noncomputable def blockOvershoot (n : ℕ) : ℚ :=
  harmonicBlock n (leastBlockEnd n) - 1

/-- Erdős Problem 314: `liminf_n n² ε(n) = 0`, stated as: for every `δ > 0` infinitely many `n`
have `n² ε(n) < δ`. -/
def liminfSquaredOvershootZero : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 * blockOvershoot n < δ

/--
Resolved true: Lim and Steinerberger (Theorem 1) proved that for every `c > 0` there are infinitely
many `(m, n)` with `1 ≤ ∑_{ℓ = n}^{m} 1/ℓ ≤ 1 + c/n²`, hence `ε(n) ≤ c/n²` for those `n`.
erdosproblems.com/314 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#314, https://www.erdosproblems.com/314 (status PROVED (LEAN)); P. Erdős and R. L. Graham, Old and
new problems and results in combinatorial number theory (1980), p. 41; resolution: J. Lim and S.
Steinerberger, On differences of two harmonic numbers, arXiv:2405.11354 (2024), Theorem 1: for any c
> 0 there are infinitely many (m, n) with 1 ≤ ∑_{ℓ=n}^{m} 1/ℓ ≤ 1 + c/n²,
https://arxiv.org/abs/2405.11354.
-/
public theorem_wanted liminfSquaredOvershootZero_holds : liminfSquaredOvershootZero

end MathlibExt.NumberTheory.HarmonicBlockOvershootErdosProblem314Wanted
