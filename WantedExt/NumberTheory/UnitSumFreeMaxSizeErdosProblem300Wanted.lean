/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Largest unit-sum-free subsets of `{1, …, N}` (Erdős Problem 300)

Erdős Problem 300: let `A(N)` be the largest size of `A ⊆ {1, …, N}` with `∑_{n ∈ S} 1/n ≠ 1` for
all `S ⊆ A`. Estimate `A(N)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

namespace MathlibExt.NumberTheory.UnitSumFreeMaxSizeErdosProblem300Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #300, https://www.erdosproblems.com/300 (status SOLVED
(LEAN)). UnsolvedMath record UM-30006815 (`EP-300`), dataset ulamai/UnsolvedMath v1.8.0.

The estimate is the asymptotic `A(N) = (1 - 1/e + o(1)) N` recorded as the solution. Compared with
the formal-conjectures statement `ErdosProblems/300.lean` (identical statement; no code imported).
-/

open Filter Topology

/-- `A(N)`: the largest size of `A ⊆ {1, …, N}` with `∑_{n ∈ S} 1/n ≠ 1` for every `S ⊆ A`. -/
noncomputable def maxUnitSumFreeSize (N : ℕ) : ℕ :=
  sSup {m | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = m ∧ ∀ S ⊆ A, ∑ n ∈ S, (1 : ℚ) / n ≠ 1}

/-- Erdős Problem 300: `A(N) = (1 - 1/e + o(1)) N`. -/
def maxUnitSumFreeSizeAsymptotic : Prop :=
  Tendsto (fun N : ℕ => (maxUnitSumFreeSize N : ℝ) / N) atTop (𝓝 (1 - 1 / Real.exp 1))

/--
Resolved true: Liu and Sawhney proved `A(N) = (1 - 1/e + o(1)) N`, disproving the Erdős-Graham guess
`A(N) = (1 + o(1)) N` (already refuted by Croot). erdosproblems.com/300 lists the problem as solved.
Source: T. F. Bloom, Erdős Problems, Problem #300, https://www.erdosproblems.com/300 (status SOLVED
(LEAN)); resolution: Y. P. Liu and M. Sawhney, On further questions regarding unit fractions,
arXiv:2404.07113 (2024), Theorem 1.3 (for N large, every A ⊆ [1, N] with |A| ≥ (1 - 1/e + ε)N has a
subset with reciprocal sum 1) and the sharpness remark after it; erdosproblems.com/300: Liu and
Sawhney proved A(N) = (1 - 1/e + o(1)) N (the lower bound is trivial; Croot, Ann. of Math. (2003),
545-556, had shown A(N) < cN for some c < 1), https://arxiv.org/abs/2404.07113.
-/
public theorem_wanted maxUnitSumFreeSizeAsymptotic_holds : maxUnitSumFreeSizeAsymptotic

end MathlibExt.NumberTheory.UnitSumFreeMaxSizeErdosProblem300Wanted
