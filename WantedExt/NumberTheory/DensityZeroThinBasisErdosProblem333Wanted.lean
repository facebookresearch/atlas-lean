/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Thin bases for sets of density zero (Erdős Problem 333)

Erdős Problem 333: let `A ⊆ ℕ` have density zero. Is there `B` with `A ⊆ B + B` and `|B ∩ {1, …, N}|
= o(N^{1/2})`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.NumberTheory.DensityZeroThinBasisErdosProblem333Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #333, https://www.erdosproblems.com/333 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006827 (`EP-333`), dataset ulamai/UnsolvedMath v1.8.0.

Density zero is natural density zero. `B ⊆ ℕ` may contain `0`: with `B` restricted to positive
integers, `A = {1}` (never in `B + B`) would be a trivial counterexample. Compared with the
formal-conjectures statement `ErdosProblems/333.lean` (identical statement; no code imported).
-/

open Filter Topology Asymptotics
open scoped Pointwise

/-- Erdős Problem 333: every `A ⊆ ℕ` of natural density zero satisfies `A ⊆ B + B` for some
`B ⊆ ℕ` with `|B ∩ {1, …, N}| = o(N^{1/2})`. -/
def densityZeroHasThinBasis : Prop :=
  ∀ A : Set ℕ, Tendsto (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / N) atTop (𝓝 0) →
    ∃ B : Set ℕ, A ⊆ B + B ∧
      (fun N : ℕ => ((B ∩ Set.Icc 1 N).ncard : ℝ)) =o[atTop] fun N : ℕ => Real.sqrt N

/--
Resolved false: Theorem 2 of Erdős and Newman gives sets of density zero that are not contained in
`B + B` for any `B` with `|B ∩ [1, N]| = o(N^{1/2})`. erdosproblems.com/333 lists the problem as
disproved. Source: T. F. Bloom, Erdős Problems, Problem #333, https://www.erdosproblems.com/333
(status DISPROVED (LEAN)); resolution: P. Erdős and D. J. Newman, Bases for sets of integers, J.
Number Theory (1977), 420-425, erdosproblems.com/333: Theorem 2 of [ErNe77] implies a negative
answer (overlooked by Erdős and Graham); the squares do have such a B,
https://www.erdosproblems.com/333.
-/
public theorem_wanted densityZeroHasThinBasis_refuted : ¬ densityZeroHasThinBasis

end MathlibExt.NumberTheory.DensityZeroThinBasisErdosProblem333Wanted
