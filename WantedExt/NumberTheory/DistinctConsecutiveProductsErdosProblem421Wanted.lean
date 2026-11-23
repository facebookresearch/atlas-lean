/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Density-one sequences with distinct consecutive products (Erdős Problem 421)

Erdős Problem 421: is there a sequence `1 ≤ d₁ < d₂ < ⋯` with density `1` such that all products
`∏_{u ≤ i ≤ v} dᵢ` are distinct?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.DistinctConsecutiveProductsErdosProblem421Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #421, https://www.erdosproblems.com/421 (status
SOLVED). UnsolvedMath record UM-00002110 (`EP-421`), dataset ulamai/UnsolvedMath v1.8.0.

Density is the natural density of the set of terms (`Set.HasDensity`, MathlibExt); products over
distinct index intervals `u ≤ v` are distinct. Compared with the formal-conjectures statement
`ErdosProblems/421.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 421: there is a sequence `1 ≤ d₀ < d₁ < ⋯` of natural density `1` whose products
`d_u ⋯ d_v` (`u ≤ v`) of consecutive terms are pairwise distinct. -/
def densityOneDistinctConsecutiveProducts : Prop :=
  ∃ d : ℕ → ℕ, StrictMono d ∧ 1 ≤ d 0 ∧ (Set.range d).HasDensity 1 ∧
    ∀ u v u' v' : ℕ, u ≤ v → u' ≤ v' →
      ∏ i ∈ Finset.Icc u v, d i = ∏ i ∈ Finset.Icc u' v', d i → u = u' ∧ v = v'

/--
Resolved true: erdosproblems.com/421 records a positive answer, following an approach sketched by
Tao and developed by Chojecki, with full proofs obtained from GPT by several people and a simplified
exposition by Pratt; the formal-conjectures statement has a Lean proof. Source: T. F. Bloom, Erdős
Problems, Problem #421, https://www.erdosproblems.com/421 (status SOLVED); resolution: K. Pratt, A
proof of Erdős Problem 421, https://www.erdosproblems.com/static/421-Pratt.pdf, after an approach
sketched by T. Tao and developed by Chojecki; formal proof plby/lean-proofs,
src/latest/ErdosProblems/Erdos421.lean, yes (erdosproblems.com/421),
https://www.erdosproblems.com/static/421-Pratt.pdf.
-/
public theorem_wanted densityOneDistinctConsecutiveProducts_holds :
    densityOneDistinctConsecutiveProducts

end MathlibExt.NumberTheory.DistinctConsecutiveProductsErdosProblem421Wanted
