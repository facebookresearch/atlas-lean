/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A partition relation for sums of increasing powers of two (Erdős Problem 1219)

Erdős Problem 1219: let `(nₖ)` be an increasing sequence of integers such that `2^{ℵ_{nₖ}}` is
strictly increasing and `2^{ℵ_{n₀}} > ℵ_ω`. Is it true that `∑ₖ 2^{ℵ_{nₖ}} → (ℵ_ω)²`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

namespace MathlibExt.Combinatorics.AlephOmegaPartitionSumErdosProblem1219Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1219, https://www.erdosproblems.com/1219 (status
PROVED). UnsolvedMath record UM-30007260 (`EP-1219`), dataset ulamai/UnsolvedMath v1.8.0.

The arrow is the Erdős-Rado partition relation for pairs with two colours: every symmetric
two-colouring of the pairs of a set of cardinality `∑ₖ 2^{ℵ_{nₖ}}` (a cardinal sum) has a
homogeneous set of cardinality `ℵ_ω`. Cardinals are in `Cardinal.{0}`. Compared with the
formal-conjectures statement `ErdosProblems/1219.lean` (equivalent; no code imported).
-/

open Cardinal

/-- The partition relation `κ → (μ)²₂`: for every type `α` of cardinality `κ` and every symmetric
`2`-colouring `c` of pairs of elements of `α`, some `H ⊆ α` of cardinality `μ` has all pairs of
distinct elements of the same colour. -/
def ArrowsPairs (κ μ : Cardinal.{0}) : Prop :=
  ∀ (α : Type), #α = κ → ∀ c : α → α → Bool, (∀ x y, c x y = c y x) →
    ∃ H : Set α, #H = μ ∧ ∃ b : Bool, ∀ x ∈ H, ∀ y ∈ H, x ≠ y → c x y = b

/-- Erdős Problem 1219: if `n₀ < n₁ < ⋯`, the cardinals `2^{ℵ_{nₖ}}` are strictly increasing and
`2^{ℵ_{n₀}} > ℵ_ω`, then `∑ₖ 2^{ℵ_{nₖ}} → (ℵ_ω)²₂`. -/
def alephOmegaPartitionOfCardinalSum : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n → StrictMono (fun k => (2 : Cardinal.{0}) ^ ℵ_ (n k)) →
    ℵ_ Ordinal.omega0 < (2 : Cardinal.{0}) ^ ℵ_ (n 0) →
      ArrowsPairs (Cardinal.sum fun k : ℕ => (2 : Cardinal.{0}) ^ ℵ_ (n k)) (ℵ_ Ordinal.omega0)

/--
Resolved true: Shelah proved the partition relation `∑ₖ 2^{ℵ_{nₖ}} → (ℵ_ω)²` under these hypotheses
(Erdős, Hajnal and Rado had noted the answer yes for `ℵ_κ`, `κ < ω`, and no for `κ > ω`);
erdosproblems.com/1219 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#1219, https://www.erdosproblems.com/1219 (status PROVED); resolution: S. Shelah, Notes on partition
calculus, in Infinite and Finite Sets (Colloq. Keszthely, 1973), Colloq. Math. Soc. János Bolyai 10,
North-Holland (1975), 1257-1276, erdosproblems.com/1219: proved by Shelah (a problem of Erdős,
Hajnal and Rado; P. Komjáth, The Erdős-Hajnal problem list, Bull. Symb. Log. (2025), p. 2).
-/
public theorem_wanted alephOmegaPartitionOfCardinalSum_holds : alephOmegaPartitionOfCardinalSum

end MathlibExt.Combinatorics.AlephOmegaPartitionSumErdosProblem1219Wanted
