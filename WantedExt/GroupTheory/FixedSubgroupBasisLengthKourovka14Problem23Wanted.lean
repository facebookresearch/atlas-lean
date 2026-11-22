/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Short bases of fixed subgroups of free group automorphisms (Kourovka Notebook Problem 14.23)

Kourovka Notebook, Problem 14.23 (O. V. Bogopolski): with `‖α‖ = max |α(xᵢ)|` for `α ∈ Aut F_n`, is
there a recursive function `f : ℕ → ℕ` such that `Fix(α)` always has a basis `y₁, …, y_k` with `|yᵢ|
≤ f(‖α‖)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Computability.Partrec
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.GroupTheory.FixedSubgroupBasisLengthKourovka14Problem23Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.23 (O. V. Bogopolski). UnsolvedMath
record UM-00701008 (`KOU-14.23`), dataset ulamai/UnsolvedMath v1.8.0.

The notebook distinguishes two quantifier orders, one target each: (a) `f` may depend on the rank
`n`; (b) one `f` works for all ranks. Recursive is `Computable`; `|·|` is the reduced word length
(`FreeGroup.norm`) in the basis `x₀, …, xₙ₋₁`; a basis of `Fix(α)` is a `FreeGroupBasis` of the
subgroup, of any finite size.
-/

/-- The norm `‖α‖ = max (|α(x₀)|, …, |α(xₙ₋₁)|)` of an automorphism `α` of `F_n`, where `|·|` is the
reduced word length in the basis `x₀, …, xₙ₋₁`. -/
def autNorm {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : ℕ :=
  Finset.univ.sup fun i => (α (FreeGroup.of i)).norm

/-- The fixed subgroup `Fix(α) = {x | α x = x}`. -/
def fixedSubgroup {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : Subgroup (FreeGroup (Fin n)) :=
  (α : FreeGroup (Fin n) →* FreeGroup (Fin n)).eqLocus (MonoidHom.id _)

/-- `Fix(α)` has a free basis all of whose elements have length at most `L`. -/
def HasShortFixedBasis {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (L : ℕ) : Prop :=
  ∃ (k : ℕ) (b : FreeGroupBasis (Fin k) (fixedSubgroup α)),
    ∀ i, ((b i : fixedSubgroup α) : FreeGroup (Fin n)).norm ≤ L

/-- Kourovka 14.23 (O. V. Bogopolski), for each fixed rank: for every `n` there is a recursive
function `f : ℕ → ℕ` such that for every `α ∈ Aut F_n` the subgroup `Fix(α)` has a free basis of
elements of length at most `f(‖α‖)`. -/
def fixedSubgroupBasisRecursiveBoundEachRank : Prop :=
  ∀ n : ℕ, ∃ f : ℕ → ℕ, Computable f ∧
    ∀ α : MulAut (FreeGroup (Fin n)), HasShortFixedBasis α (f (autNorm α))

/-- Kourovka 14.23 (O. V. Bogopolski), uniformly in the rank: one recursive function
`f : ℕ → ℕ` works for every `n` and every `α ∈ Aut F_n`. -/
def fixedSubgroupBasisRecursiveBoundUniform : Prop :=
  ∃ f : ℕ → ℕ, Computable f ∧
    ∀ (n : ℕ) (α : MulAut (FreeGroup (Fin n))), HasShortFixedBasis α (f (autNorm α))

/--
Resolved true: for each fixed rank such a recursive function exists, as a consequence of the
algorithm computing a basis of `Fix(α)` (Kharlampovich, Proposition 2); the Kourovka Notebook (21st
issue) records this answer. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.23 (O. V.
Bogopolski); resolution: O. Kharlampovich, Two observations on Problems 14.23 and 17.32 of the
Kourovka Notebook, preprint (2026), Proposition 2 (each rank); O. Kharlampovich, A counterexample to
the rank-uniform form of Kourovka Notebook Problem 14.23, preprint (2026), Theorem 1, the Kourovka
Notebook (21st issue) marks 14.23 solved: true for each given rank, false if one function must work
for all ranks,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/08/kourovka_14_23_uniform_counterexample.pdf.
-/
public theorem_wanted fixedSubgroupBasisRecursiveBoundEachRank_holds :
    fixedSubgroupBasisRecursiveBoundEachRank

/--
Resolved false: for every `r ≥ 3` there is an automorphism `α_r` of the free group of rank `2r - 1`
with `‖α_r‖ = 3` such that every generating set of `Fix(α_r)` contains an element of length at least
`r` (Kharlampovich, Theorem 1), so no function at all, recursive or not, works for all ranks; the
Kourovka Notebook (21st issue) records this answer. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 14.23 (O. V. Bogopolski); resolution: O. Kharlampovich, Two observations on Problems 14.23
and 17.32 of the Kourovka Notebook, preprint (2026), Proposition 2 (each rank); O. Kharlampovich, A
counterexample to the rank-uniform form of Kourovka Notebook Problem 14.23, preprint (2026), Theorem
1, the Kourovka Notebook (21st issue) marks 14.23 solved: true for each given rank, false if one
function must work for all ranks,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/08/kourovka_14_23_uniform_counterexample.pdf.
-/
public theorem_wanted fixedSubgroupBasisRecursiveBoundUniform_refuted :
    ¬ fixedSubgroupBasisRecursiveBoundUniform

end MathlibExt.GroupTheory.FixedSubgroupBasisLengthKourovka14Problem23Wanted
