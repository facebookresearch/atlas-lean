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
public import MathlibExt.GroupTheory.FixedSubgroupBasisLengthKourovka14Problem23

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

/--
**Kourovka Problem 14.23 holds for each rank.** For every $n$ there is a computable function
$f : \mathbb{N} \to \mathbb{N}$ such that for every automorphism $\alpha$ of the free group $F_n$
on $x_0, \dots, x_{n-1}$, the fixed subgroup $\mathrm{Fix}(\alpha)$ has a finite free basis all
of whose elements have reduced word length at most $f(\|\alpha\|)$, where $\|\alpha\|$ is the
maximum of the reduced word lengths of $\alpha(x_0), \dots, \alpha(x_{n-1})$.

This follows from the algorithm computing a basis of $\mathrm{Fix}(\alpha)$ (Kharlampovich,
Proposition 2); the Kourovka Notebook (21st issue) records this answer.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
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

end MathlibExt.GroupTheory.FixedSubgroupBasisLengthKourovka14Problem23Wanted
