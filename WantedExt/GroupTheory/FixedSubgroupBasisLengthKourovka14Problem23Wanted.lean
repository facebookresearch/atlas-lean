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

/-- **Norm of an automorphism of a free group.** Let $F_n$ be the free group on the basis
$x_0, \dots, x_{n-1}$, and for $w \in F_n$ let $|w|$ be the length of the reduced word
representing $w$. The norm of an automorphism $\alpha$ of $F_n$ is
$\|\alpha\| = \max(|\alpha(x_0)|, \dots, |\alpha(x_{n-1})|)$, taken to be $0$ when $n = 0$. -/
def autNorm {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : ℕ :=
  Finset.univ.sup fun i => (α (FreeGroup.of i)).norm

/-- **Fixed subgroup of a free group automorphism.** For an automorphism $\alpha$ of the free
group $F_n$ on $x_0, \dots, x_{n-1}$, the fixed subgroup of $\alpha$ is the subgroup
$\mathrm{Fix}(\alpha) = \{x \in F_n \mid \alpha(x) = x\}$ of $F_n$. -/
def fixedSubgroup {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : Subgroup (FreeGroup (Fin n)) :=
  (α : FreeGroup (Fin n) →* FreeGroup (Fin n)).eqLocus (MonoidHom.id _)

/-- **Fixed subgroups with a short free basis.** Let $\alpha$ be an automorphism of the free group
$F_n$ on $x_0, \dots, x_{n-1}$, let $|w|$ be the length of the reduced word representing
$w \in F_n$, and let $L$ be a natural number. The fixed subgroup $\mathrm{Fix}(\alpha)$ has a
short free basis with bound $L$ when, for some $k \ge 0$, it has a free basis
$y_1, \dots, y_k$ with $|y_i| \le L$ for every $i$. -/
def HasShortFixedBasis {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (L : ℕ) : Prop :=
  ∃ (k : ℕ) (b : FreeGroupBasis (Fin k) (fixedSubgroup α)),
    ∀ i, ((b i : fixedSubgroup α) : FreeGroup (Fin n)).norm ≤ L

/-- **Kourovka Problem 14.23, rank-dependent form.** For every $n$ there is a computable
function $f : \mathbb{N} \to \mathbb{N}$ such that for every automorphism $\alpha$ of the free
group $F_n$ on $x_0, \dots, x_{n-1}$, the fixed subgroup $\mathrm{Fix}(\alpha)$ has a finite
free basis all of whose elements have reduced word length at most $f(\|\alpha\|)$, where
$\|\alpha\|$ is the maximum of the reduced word lengths of $\alpha(x_0), \dots, \alpha(x_{n-1})$.

This is the form of Kourovka Notebook Problem 14.23 (O. V. Bogopolski) in which $f$ may depend
on the rank $n$. -/
def fixedSubgroupBasisRecursiveBoundEachRank : Prop :=
  ∀ n : ℕ, ∃ f : ℕ → ℕ, Computable f ∧
    ∀ α : MulAut (FreeGroup (Fin n)), HasShortFixedBasis α (f (autNorm α))

/-- **Kourovka Problem 14.23, rank-uniform form.** There is a computable function
$f : \mathbb{N} \to \mathbb{N}$ such that for every $n$ and every automorphism $\alpha$ of the
free group $F_n$ on $x_0, \dots, x_{n-1}$, the fixed subgroup $\mathrm{Fix}(\alpha)$ has a
finite free basis all of whose elements have reduced word length at most $f(\|\alpha\|)$, where
$\|\alpha\|$ is the maximum of the reduced word lengths of $\alpha(x_0), \dots, \alpha(x_{n-1})$.

This is the form of Kourovka Notebook Problem 14.23 (O. V. Bogopolski) in which one $f$ must
work for all ranks $n$. -/
def fixedSubgroupBasisRecursiveBoundUniform : Prop :=
  ∃ f : ℕ → ℕ, Computable f ∧
    ∀ (n : ℕ) (α : MulAut (FreeGroup (Fin n))), HasShortFixedBasis α (f (autNorm α))

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

/--
**Kourovka Problem 14.23 fails uniformly in the rank.** There is no computable function
$f : \mathbb{N} \to \mathbb{N}$ such that for every $n$ and every automorphism $\alpha$ of the
free group $F_n$ on $x_0, \dots, x_{n-1}$, the fixed subgroup $\mathrm{Fix}(\alpha)$ has a
finite free basis all of whose elements have reduced word length at most $f(\|\alpha\|)$, where
$\|\alpha\|$ is the maximum of the reduced word lengths of $\alpha(x_0), \dots, \alpha(x_{n-1})$.

Kharlampovich (Theorem 1) proves more: for every $r \ge 3$ there is an automorphism $\alpha_r$
of the free group of rank $2r - 1$ with $\|\alpha_r\| = 3$ such that every generating set of
$\mathrm{Fix}(\alpha_r)$ contains an element of length at least $r$, so no function at all,
computable or not, works for all ranks; the Kourovka Notebook (21st issue) records this answer.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
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
