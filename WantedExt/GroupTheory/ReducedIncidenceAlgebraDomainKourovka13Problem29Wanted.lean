/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The invariant reduced incidence algebra is a domain (Kourovka Notebook Problem 13.29)

Kourovka Notebook, Archive of Solved Problems, Problem 13.29 (P. J. Cameron): for an infinite set
`Ω` let `A = ⨁ Vₙ`, `Vₙ` the functions from `n`-subsets of `Ω` to `ℚ`, with `(fg)(X) = ∑ f(Y) g(X ∖
Y)` over the `n`-subsets `Y` of `X` (`f ∈ Vₙ`, `g ∈ Vₘ`, `|X| = n + m`). Conjecture: if a
permutation group `G` on `Ω` has no finite orbits, then the algebra `A^G` of `G`-invariants is an
integral domain.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Finset.Powerset
public import Mathlib.GroupTheory.GroupAction.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.ReducedIncidenceAlgebraDomainKourovka13Problem29Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.29 (P. J.
Cameron). UnsolvedMath record UM-00700947 (`KOU-13.29`), dataset ulamai/UnsolvedMath v1.8.0.

Elements of `A` are functions on finite subsets vanishing above some size, and the product `(fg)(X)
= ∑_{Y ⊆ X} f(Y) g(X ∖ Y)` restricts to the problem's product on `Vₙ × Vₘ` and extends it
bilinearly. `A^G` consists of the `G`-invariant elements. Being an integral domain is stated as the
absence of zero divisors in `A^G` (the unit of `V₀` is nonzero). The definitions agree with
`OpenConjectures` entry `Kourovka19Problem18`.
-/

variable {Ω : Type*} [DecidableEq Ω]

/-- **Product of the reduced incidence algebra.** Let $\Omega$ be a set. For functions $f$ and $g$
from the finite subsets of $\Omega$ to $\mathbb{Q}$, their product $fg$ is the function on finite
subsets given by $(fg)(X) = \sum_{Y \subseteq X} f(Y)\, g(X \setminus Y)$.

If $f$ vanishes off the $n$-element subsets and $g$ vanishes off the $m$-element subsets, this is
the product of Kourovka Problem 13.29, and $fg$ vanishes off the $(n+m)$-element subsets. -/
def incMul (f g : Finset Ω → ℚ) : Finset Ω → ℚ :=
  fun X => ∑ Y ∈ X.powerset, f Y * g (X \ Y)

/-- **Elements of the reduced incidence algebra.** Let $\Omega$ be a set. A function $f$ from the
finite subsets of $\Omega$ to $\mathbb{Q}$ lies in the algebra $A = \bigoplus_n V_n$, where $V_n$
consists of the functions vanishing off the $n$-element subsets, when there is a natural number
$N$ such that $f(X) = 0$ for every finite subset $X$ of $\Omega$ with more than $N$ elements. -/
def IsInA (f : Finset Ω → ℚ) : Prop :=
  ∃ N : ℕ, ∀ X : Finset Ω, N < X.card → f X = 0

/-- **Invariant functions on finite subsets.** Let $G$ be a group of permutations of a set
$\Omega$. A function $f$ from the finite subsets of $\Omega$ to $\mathbb{Q}$ is $G$-invariant when
$f(\sigma(X)) = f(X)$ for every $\sigma \in G$ and every finite subset $X$ of $\Omega$, where
$\sigma(X)$ is the image of $X$ under $\sigma$. -/
def IsInvariant (G : Subgroup (Equiv.Perm Ω)) (f : Finset Ω → ℚ) : Prop :=
  ∀ σ ∈ G, ∀ X : Finset Ω, f (X.map σ.toEmbedding) = f X

/-- **Cameron's conjecture on invariant incidence algebras (Kourovka 13.29).** The statement that
for every infinite set $\Omega$ and every group $G$ of permutations of $\Omega$ all of whose orbits
are infinite, the following holds: if $f$ and $g$ are nonzero functions from the finite subsets of
$\Omega$ to $\mathbb{Q}$ that are $G$-invariant ($f(\sigma(X)) = f(X)$ for all $\sigma \in G$ and
all finite $X$, and likewise for $g$) and that each vanish on all subsets of size larger than some
bound, then their product $fg$ in the reduced incidence algebra, given by
$(fg)(X) = \sum_{Y \subseteq X} f(Y)\, g(X \setminus Y)$, is not identically zero. In other words,
the algebra $A^G$ of $G$-invariant elements of the reduced incidence algebra $A$ has no zero
divisors. -/
def invariantIncidenceAlgebraIsDomain : Prop :=
  ∀ (Ω : Type) [DecidableEq Ω] [Infinite Ω] (G : Subgroup (Equiv.Perm Ω)),
    (∀ x : Ω, (MulAction.orbit G x).Infinite) →
    ∀ f g : Finset Ω → ℚ, IsInA f → IsInvariant G f → IsInA g → IsInvariant G g →
      f ≠ 0 → g ≠ 0 → incMul f g ≠ 0

/--
**Cameron's conjecture on invariant incidence algebras holds (Pouzet).** Let $\Omega$ be an
infinite set and let $G$ be a group of permutations of $\Omega$ all of whose orbits are infinite.
Let $f$ and $g$ be nonzero functions from the finite subsets of $\Omega$ to $\mathbb{Q}$ that are
$G$-invariant ($f(\sigma(X)) = f(X)$ for all $\sigma \in G$ and all finite $X$, and likewise for
$g$) and that each vanish on all subsets of size larger than some bound. Then their product in the
reduced incidence algebra, $(fg)(X) = \sum_{Y \subseteq X} f(Y)\, g(X \setminus Y)$, is not
identically zero. In other words, the algebra $A^G$ of $G$-invariant elements of the reduced
incidence algebra $A$ has no zero divisors.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 13.29 (P. J. Cameron); resolution: M. Pouzet, Theor. Inform. Appl. 42 (2008), no. 1, 83-103,
Kourovka Archive, Problem 13.29: the conjecture is proved.
-/
public theorem_wanted invariantIncidenceAlgebraIsDomain_holds : invariantIncidenceAlgebraIsDomain

end MathlibExt.GroupTheory.ReducedIncidenceAlgebraDomainKourovka13Problem29Wanted
