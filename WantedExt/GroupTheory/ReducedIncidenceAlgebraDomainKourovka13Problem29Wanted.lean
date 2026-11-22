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

/-- The product of the reduced incidence algebra on functions `Finset Ω → ℚ`:
`(fg)(X) = ∑_{Y ⊆ X} f(Y) g(X ∖ Y)`. For `f ∈ Vₙ`, `g ∈ Vₘ` (vanishing off `n`- resp. `m`-subsets)
this is the product of the problem, landing in `V_{n+m}`. -/
def incMul (f g : Finset Ω → ℚ) : Finset Ω → ℚ :=
  fun X => ∑ Y ∈ X.powerset, f Y * g (X \ Y)

/-- `f` lies in `A = ⨁ₙ Vₙ`: it vanishes on all finite subsets of size larger than some `N`. -/
def IsInA (f : Finset Ω → ℚ) : Prop :=
  ∃ N : ℕ, ∀ X : Finset Ω, N < X.card → f X = 0

/-- `f` is invariant under the permutation group `G`. -/
def IsInvariant (G : Subgroup (Equiv.Perm Ω)) (f : Finset Ω → ℚ) : Prop :=
  ∀ σ ∈ G, ∀ X : Finset Ω, f (X.map σ.toEmbedding) = f X

/-- Kourovka 13.29 (P. J. Cameron): if a permutation group `G` on an infinite set `Ω` has no
finite orbits, then the algebra `A^G` of `G`-invariants of the reduced incidence algebra of finite
subsets of `Ω` is an integral domain (it has no zero divisors). -/
def invariantIncidenceAlgebraIsDomain : Prop :=
  ∀ (Ω : Type) [DecidableEq Ω] [Infinite Ω] (G : Subgroup (Equiv.Perm Ω)),
    (∀ x : Ω, (MulAction.orbit G x).Infinite) →
    ∀ f g : Finset Ω → ℚ, IsInA f → IsInvariant G f → IsInA g → IsInvariant G g →
      f ≠ 0 → g ≠ 0 → incMul f g ≠ 0

/--
Resolved true: the Kourovka Archive records Cameron's conjecture as proved by M. Pouzet (Theor.
Inform. Appl. 42 (2008)). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 13.29 (P. J. Cameron); resolution: M. Pouzet, Theor. Inform. Appl. 42 (2008), no. 1, 83-103,
Kourovka Archive, Problem 13.29: the conjecture is proved.
-/
public theorem_wanted invariantIncidenceAlgebraIsDomain_holds : invariantIncidenceAlgebraIsDomain

end MathlibExt.GroupTheory.ReducedIncidenceAlgebraDomainKourovka13Problem29Wanted
