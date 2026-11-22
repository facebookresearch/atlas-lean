/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dimension of first cohomology of absolutely irreducible modules (Kourovka Notebook Problem 16.55)

Kourovka Notebook, Archive of Solved Problems, Problem 16.55 (V. D. Mazurov): (well-known problem)
let `V` be a faithful absolutely irreducible module for a finite group `G`. Is it true that `dim
H¹(G, V) ≤ 2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

@[expose] public section

namespace MathlibExt.GroupTheory.FirstCohomologyDimensionKourovka16Problem55Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.55 (V. D.
Mazurov). UnsolvedMath record UM-00701247 (`KOU-16.55`), dataset ulamai/UnsolvedMath v1.8.0.

`V` is a finite-dimensional representation `ρ` of `G` over an arbitrary field `k`; faithful means
that `ρ` is injective, and absolutely irreducible is stated as irreducible with only scalar
`G`-endomorphisms, which for finite-dimensional modules is equivalent to irreducibility over an
algebraic closure. `H¹(G, V)` is Mathlib's `groupCohomology.H1 (Rep.of ρ)` and `dim` is
`Module.finrank k`.
-/

/-- **Absolutely irreducible representations.** A representation $\rho$ of a group $G$ on a vector
space $V$ over a field $k$ is absolutely irreducible when $V \neq 0$, the only $G$-invariant
subspaces of $V$ are $0$ and $V$, and every $k$-linear endomorphism of $V$ commuting with
$\rho(g)$ for all $g \in G$ is a scalar multiple of the identity.

For a finite-dimensional irreducible module this is equivalent to irreducibility over an algebraic
closure of $k$. -/
def IsAbsolutelyIrreducible {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Prop :=
  Nontrivial V ∧ (∀ W : Submodule k V, (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
    ∀ φ : V →ₗ[k] V, (∀ g : G, φ ∘ₗ ρ g = ρ g ∘ₗ φ) → ∃ c : k, φ = c • LinearMap.id

/-- **Mazurov's question on first cohomology (Kourovka 16.55).** The proposition that for every
field $k$, every finite group $G$ and every faithful absolutely irreducible representation $\rho$
of $G$ on a finite-dimensional $k$-vector space $V$, the first cohomology group $H^1(G, V)$ has
dimension at most $2$ over $k$. -/
def firstCohomologyDimAtMostTwo : Prop :=
  ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V), Function.Injective ρ →
    IsAbsolutelyIrreducible ρ → Module.finrank k (groupCohomology.H1 (Rep.of ρ)) ≤ 2

/--
**Mazurov's question on first cohomology (Kourovka 16.55) has a negative answer.** There exist a
field $k$, a finite group $G$ and a faithful absolutely irreducible representation of $G$ on a
finite-dimensional $k$-vector space $V$ such that the first cohomology group $H^1(G, V)$ has
dimension greater than $2$ over $k$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 16.55 (V. D. Mazurov); resolution: L. L. Scott, J. Algebra 260 (2003),
416-425; J. N. Bray and R. A. Wilson, J. Group Theory 11 (2008), 669-673, Kourovka Archive, Problem
16.55 (No, it is not).
-/
public theorem_wanted firstCohomologyDimAtMostTwo_refuted : ¬ firstCohomologyDimAtMostTwo

end MathlibExt.GroupTheory.FirstCohomologyDimensionKourovka16Problem55Wanted
