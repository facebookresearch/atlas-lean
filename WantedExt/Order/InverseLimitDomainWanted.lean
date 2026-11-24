/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.ScottContinuity
public import Mathlib.Order.Hom.Basic
public import MathlibExt.Order.ScottContinuity.ContinuousLattice

/-!
# Scott's inverse-limit model `D∞ ≅ [D∞ → D∞]`

Scott solved the domain equation `D ≅ [D → D]` non-trivially by an inverse limit
(D. Scott, *Continuous Lattices*, Oxford PRG-7 (1971), §4; published in *Toposes, Algebraic
Geometry and Logic*, Lecture Notes in Math. 274 (1972), 97–136). Starting from a continuous lattice
`D₀` and a projection pair between `D₀` and `D₁ = [D₀ → D₀]`, he sets `Dₙ₊₁ = [Dₙ → Dₙ]` and lifts
the projection pairs; the inverse limit `D∞` is a continuous lattice (Proposition 4.1)
homeomorphic, and in particular order-isomorphic, to its own space of continuous maps
(Theorem 4.4), and each `Dₙ` is a projection of `D∞` (Proposition 4.2). With application `x(y)`
and abstraction transported along this isomorphism, `D∞` is a model of the untyped λ-calculus in
which β and η both hold.

The entry below records Propositions 4.1–4.2 (for `n = 0`) and Theorem 4.4 as one existence
statement, with Scott's hypothesis and Scott's definition of continuous lattices; the construction
itself is deferred.
-/

@[expose] public section

namespace MathlibExt.Order.InverseLimitDomainWanted

open MathlibExt.Order.ScottContinuity.ContinuousLattice

universe u

/-- **Scott's inverse-limit theorem.** The domain equation `D ≅ [D → D]` has non-trivial
solutions among continuous lattices. For every continuous lattice `D₀` there is a continuous
lattice `D` that is order-isomorphic to the lattice of its own Scott-continuous self-maps, ordered
pointwise, and of which `D₀` is a projection: there are Scott-continuous `e : D₀ → D` and
`p : D → D₀` with `p ∘ e = id` and `e ∘ p ≤ id` (D. Scott, *Continuous Lattices*, Oxford PRG-7
(1971), Proposition 4.1, Proposition 4.2 and Theorem 4.4, with continuous lattices as in
Definition 2.3 and projections as in Definition 3.6). If `D₀` has two distinct elements, so has
`D`, because `e` is injective.

The hypotheses are Scott's. The statement asserts only that such a `D` exists, while Scott
constructs a specific one, `D∞`, from a chosen projection pair between `D₀` and `[D₀ → D₀]`.
Scott states a homeomorphism for the induced topologies; an order isomorphism between complete
lattices is a homeomorphism for their Scott topologies, and for continuous lattices Scott shows
that the topology of `[D → D]` is its Scott topology (Theorem 3.3), so the order isomorphism
carries the same information. -/
theorem_wanted exists_orderIso_scottContinuous_self (D₀ : Type u) [CompleteLattice D₀]
    (h₀ : IsContinuousLattice D₀) :
    ∃ (D : Type u) (_ : CompleteLattice D) (_ : D ≃o {f : D → D // ScottContinuous f})
      (e : D₀ → D) (p : D → D₀),
      IsContinuousLattice D ∧ ScottContinuous e ∧ ScottContinuous p ∧ p ∘ e = id ∧ e ∘ p ≤ id

end MathlibExt.Order.InverseLimitDomainWanted
