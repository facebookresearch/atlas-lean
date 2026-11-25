/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients

@[expose] public noncomputable section

/-!
# Scalar extension of continuous adic coefficient models

Authors: Bhargav Bhatt, Peter Scholze.

Source: The pro-étale topology for schemes, Lemma 4.2.12 and
Lemma 6.8.2, https://arxiv.org/abs/1309.1198.
The same argument applies to an open lattice in a topological module:
on quasi-compact objects one common denominator clears all its values,
and sheafification accounts for arbitrary objects.

For example, with `R = ℤ_ℓ`, `S = ℚ_ℓ` and `L = ℤ_ℓⁿ ⊆ V = ℚ_ℓⁿ`, the sheafified extension of
scalars of `C(-, ℤ_ℓⁿ)` is `C(-, ℚ_ℓⁿ)`.
-/

namespace WantedExt.AlgebraicGeometry.ContinuousAdicCoefficients

open CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients

universe u

/-- For an open, finitely generated `R`-submodule `L` of a topological `R[1/a]`-module `V` such that
every vector has a multiple by a power of `a` in `L`, the comparison from the sheafified extension
of scalars of `C(-, L)` to `C(-, V)` is an isomorphism. -/
public theorem_wanted latticeScalarComparison_isIso
    (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (a : R) [IsLocalization.Away a S]
    (V : Type (u + 1)) [TopologicalSpace V] [AddCommGroup V] [Module S V]
    [IsTopologicalAddGroup V] [ContinuousConstSMul S V]
    (L : Submodule R (restrictedVector R S V)) [Module.Finite R L]
    (openLattice : IsOpen (L : Set (restrictedVector R S V)))
    (fullLattice : ∀ v : V, ∃ n : ℕ, (algebraMap R S a) ^ n • v ∈ L)
    (X : Scheme.{u}) :
    IsIso (latticeScalarComparison R S V L X)

end WantedExt.AlgebraicGeometry.ContinuousAdicCoefficients
