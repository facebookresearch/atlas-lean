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

Generic adic systems, completion criteria and compact-group integral
lattices are already supplied by the public Axiom implementations.
This request identifies their coefficient models with the actual
continuous coefficient sheaf through its specified scalar-extension map.
-/

namespace WantedExt.AlgebraicGeometry.ContinuousAdicCoefficients

open CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients

universe u

/-- Sheafified scalar extension identifies the continuous coefficient
model of a full open lattice with that of its localized module.
The hypotheses are actual openness, finiteness and denominator coverage. -/
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

