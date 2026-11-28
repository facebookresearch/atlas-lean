/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
public import Batteries.Util.ProofWanted

/-!
# Wanted actual global negative-cyclic cochain models

The underlying projection and pullback are completed native limit/lift
maps. This construction chooses only actual injective replacements of
the full prescribed affine-family cochain diagrams.
References: PTVV1111.3209v4 §1.1; Bousfield--Kan ChaptersX--XI.
-/

open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams

universe u

def_wanted global_weighted_negative_cyclic_complex (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (p : ℕ) (NC : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k) :
    GlobalNCModel D p NC X
