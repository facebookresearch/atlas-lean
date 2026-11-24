/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedFibreClosingPaths
public import Batteries.Util.ProofWanted

/-!
# Wanted coupled negative-cyclic path comparisons for derived intersections

The source constructor chooses compatible diagram replacements for
the entire native fibre diagram. It fixes the diagonal projection,
both endpoint sections and the universal comparison, before the
computed relative-cylinder homotopy is used. No residue form or
nondegeneracy conclusion is passed as background.

Reference: PTVV arXiv:1111.3209v4 Theorem 2.9, pp.39--40.
-/

open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedFibreClosingPaths
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams

universe u

def_wanted coupled_derived_fibre_negative_cyclic_models (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (NC : NegativeCyclicDiagram D.functor (2 : ℤ))
    (X Y F : DerivedStack Q) (P : NaturalPathModel F)
    (f : StackMap X F) (g : StackMap Y F) (Z : FibreStackModel P f g) (n : ℤ) :
    FibreNCModels (D := D) (NC := NC) Z n
