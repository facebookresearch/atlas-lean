/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels

/-!
# Wanted actual derived affine stack models

Construct a stack model with an actual weak augmentation from the fixed
Map(QA,-) functor. Its Kan, homotopy-invariance, injective fibrancy and
native étale hyperdescent are outputs. No Artin atlas, cotangent
perfectness, mapping-stack geometricity or shifted form is an input.

References: Toën--Vezzosi, HAG II, Part 2; Toën--Vaquié,
arXiv:math/0503269v5, §2.1.
-/

open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels

universe u

/-- **An étale derived stack model of a derived affine.** For a commutative ring $k$, a cofibrant
replacement functor $Q$ for simplicial commutative $k$-algebras and a simplicial commutative
$k$-algebra $A$: a derived stack $F$ for the derived étale topology defined by $Q$
(`DerivedStack Q`: an injectively fibrant derived prestack with descent along local trivial
fibrations), with a natural transformation from the affine mapping prestack
$\operatorname{Map}(QA, -)$ (`affineMapping k Q A`) to $F$ that is a weak equivalence at every
simplicial commutative $k$-algebra. -/
def_wanted derived_affine_etale_stack (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (A : SAlg k) : AffineStackModel Q A
