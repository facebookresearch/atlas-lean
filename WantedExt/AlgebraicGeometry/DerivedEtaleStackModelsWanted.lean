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

/-- Construct the actual étale stack representative of a derived affine. -/
def_wanted derived_affine_etale_stack (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (A : SAlg k) : AffineStackModel Q A
