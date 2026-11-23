/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels

/-!
# Wanted geometricity of fixed native derived limits

The sources' geometric-limit facts are stated on the actual
product/path-pullback models. Geometricity of their inputs is explicit;
geometricity of the result is the conclusion. These requests do not
assume a mapping-stack or dg-moduli geometricity theorem.

Reference: Toën--Vezzosi, HAG II, Part 2.
-/

open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
open MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels

universe u

/-- Products of actual derived Artin stacks remain derived Artin. -/
theorem_wanted derived_artin_product (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (F G : DerivedStack Q)
    (hF : IsDerivedArtin F) (hG : IsDerivedArtin G) (M : ProductStackModel F G) :
  IsDerivedArtin M.stack

/-- The fixed native homotopy pullback of derived Artin stacks is derived Artin. -/
theorem_wanted derived_artin_homotopy_pullback (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (F G H : DerivedStack Q)
    (hF : IsDerivedArtin F) (hG : IsDerivedArtin G) (hH : IsDerivedArtin H)
    (P : NaturalPathModel H) (f : StackMap F H) (g : StackMap G H)
    (M : FibreStackModel P f g) : IsDerivedArtin M.stack
