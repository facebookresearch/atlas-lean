/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedStackFibreModels

/-!
# Wanted native stack path, product and fibre construction

Assemble the actual path factorization and the stack laws of the
publicly computed product/pullback functors. The outputs contain no
Artin geometricity, local finite presentation, shifted form, orientation
or nondegeneracy theorem.

Reference: Toën--Vezzosi, HAG II, Part 2; PTVV conventions.
-/

open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels

universe u

/-- Construct a genuine natural path factorization of an actual stack. -/
def_wanted derived_stack_natural_path (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (G : DerivedStack Q) : NaturalPathModel G

/-- Establish the stack laws of the literal native product. -/
def_wanted derived_stack_product (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (F G : DerivedStack Q) : ProductStackModel F G

/-- Establish the stack laws of the fixed native path pullback. -/
def_wanted derived_stack_homotopy_pullback (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (F G H : DerivedStack Q)
    (P : NaturalPathModel H) (f : StackMap F H) (g : StackMap G H) : FibreStackModel P f g
