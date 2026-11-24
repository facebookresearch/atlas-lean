/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry

/-!
# Wanted simplicial-algebra model adapters

The requests choose the actual cofibrant replacement and establish the
prestack conditions for the fixed Map(QA,-) functor. They assume no
Artin atlas, cotangent representation, symplectic nondegeneracy or
moduli theorem. The native polynomial-resolution and Dold--Kan support
is completed source mathematics and is not re-requested here.

Sources: Toën--Vaquié, arXiv:math/0503269v5, §2.1; PTVV,
arXiv:1111.3209v4, conventions.
-/

open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry

universe u

/-- Choose the standard actual algebra replacement with augmentation. -/
def_wanted simplicial_algebra_replacement_functor (k : Type u) [CommRing k] :
  AlgebraReplacementFunctor k

/-- Establish the derived-prestack conditions for the actual affine mapping functor. -/
def_wanted derived_affine_prestack (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (A : SAlg k) :
  {F : DerivedPrestack.{u, u} k // F.functor = derivedSpecFunctor Q A}
