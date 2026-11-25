/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedPrestackMapping

/-!
# Wanted algebra-prestack mapping model choices

Choose an actual injectively fibrant replacement and establish Kan and
homotopy-invariance laws for the publicly computed mapping-family functor.
The sources use the simplicial-algebra model and its derived presheaf
mapping spaces. The indexing objects and values are both small in u+1;
replacement is ordinary injective small-diagram replacement in that
universe. No accessibility or replacement-existence assumption is an
input. No Artin atlas, cotangent representation, transgression
nondegeneracy or enhanced categorical descent theorem is an input.

References: PTVV, arXiv:1111.3209v4, conventions and §2.1;
Toën--Vaquié, arXiv:math/0503269v5, §§2.1 and 3.1.
-/

open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping

universe u

/-- Choose the standard actual injective diagram replacement. -/
def_wanted algebra_prestack_fibrant_replacement (k : Type u) [CommRing k]
    (F : Prestack k) : FibrantReplacement F

/-- Establish the derived-prestack laws of the fixed native mapping functor. -/
def_wanted derived_mapping_prestack (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (X F : DerivedPrestack.{u, u + 1} k)
    (R : FibrantReplacement F.functor) : MappingPrestackModel k Q X F R
