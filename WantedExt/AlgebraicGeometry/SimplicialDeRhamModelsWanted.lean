/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels

/-!
# Wanted actual affine graded mixed de Rham assembly

Each request fixes native forms, every generator image and the completed
ordinary differential. Graded weights and mixed maps use literal Moore
normalization, integer reindexing and the stated shift. This is shared
affine infrastructure, without assuming a paper's geometric conclusion.

Reference: PTVV arXiv:1111.3209v4, §1.1, Definitions 1.7--1.8.
-/

open CategoryTheory
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels

universe u

/-- Assemble actual simplicial forms and their ordinary de Rham maps. -/
def_wanted simplicial_deRham_model (k : Type u) [CommRing k] (A : SAlg k) :
  SimplicialDRModel A

/-- Assemble the normalized affine graded mixed object in the fixed source convention. -/
def_wanted derived_affine_deRham_model (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (A : SAlg k)
    (M : SimplicialDRModel (Q.functor.obj A)) : AffineDRModel Q A M

/-- The actual simplicial de Rham map sends every displayed generator to its image. -/
def_wanted simplicial_deRham_map (k : Type u) [CommRing k] (A B : SAlg k)
    (M : SimplicialDRModel A) (N : SimplicialDRModel B) (f : A ⟶ B) :
  SimplicialDRMap M N f

/-- The actual affine form pullback is the corresponding normalized mixed map. -/
def_wanted derived_affine_deRham_map (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (A B : SAlg k)
    (M : SimplicialDRModel (Q.functor.obj A)) (N : SimplicialDRModel (Q.functor.obj B))
    (D : AffineDRModel Q A M) (E : AffineDRModel Q B N) (f : A ⟶ B)
    (g : SimplicialDRMap M N (Q.functor.map f)) : AffineDRMap D E f g
