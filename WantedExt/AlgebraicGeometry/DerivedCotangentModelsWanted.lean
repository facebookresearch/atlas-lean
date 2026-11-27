/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCotangentModels
public import MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
public import Batteries.Util.ProofWanted

/-!
# Wanted actual square-zero coefficient modules and point cotangent representation

The module value and all shuffle actions are already fixed. Cotangent
representation is natural on actual kernel morphisms and has the literal
split lift as origin. A derived moduli tangent/self-Ext identification
is a separate comparison theorem, not contained in this construction.

References: HAG II math/0404373v7 §§1.3.7 and 1.4.1; PTVV1111.3209v4 conventions;
Toën--Vaquié math/0503269v5 §3.3.
-/

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
open MathlibExt.AlgebraicGeometry.DerivedCotangentModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

universe u

def_wanted square_zero_normalized_kernel_module (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (A : SAlg k) (E : SplitExtension A) : KernelModuleModel N E

def_wanted derived_artin_point_cotangent_representation (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k)
    (X : DerivedStack Q) (geometric : IsDerivedArtin X)
    (A : SAlg k) (x : (Δ[0] : SSet.{u + 1}) ⟶ X.functor.obj A)
    (P : KanPathModel (X.functor.obj A)) :
    CotangentRepresentation N X.toDerivedPrestack A x P
