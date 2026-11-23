/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWeakEquivalenceChains
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

/-!
# Singular-chain invariance under weak homotopy equivalences

Topological weak homotopy equivalences are defined by applying the Kan weak
equivalence predicate to the singular simplicial map.  Singular chains are
the unnormalized simplicial chains of that same singular complex, so the
result is the Kan chain theorem without any topological homotopy-equivalence
premise.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicTopology CategoryTheory HomologicalComplex Limits

universe w v u

namespace TopCat.weakHomotopyEquivalences

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]

/-- A weak homotopy equivalence induces a quasi-isomorphism on singular
chains. -/
theorem quasiIso_singularChainComplexMap
    {X Y : TopCat.{w}} {f : X ⟶ Y}
    (hf : TopCat.weakHomotopyEquivalences f) (A : C) :
    QuasiIso (((singularChainComplexFunctor C).obj A).map f) :=
  SSet.KanComplex.W.quasiIso_chainComplexMap hf A

end TopCat.weakHomotopyEquivalences
