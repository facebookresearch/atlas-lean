/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.WeakHomotopySingularChains
import Mathlib.Topology.Homotopy.Equiv

/-!
# Tests for singular-chain invariance of weak homotopy equivalences

The clients cover the generic coefficient contract, degree zero, empty and
disconnected spaces, identities, isomorphisms, independent universes,
coefficient naturality, and the boundary against inferring a topological
homotopy equivalence.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicTopology CategoryTheory HomologicalComplex Limits
open CategoryTheory.MorphismProperty

universe w v u

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
namespace WeakHomotopySingularChainsTests

section PublicContract

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]
  {X Y : TopCat.{w}} {f : X ⟶ Y} (A : C)

example (hf : TopCat.weakHomotopyEquivalences f) :
    QuasiIso (((singularChainComplexFunctor C).obj A).map f) :=
  hf.quasiIso_singularChainComplexMap A

example (hf : TopCat.weakHomotopyEquivalences f) :
    QuasiIsoAt (((singularChainComplexFunctor C).obj A).map f) 0 := by
  let _ : QuasiIso (((singularChainComplexFunctor C).obj A).map f) :=
    hf.quasiIso_singularChainComplexMap A
  infer_instance

end PublicContract

section ConcreteSpaces

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]

example (A : C) :
    QuasiIso
      (((singularChainComplexFunctor C).obj A).map
        (𝟙 (TopCat.of (ULift.{w} Empty) : TopCat.{w}))) :=
  TopCat.weakHomotopyEquivalences.quasiIso_singularChainComplexMap
    (TopCat.weakHomotopyEquivalences.id_mem _) A

example (A : C) :
    QuasiIso
      (((singularChainComplexFunctor C).obj A).map
        (𝟙 (TopCat.of (ULift.{w} (Fin 2)) : TopCat.{w}))) :=
  TopCat.weakHomotopyEquivalences.quasiIso_singularChainComplexMap
    (TopCat.weakHomotopyEquivalences.id_mem _) A

example {X Y : TopCat.{w}} (e : X ≅ Y) (A : C) :
    QuasiIso (((singularChainComplexFunctor C).obj A).map e.hom) :=
  TopCat.weakHomotopyEquivalences.quasiIso_singularChainComplexMap
    (MorphismProperty.of_isIso _ e.hom) A

end ConcreteSpaces

section CoefficientNaturality

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C]

example {A B : C} (a : A ⟶ B) {X Y : TopCat.{w}} (f : X ⟶ Y) :
    ((singularChainComplexFunctor C).obj A).map f ≫
        ((singularChainComplexFunctor C).map a).app Y =
      ((singularChainComplexFunctor C).map a).app X ≫
        ((singularChainComplexFunctor C).obj B).map f :=
  ((singularChainComplexFunctor C).map a).naturality f

end CoefficientNaturality

section ExplicitUniverses

example {C : Type 1} [Category.{1} C] [Preadditive C]
    [HasCoproducts.{1} C] [CategoryWithHomology C]
    {X Y : TopCat.{1}} {f : X ⟶ Y}
    (hf : TopCat.weakHomotopyEquivalences f) (A : C) :
    QuasiIso (((singularChainComplexFunctor C).obj A).map f) :=
  hf.quasiIso_singularChainComplexMap A

example {C : Type} [Category C] [Preadditive C]
    [HasCoproducts.{0} C] [CategoryWithHomology C]
    {X Y : TopCat.{0}} {f : X ⟶ Y}
    (hf : TopCat.weakHomotopyEquivalences f) (A : C) :
    QuasiIso (((singularChainComplexFunctor C).obj A).map f) :=
  hf.quasiIso_singularChainComplexMap A

end ExplicitUniverses

section NegativeHomotopyEquivalenceGate

example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : TopCat.of X ⟶ TopCat.of Y}
    (_hf : TopCat.weakHomotopyEquivalences f) : True := by
  fail_if_success
    let _ : Nonempty (ContinuousMap.HomotopyEquiv X Y) := inferInstance
  trivial

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check TopCat.weakHomotopyEquivalences.homotopyEquiv

end NegativeHomotopyEquivalenceGate

#print axioms TopCat.weakHomotopyEquivalences.quasiIso_singularChainComplexMap

end WeakHomotopySingularChainsTests
end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
