/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The chain homotopy equivalence induced by a simplicial homotopy equivalence:
two maps `f : X ⟶ Y`, `g : Y ⟶ X` with simplicial homotopies `f ≫ g ≃ 𝟙` and
`g ≫ f ≃ 𝟙` give a chain `HomotopyEquiv` whose forward and inverse are
exactly `SSet.chainComplexMap f R` and `SSet.chainComplexMap g R`. Homotopies are
obtained via `SimplicialObject.Homotopy.sSetChainComplexMap` transported along
`Functor.map_comp` and `Functor.map_id`. -/
noncomputable def chainHomotopyEquivOfSimplicialHomotopyEquiv
    {X Y : SSet.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (Hfg : SimplicialObject.Homotopy (f ≫ g) (𝟙 X))
    (Hgf : SimplicialObject.Homotopy (g ≫ f) (𝟙 Y))
    (R : C) : HomotopyEquiv (X.chainComplex R) (Y.chainComplex R) where
  hom := SSet.chainComplexMap f R
  inv := SSet.chainComplexMap g R
  homotopyHomInvId :=
    let F := (SSet.chainComplexFunctor C).obj R
    (_root_.Homotopy.ofEq (F.map_comp f g).symm).trans
      ((Hfg.sSetChainComplexMap R).trans (_root_.Homotopy.ofEq (F.map_id X)))
  homotopyInvHomId :=
    let F := (SSet.chainComplexFunctor C).obj R
    (_root_.Homotopy.ofEq (F.map_comp g f).symm).trans
      ((Hgf.sSetChainComplexMap R).trans (_root_.Homotopy.ofEq (F.map_id Y)))

@[simp]
theorem chainHomotopyEquivOfSimplicialHomotopyEquiv_hom
    {X Y : SSet.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (Hfg : SimplicialObject.Homotopy (f ≫ g) (𝟙 X))
    (Hgf : SimplicialObject.Homotopy (g ≫ f) (𝟙 Y))
    (R : C) :
    (chainHomotopyEquivOfSimplicialHomotopyEquiv f g Hfg Hgf R).hom =
      SSet.chainComplexMap f R := rfl

@[simp]
theorem chainHomotopyEquivOfSimplicialHomotopyEquiv_inv
    {X Y : SSet.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (Hfg : SimplicialObject.Homotopy (f ≫ g) (𝟙 X))
    (Hgf : SimplicialObject.Homotopy (g ≫ f) (𝟙 Y))
    (R : C) :
    (chainHomotopyEquivOfSimplicialHomotopyEquiv f g Hfg Hgf R).inv =
      SSet.chainComplexMap g R := rfl

variable [CategoryWithHomology C]

/-- The forward chain map of a simplicial homotopy equivalence is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_of_simplicialHomotopyEquiv
    {X Y : SSet.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (Hfg : SimplicialObject.Homotopy (f ≫ g) (𝟙 X))
    (Hgf : SimplicialObject.Homotopy (g ≫ f) (𝟙 Y))
    (R : C) :
    QuasiIso (SSet.chainComplexMap f R) :=
  (chainHomotopyEquivOfSimplicialHomotopyEquiv f g Hfg Hgf R).quasiIso_hom

end SSet
