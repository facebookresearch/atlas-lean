/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.SSetFunctoriality
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Basic

/-! # Tests for functoriality of simplicial-set local-coefficient chains -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

universe uR uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.SSetFunctorialityTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X : SSet.{uX}}
variable {L K P : SSet.LocalSystem R X}
variable (α : L ⟶ K) (β : K ⟶ P)

example {n : ℕ} (σ : X _⦋n⦌) :
    SSet.localCoefficientFamily L n σ ⟶
      SSet.localCoefficientObj L n :=
  SSet.localCoefficientι L σ

example (n : ℕ) :
    SSet.localCoefficientObj L n ⟶ SSet.localCoefficientObj K n :=
  SSet.localCoefficientMap α n

example {n : ℕ} (σ : X _⦋n⦌) :
    SSet.localCoefficientι L σ ≫ SSet.localCoefficientMap α n =
      α.app
          ((SSet.fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) σ).left ≫
        SSet.localCoefficientι K σ :=
  SSet.localCoefficientι_map α σ

example (n : ℕ) :
    SSet.localCoefficientMap (𝟙 L) n = 𝟙 _ :=
  SSet.localCoefficientMap_id n

example (n : ℕ) :
    SSet.localCoefficientMap (α ≫ β) n =
      SSet.localCoefficientMap α n ≫
        SSet.localCoefficientMap β n :=
  SSet.localCoefficientMap_comp α β n

example {n : ℕ} (i : Fin (n + 2)) (σ : X _⦋n + 1⦌) :
    α.app ((SSet.fundamentalGroupoidNerveUnit X).app _ σ).left ≫
        nervePullbackCoefficientFaceHom
          (SSet.fundamentalGroupoidNerveUnit X) K i σ =
      nervePullbackCoefficientFaceHom
          (SSet.fundamentalGroupoidNerveUnit X) L i σ ≫
        α.app
          ((SSet.fundamentalGroupoidNerveUnit X).app _ (X.δ i σ)).left :=
  SSet.localCoefficientFaceHom_naturality α i σ

example {n : ℕ} (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    α.app ((SSet.fundamentalGroupoidNerveUnit X).app _ σ).left ≫
        nervePullbackCoefficientDegeneracyHom
          (SSet.fundamentalGroupoidNerveUnit X) K i σ =
      nervePullbackCoefficientDegeneracyHom
          (SSet.fundamentalGroupoidNerveUnit X) L i σ ≫
        α.app
          ((SSet.fundamentalGroupoidNerveUnit X).app _ (X.σ i σ)).left :=
  SSet.localCoefficientDegeneracyHom_naturality α i σ

example {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    α.app (SSet.FundamentalGroupoid.mk x) ≫
        K.map (SSet.FundamentalGroupoid.homMk e) =
      L.map (SSet.FundamentalGroupoid.homMk e) ≫
        α.app (SSet.FundamentalGroupoid.mk y) :=
  SSet.localSystemHom_homMk_naturality α e

example {n : ℕ} (i : Fin (n + 2)) :
    SSet.localCoefficientMap α (n + 1) ≫
        SSet.localCoefficientFace K i =
      SSet.localCoefficientFace L i ≫
        SSet.localCoefficientMap α n :=
  SSet.localCoefficientMap_naturality_face α i

example :
    SSet.localCoefficientMap α 1 ≫
        SSet.localCoefficientFace K (0 : Fin 2) =
      SSet.localCoefficientFace L (0 : Fin 2) ≫
        SSet.localCoefficientMap α 0 :=
  SSet.localCoefficientMap_naturality_face α 0

example {n : ℕ} (i : Fin (n + 1)) :
    SSet.localCoefficientMap α n ≫
        SSet.localCoefficientDegeneracy K i =
      SSet.localCoefficientDegeneracy L i ≫
        SSet.localCoefficientMap α (n + 1) :=
  SSet.localCoefficientMap_naturality_degeneracy α i

example :
    SSet.localCoefficientData L ⟶ SSet.localCoefficientData K :=
  SSet.localCoefficientDataMap α

example : SSet.localCoefficientDataMap (𝟙 L) = 𝟙 _ :=
  SSet.localCoefficientDataMap_id

example : SSet.localCoefficientDataMap (α ≫ β) =
    SSet.localCoefficientDataMap α ≫ SSet.localCoefficientDataMap β :=
  SSet.localCoefficientDataMap_comp α β

example :
    SSet.LocalSystem R X ⥤
      SimplicialObject.Data (ModuleCat.{max uR uX} R) :=
  SSet.localCoefficientDataFunctor

example :
    SSet.localCoefficientSimplicial L ⟶
      SSet.localCoefficientSimplicial K :=
  SSet.localCoefficientSimplicialMap α

example (n : ℕ) :
    (SSet.localCoefficientSimplicialMap α).app (op ⦋n⦌) =
      SSet.localCoefficientMap α n :=
  SSet.localCoefficientSimplicialMap_app_mk α n

example : SSet.localCoefficientSimplicialMap (𝟙 L) = 𝟙 _ :=
  SSet.localCoefficientSimplicialMap_id

example : SSet.localCoefficientSimplicialMap (α ≫ β) =
    SSet.localCoefficientSimplicialMap α ≫
      SSet.localCoefficientSimplicialMap β :=
  SSet.localCoefficientSimplicialMap_comp α β

example :
    SSet.LocalSystem R X ⥤
      SimplicialObject (ModuleCat.{max uR uX} R) :=
  SSet.localCoefficientSimplicialFunctor

example :
    SSet.localCoefficientChainComplex L ⟶
      SSet.localCoefficientChainComplex K :=
  SSet.localCoefficientChainMap α

example (n : ℕ) :
    (SSet.localCoefficientChainMap α).f n =
      SSet.localCoefficientMap α n :=
  SSet.localCoefficientChainMap_f α n

example : SSet.localCoefficientChainMap (𝟙 L) = 𝟙 _ :=
  SSet.localCoefficientChainMap_id

example : SSet.localCoefficientChainMap (α ≫ β) =
    SSet.localCoefficientChainMap α ≫ SSet.localCoefficientChainMap β :=
  SSet.localCoefficientChainMap_comp α β

example :
    SSet.LocalSystem R X ⥤
      ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
  SSet.localCoefficientChainComplexFunctor

example :
    SSet.localCoefficientSimplicialFunctor.obj L =
      SSet.localCoefficientSimplicial L :=
  SSet.localCoefficientSimplicialFunctor_obj L

example :
    SSet.localCoefficientSimplicialFunctor.map α =
      SSet.localCoefficientSimplicialMap α :=
  SSet.localCoefficientSimplicialFunctor_map α

example :
    SSet.localCoefficientChainComplexFunctor.obj L =
      SSet.localCoefficientChainComplex L :=
  SSet.localCoefficientChainComplexFunctor_obj L

example :
    SSet.localCoefficientChainComplexFunctor.map α =
      SSet.localCoefficientChainMap α :=
  SSet.localCoefficientChainComplexFunctor_map α

end Generic

section ConcreteForwardEdge

private def swap₂ : Equiv.Perm (Fin 2) := Equiv.swap 0 1

private def swapEnd :
    End (SingleObj.star (Equiv.Perm (Fin 2))) :=
  SingleObj.toEnd (Equiv.Perm (Fin 2)) swap₂

example : swap₂ ≠ 1 := by decide

variable {L K : SSet.LocalSystem (ZMod 1)
  (CategoryTheory.nerve (SingleObj (Equiv.Perm (Fin 2))))}
variable (α : L ⟶ K)

example : True := by
  have _h := SSet.localSystemHom_homMk_naturality α
    (CategoryTheory.nerve.edgeMk swapEnd.asHom)
  trivial

end ConcreteForwardEdge

section PointZeroRing

variable {L K : SSet.LocalSystem (ZMod 1) Δ[0]}
variable (α : L ⟶ K)

example (n : ℕ) :
    SSet.localCoefficientObj L n ⟶ SSet.localCoefficientObj K n :=
  SSet.localCoefficientMap α n

example :
    SSet.LocalSystem (ZMod 1) Δ[0] ⥤
      SimplicialObject (ModuleCat (ZMod 1)) :=
  SSet.localCoefficientSimplicialFunctor

example :
    SSet.LocalSystem (ZMod 1) Δ[0] ⥤
      ChainComplex (ModuleCat (ZMod 1)) ℕ :=
  SSet.localCoefficientChainComplexFunctor

end PointZeroRing

section RaisedSimplexUniverse

variable (R : Type 1) [CommRing R]
variable (X : SSet.{2})

example :
    SSet.LocalSystem R X ⥤ SimplicialObject (ModuleCat.{2} R) :=
  SSet.localCoefficientSimplicialFunctor

example :
    SSet.LocalSystem R X ⥤ ChainComplex (ModuleCat.{2} R) ℕ :=
  SSet.localCoefficientChainComplexFunctor

end RaisedSimplexUniverse

section RaisedRingUniverse

variable (R : Type 2) [CommRing R]
variable (X : SSet.{1})

example :
    SSet.LocalSystem R X ⥤ SimplicialObject (ModuleCat.{2} R) :=
  SSet.localCoefficientSimplicialFunctor

example :
    SSet.LocalSystem R X ⥤ ChainComplex (ModuleCat.{2} R) ℕ :=
  SSet.localCoefficientChainComplexFunctor

end RaisedRingUniverse

section StoppingBoundary

-- Pullback along a map of base simplicial sets belongs to LC3.B.
#guard_msgs (error, substring := true) in
#check SSet.localCoefficientPullbackChainMap

-- Homology is outside this packet.
#guard_msgs (error, substring := true) in
#check SSet.localCoefficientHomology

-- Constant coefficients are compared only in LC4.
#guard_msgs (error, substring := true) in
#check SSet.localCoefficientConstantChainIso

end StoppingBoundary

#print axioms SSet.localCoefficientMap
#print axioms SSet.localCoefficientι_map
#print axioms SSet.localCoefficientMap_id
#print axioms SSet.localCoefficientMap_comp
#print axioms SSet.localCoefficientFaceHom_naturality
#print axioms SSet.localCoefficientDegeneracyHom_naturality
#print axioms SSet.localSystemHom_homMk_naturality
#print axioms SSet.localCoefficientMap_naturality_face
#print axioms SSet.localCoefficientMap_naturality_degeneracy
#print axioms SSet.localCoefficientDataMap
#print axioms SSet.localCoefficientDataMap_id
#print axioms SSet.localCoefficientDataMap_comp
#print axioms SSet.localCoefficientDataFunctor
#print axioms SSet.localCoefficientDataFunctor_obj
#print axioms SSet.localCoefficientDataFunctor_map
#print axioms SSet.localCoefficientSimplicialMap
#print axioms SSet.localCoefficientSimplicialMap_app_mk
#print axioms SSet.localCoefficientSimplicialMap_id
#print axioms SSet.localCoefficientSimplicialMap_comp
#print axioms SSet.localCoefficientSimplicialFunctor
#print axioms SSet.localCoefficientSimplicialFunctor_obj
#print axioms SSet.localCoefficientSimplicialFunctor_map
#print axioms SSet.localCoefficientChainMap
#print axioms SSet.localCoefficientChainMap_f
#print axioms SSet.localCoefficientChainMap_id
#print axioms SSet.localCoefficientChainMap_comp
#print axioms SSet.localCoefficientChainComplexFunctor
#print axioms SSet.localCoefficientChainComplexFunctor_obj
#print axioms SSet.localCoefficientChainComplexFunctor_map

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.SSetFunctorialityTests
