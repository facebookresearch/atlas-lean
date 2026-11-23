/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarBaseFunctoriality
public import Mathlib.Data.ZMod.Basic

/-! # Tests for base functoriality of the nerve-pullback coefficient bar -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarBaseFunctorialityTests

universe vG uG vA uA

section Generic

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X Y : SSet.{max uG vG}}
variable (f : X ⟶ Y) (ψ : Y ⟶ CategoryTheory.nerve G) (M : G ⥤ A)
variable [HasCoproducts.{max uG vG} A]

example (n : ℕ) :
    nervePullbackCoefficientObj (f ≫ ψ) M n ⟶
      nervePullbackCoefficientObj ψ M n :=
  nervePullbackCoefficientBaseMap f ψ M n

example {n : ℕ} (σ : X.obj (op (SimplexCategory.mk n))) :
    nervePullbackCoefficientι (f ≫ ψ) M σ ≫
        nervePullbackCoefficientBaseMap f ψ M n =
      nervePullbackCoefficientι ψ M
        (f.app (op (SimplexCategory.mk n)) σ) :=
  nervePullbackCoefficientι_baseMap f ψ M σ

example {n : ℕ} (i : Fin (n + 2))
    (σ : X.obj (op (SimplexCategory.mk (n + 1)))) :
    nervePullbackCoefficientFaceHom ψ M i
          (f.app (op (SimplexCategory.mk (n + 1))) σ) ≫
        eqToHom (congrArg
          (nervePullbackCoefficientFamily ψ M n)
          (SSet.δ_naturality_apply f i σ).symm) =
      nervePullbackCoefficientFaceHom (f ≫ ψ) M i σ :=
  nervePullbackCoefficientFaceHom_base_naturality f ψ M i σ

example {n : ℕ} (i : Fin (n + 1))
    (σ : X.obj (op (SimplexCategory.mk n))) :
    nervePullbackCoefficientDegeneracyHom ψ M i
          (f.app (op (SimplexCategory.mk n)) σ) ≫
        eqToHom (congrArg
          (nervePullbackCoefficientFamily ψ M (n + 1))
          (SSet.σ_naturality_apply f i σ).symm) =
      nervePullbackCoefficientDegeneracyHom (f ≫ ψ) M i σ :=
  nervePullbackCoefficientDegeneracyHom_base_naturality f ψ M i σ

example {n : ℕ} (i : Fin (n + 2)) :
    nervePullbackCoefficientBaseMap f ψ M (n + 1) ≫
        nervePullbackCoefficientFace ψ M i =
      nervePullbackCoefficientFace (f ≫ ψ) M i ≫
        nervePullbackCoefficientBaseMap f ψ M n :=
  nervePullbackCoefficientBaseMap_naturality_face f ψ M i

example {n : ℕ} (i : Fin (n + 1)) :
    nervePullbackCoefficientBaseMap f ψ M n ≫
        nervePullbackCoefficientDegeneracy ψ M i =
      nervePullbackCoefficientDegeneracy (f ≫ ψ) M i ≫
        nervePullbackCoefficientBaseMap f ψ M (n + 1) :=
  nervePullbackCoefficientBaseMap_naturality_degeneracy f ψ M i

example :
    nervePullbackCoefficientData (f ≫ ψ) M ⟶
      nervePullbackCoefficientData ψ M :=
  nervePullbackCoefficientBaseDataMap f ψ M

example (n : ℕ) :
    (nervePullbackCoefficientBaseDataMap f ψ M).app n =
      nervePullbackCoefficientBaseMap f ψ M n :=
  nervePullbackCoefficientBaseDataMap_app f ψ M n

example :
    nervePullbackCoefficientSimplicial (f ≫ ψ) M ⟶
      nervePullbackCoefficientSimplicial ψ M :=
  nervePullbackCoefficientBaseSimplicialMap f ψ M

example (n : ℕ) :
    (nervePullbackCoefficientBaseSimplicialMap f ψ M).app
        (op (SimplexCategory.mk n)) =
      nervePullbackCoefficientBaseMap f ψ M n :=
  nervePullbackCoefficientBaseSimplicialMap_app_mk f ψ M n

section Preadditive

variable [Preadditive A]

example :
    nervePullbackCoefficientComplex (f ≫ ψ) M ⟶
      nervePullbackCoefficientComplex ψ M :=
  nervePullbackCoefficientBaseComplexMap f ψ M

example (n : ℕ) :
    (nervePullbackCoefficientBaseComplexMap f ψ M).f n =
      nervePullbackCoefficientBaseMap f ψ M n :=
  nervePullbackCoefficientBaseComplexMap_f f ψ M n

end Preadditive

end Generic

section NontrivialReindex

private abbrev endpoint : (Δ[0] : SSet) ⟶ Δ[1] :=
  SSet.stdSimplex.δ (0 : Fin 2)

private def pointVertex : (Δ[0] : SSet).obj (op (SimplexCategory.mk 0)) :=
  SSet.stdSimplex.obj₀Equiv.symm 0

variable (L : SSet.LocalSystem (ZMod 1) Δ[1])

example :
    nervePullbackCoefficientObj
        (endpoint ≫ SSet.fundamentalGroupoidNerveUnit Δ[1]) L 0 ⟶
      nervePullbackCoefficientObj
        (SSet.fundamentalGroupoidNerveUnit Δ[1]) L 0 :=
  nervePullbackCoefficientBaseMap endpoint
    (SSet.fundamentalGroupoidNerveUnit Δ[1]) L 0

example :
    nervePullbackCoefficientι
          (endpoint ≫ SSet.fundamentalGroupoidNerveUnit Δ[1])
          L pointVertex ≫
        nervePullbackCoefficientBaseMap endpoint
          (SSet.fundamentalGroupoidNerveUnit Δ[1]) L 0 =
      nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit Δ[1]) L
        (endpoint.app (op (SimplexCategory.mk 0)) pointVertex) :=
  nervePullbackCoefficientι_baseMap endpoint
    (SSet.fundamentalGroupoidNerveUnit Δ[1]) L pointVertex

example :
    SSet.localCoefficientChainComplex (L.pullback endpoint) ⟶
      SSet.localCoefficientChainComplex L :=
  SSet.localCoefficientPullbackChainMap endpoint L

example :
    ((SSet.fundamentalGroupoidNerveUnit Δ[1]).app
        (op (SimplexCategory.mk 0))
        (endpoint.app (op (SimplexCategory.mk 0)) pointVertex)).left =
      (SSet.mapFundamentalGroupoid endpoint).obj
        ((SSet.fundamentalGroupoidNerveUnit Δ[0]).app
          (op (SimplexCategory.mk 0)) pointVertex).left :=
  SSet.localCoefficientPullbackLeftIndex endpoint pointVertex

example :
    (SSet.localCoefficientPullbackChainMap endpoint L).f 0 =
      eqToHom (SSet.localCoefficientPullbackObjEq endpoint L 0) ≫
        nervePullbackCoefficientBaseMap endpoint
          (SSet.fundamentalGroupoidNerveUnit Δ[1]) L 0 :=
  SSet.localCoefficientPullbackChainMap_f endpoint L 0

example :
    nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit Δ[0])
          (L.pullback endpoint) pointVertex ≫
        (SSet.localCoefficientPullbackChainMap endpoint L).f 0 =
      eqToHom
          (SSet.localCoefficientPullbackFamilyEq endpoint L pointVertex) ≫
        nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit Δ[1]) L
          (endpoint.app (op (SimplexCategory.mk 0)) pointVertex) :=
  SSet.localCoefficientι_pullbackChainMap endpoint L pointVertex

end NontrivialReindex

section SSetSpecialization

universe uR uX

variable {R : Type uR} [CommRing R]
variable {X Y : SSet.{uX}}
variable (f : X ⟶ Y) (L : SSet.LocalSystem R Y)

example :
    f ≫ SSet.fundamentalGroupoidNerveUnit Y =
      SSet.fundamentalGroupoidNerveUnit X ≫
        CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f) :=
  SSet.fundamentalGroupoidNerveUnit_naturality f

example : SSet.LocalSystem R X := L.pullback f

example {n : ℕ} (σ : X _⦋n⦌) :
    ((SSet.fundamentalGroupoidNerveUnit Y).app
        (op (SimplexCategory.mk n))
        (f.app (op (SimplexCategory.mk n)) σ)).left =
      (SSet.mapFundamentalGroupoid f).obj
        ((SSet.fundamentalGroupoidNerveUnit X).app
          (op (SimplexCategory.mk n)) σ).left :=
  SSet.localCoefficientPullbackLeftIndex f σ

example (n : ℕ) :
    (nervePullbackCoefficientData
        (SSet.fundamentalGroupoidNerveUnit X ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L).obj n =
      (nervePullbackCoefficientData
        (f ≫ SSet.fundamentalGroupoidNerveUnit Y) L).obj n :=
  SSet.localCoefficientPullbackObjEq f L n

example {n : ℕ} (σ : X _⦋n⦌) :
    nervePullbackCoefficientFamily
        (SSet.fundamentalGroupoidNerveUnit X ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L n σ =
      nervePullbackCoefficientFamily
        (f ≫ SSet.fundamentalGroupoidNerveUnit Y) L n σ :=
  SSet.localCoefficientPullbackFamilyEq f L σ

example :
    nervePullbackCoefficientData
        (SSet.fundamentalGroupoidNerveUnit X ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L ⟶
      nervePullbackCoefficientData
        (SSet.fundamentalGroupoidNerveUnit Y) L :=
  SSet.localCoefficientPullbackDataMap f L

example (n : ℕ) :
    (SSet.localCoefficientPullbackDataMap f L).app n =
      eqToHom (SSet.localCoefficientPullbackObjEq f L n) ≫
        nervePullbackCoefficientBaseMap f
          (SSet.fundamentalGroupoidNerveUnit Y) L n :=
  SSet.localCoefficientPullbackDataMap_app f L n

example :
    nervePullbackCoefficientSimplicial
        (SSet.fundamentalGroupoidNerveUnit X ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)) L ⟶
      nervePullbackCoefficientSimplicial
        (SSet.fundamentalGroupoidNerveUnit Y) L :=
  SSet.localCoefficientPullbackSimplicialMap f L

example (n : ℕ) :
    (SSet.localCoefficientPullbackSimplicialMap f L).app
        (op (SimplexCategory.mk n)) =
      eqToHom (SSet.localCoefficientPullbackObjEq f L n) ≫
        nervePullbackCoefficientBaseMap f
          (SSet.fundamentalGroupoidNerveUnit Y) L n :=
  SSet.localCoefficientPullbackSimplicialMap_app_mk f L n

example :
    SSet.localCoefficientChainComplex (L.pullback f) ⟶
      SSet.localCoefficientChainComplex L :=
  SSet.localCoefficientPullbackChainMap f L

example (n : ℕ) :
    (SSet.localCoefficientPullbackChainMap f L).f n =
      eqToHom (SSet.localCoefficientPullbackObjEq f L n) ≫
        nervePullbackCoefficientBaseMap f
          (SSet.fundamentalGroupoidNerveUnit Y) L n :=
  SSet.localCoefficientPullbackChainMap_f f L n

example {n : ℕ} (σ : X _⦋n⦌) :
    nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit X) (L.pullback f) σ ≫
        (SSet.localCoefficientPullbackChainMap f L).f n =
      eqToHom (SSet.localCoefficientPullbackFamilyEq f L σ) ≫
        nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit Y) L
          (f.app (op (SimplexCategory.mk n)) σ) :=
  SSet.localCoefficientι_pullbackChainMap f L σ

end SSetSpecialization

section IndependentUniverses

variable {G : Type 1} [Category.{2} G]
variable {A : Type 3} [Category.{1} A] [Preadditive A]
variable [HasCoproducts.{2} A]
variable {X Y : SSet.{2}}
variable (f : X ⟶ Y) (ψ : Y ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

example :
    nervePullbackCoefficientData (f ≫ ψ) M ⟶
      nervePullbackCoefficientData ψ M :=
  nervePullbackCoefficientBaseDataMap f ψ M

example :
    nervePullbackCoefficientSimplicial (f ≫ ψ) M ⟶
      nervePullbackCoefficientSimplicial ψ M :=
  nervePullbackCoefficientBaseSimplicialMap f ψ M

example :
    nervePullbackCoefficientComplex (f ≫ ψ) M ⟶
      nervePullbackCoefficientComplex ψ M :=
  nervePullbackCoefficientBaseComplexMap f ψ M

end IndependentUniverses

section IndependentSSetUniverses

variable (R₁ : Type 1) [CommRing R₁]
variable {X₂ Y₂ : SSet.{2}}
variable (f₂ : X₂ ⟶ Y₂) (L₁ : SSet.LocalSystem R₁ Y₂)

example :
    SSet.localCoefficientChainComplex (L₁.pullback f₂) ⟶
      SSet.localCoefficientChainComplex L₁ :=
  SSet.localCoefficientPullbackChainMap f₂ L₁

example (n : ℕ) :
    (SSet.localCoefficientPullbackChainMap f₂ L₁).f n =
      eqToHom (SSet.localCoefficientPullbackObjEq f₂ L₁ n) ≫
        nervePullbackCoefficientBaseMap f₂
          (SSet.fundamentalGroupoidNerveUnit Y₂) L₁ n :=
  SSet.localCoefficientPullbackChainMap_f f₂ L₁ n

variable (R₂ : Type 2) [CommRing R₂]
variable {X₁ Y₁ : SSet.{1}}
variable (f₁ : X₁ ⟶ Y₁) (L₂ : SSet.LocalSystem R₂ Y₁)

example :
    SSet.localCoefficientChainComplex (L₂.pullback f₁) ⟶
      SSet.localCoefficientChainComplex L₂ :=
  SSet.localCoefficientPullbackChainMap f₁ L₂

example (n : ℕ) :
    (SSet.localCoefficientPullbackChainMap f₁ L₂).f n =
      eqToHom (SSet.localCoefficientPullbackObjEq f₁ L₂ n) ≫
        nervePullbackCoefficientBaseMap f₁
          (SSet.fundamentalGroupoidNerveUnit Y₁) L₂ n :=
  SSet.localCoefficientPullbackChainMap_f f₁ L₂ n

end IndependentSSetUniverses

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check SSet.localCoefficientPullbackChainMap_id

#guard_msgs (error, substring := true) in
#check SSet.localCoefficientPullbackChainMap_comp

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPullbackChainMap

end StoppingBoundary

#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientBaseMap
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientι_baseMap
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom_base_naturality
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom_base_naturality
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientBaseMap_naturality_face
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientBaseMap_naturality_degeneracy
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientBaseDataMap
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientBaseDataMap_app
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientBaseSimplicialMap
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientBaseSimplicialMap_app_mk
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientBaseComplexMap
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientBaseComplexMap_f
#print axioms SSet.fundamentalGroupoidNerveUnit_naturality
#print axioms SSet.localCoefficientPullbackLeftIndex
#print axioms SSet.localCoefficientPullbackObjEq
#print axioms SSet.localCoefficientPullbackFamilyEq
#print axioms SSet.localCoefficientPullbackDataMap
#print axioms SSet.localCoefficientPullbackDataMap_app
#print axioms SSet.localCoefficientPullbackSimplicialMap
#print axioms SSet.localCoefficientPullbackSimplicialMap_app_mk
#print axioms SSet.localCoefficientPullbackRawChainMap
#print axioms SSet.localCoefficientPullbackChainMap
#print axioms SSet.localCoefficientPullbackChainMap_f
#print axioms SSet.localCoefficientι_pullbackChainMap

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarBaseFunctorialityTests
