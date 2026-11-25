/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelStructure

/-!
# Tests for functorial factorizations from generation data

The generic constructors are exercised abstractly and on the native CGWH
cofibrant-generation datum. The datum remains an explicit choice: importing
the provider installs no selected factorization instance.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory

namespace CofibrantlyGeneratedFactorizationTests

section Generic

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

example (d : CofibrantGenerationData C κ) :
    HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
  ⟨⟨d.cofibrantFactorizationData⟩⟩

example (d : CofibrantGenerationData C κ) :
    HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
  ⟨⟨d.fibrantFactorizationData⟩⟩


example (d : CofibrantGenerationData C κ) :
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) :=
  d.cofibrantFactorizationData

example (d : CofibrantGenerationData C κ) :
    FunctorialFactorizationData (trivialCofibrations C) (fibrations C) :=
  d.fibrantFactorizationData

example (d : CofibrantGenerationData C κ) (f : Arrow C) :
    d.cofibrantFactorizationData.i.app f ≫ d.cofibrantFactorizationData.p.app f = f.hom :=
  d.cofibrantFactorizationData.fac_app

example (d : CofibrantGenerationData C κ) (f : Arrow C) :
    d.fibrantFactorizationData.i.app f ≫ d.fibrantFactorizationData.p.app f = f.hom :=
  d.fibrantFactorizationData.fac_app

example (d : CofibrantGenerationData C κ) {f g : Arrow C} (φ : f ⟶ g) :
    φ.left ≫ d.cofibrantFactorizationData.i.app g =
      d.cofibrantFactorizationData.i.app f ≫ d.cofibrantFactorizationData.Z.map φ :=
  d.cofibrantFactorizationData.i.naturality φ

example (d : CofibrantGenerationData C κ) {f g : Arrow C} (φ : f ⟶ g) :
    d.fibrantFactorizationData.Z.map φ ≫ d.fibrantFactorizationData.p.app g =
      d.fibrantFactorizationData.p.app f ≫ φ.right :=
  d.fibrantFactorizationData.p.naturality φ

example (d : CofibrantGenerationData C κ) (f : Arrow C) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    d.cofibrantFactorizationData.Z.obj f = SmallObject.obj d.I κ f.hom :=
  rfl

example (d : CofibrantGenerationData C κ) {f g : Arrow C} (φ : f ⟶ g) :
    letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
    d.fibrantFactorizationData.Z.map φ = SmallObject.objMap d.J κ φ :=
  rfl

example (d : CofibrantGenerationData C κ) (f : Arrow C) :
    d.cofibrantFactorizationData.Z.map (𝟙 f) = 𝟙 (d.cofibrantFactorizationData.Z.obj f) :=
  d.cofibrantFactorizationData.Z.map_id f

example (d : CofibrantGenerationData C κ) {f g h : Arrow C} (φ : f ⟶ g) (ψ : g ⟶ h) :
    d.fibrantFactorizationData.Z.map (φ ≫ ψ) =
      d.fibrantFactorizationData.Z.map φ ≫ d.fibrantFactorizationData.Z.map ψ :=
  d.fibrantFactorizationData.Z.map_comp φ ψ


example (d : CofibrantGenerationData C κ) {f g : Arrow C} (φ : f ⟶ g) :
    d.cofibrantFactorizationData.Z.map φ ≫ d.cofibrantFactorizationData.p.app g =
      d.cofibrantFactorizationData.p.app f ≫ φ.right :=
  d.cofibrantFactorizationData.p.naturality φ

example (d : CofibrantGenerationData C κ) {f g : Arrow C} (φ : f ⟶ g) :
    φ.left ≫ d.fibrantFactorizationData.i.app g =
      d.fibrantFactorizationData.i.app f ≫ d.fibrantFactorizationData.Z.map φ :=
  d.fibrantFactorizationData.i.naturality φ

example (d : CofibrantGenerationData C κ) {f g h : Arrow C} (φ : f ⟶ g) (ψ : g ⟶ h) :
    d.cofibrantFactorizationData.Z.map (φ ≫ ψ) =
      d.cofibrantFactorizationData.Z.map φ ≫ d.cofibrantFactorizationData.Z.map ψ :=
  d.cofibrantFactorizationData.Z.map_comp φ ψ

example (d : CofibrantGenerationData C κ) (f : Arrow C) :
    trivialCofibrations C (d.fibrantFactorizationData.i.app f) ∧
      fibrations C (d.fibrantFactorizationData.p.app f) := ⟨d.fibrantFactorizationData.hi f, d.fibrantFactorizationData.hp f⟩

end Generic

section NoInstalledFactorizations

example : True := by
  fail_if_success
    let _ : HasFunctorialFactorization (cofibrations CGWH.{u, v})
        (trivialFibrations CGWH.{u, v}) := inferInstance
  fail_if_success
    let _ : HasFunctorialFactorization (trivialCofibrations CGWH.{u, v})
        (fibrations CGWH.{u, v}) := inferInstance
  trivial

end NoInstalledFactorizations

section GenuineDatum

local instance cofibrationFactorization :
    HasFunctorialFactorization (cofibrations CGWH.{u, v})
      (trivialFibrations CGWH.{u, v}) :=
  ⟨⟨CGWH.cofibrantGenerationData.cofibrantFactorizationData⟩⟩

local instance trivialCofibrationFactorization :
    HasFunctorialFactorization (trivialCofibrations CGWH.{u, v})
      (fibrations CGWH.{u, v}) :=
  ⟨⟨CGWH.cofibrantGenerationData.fibrantFactorizationData⟩⟩

#synth HasFunctorialFactorization (cofibrations CGWH.{u, v})
  (trivialFibrations CGWH.{u, v})
#synth HasFunctorialFactorization (trivialCofibrations CGWH.{u, v})
  (fibrations CGWH.{u, v})

example : FunctorialFactorizationData (cofibrations CGWH.{u, v})
    (trivialFibrations CGWH.{u, v}) :=
  functorialFactorizationData _ _

example : FunctorialFactorizationData (trivialCofibrations CGWH.{u, v})
    (fibrations CGWH.{u, v}) :=
  functorialFactorizationData _ _

example {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    cofibrations CGWH.{u, v}
      ((functorialFactorizationData (cofibrations CGWH.{u, v})
        (trivialFibrations CGWH.{u, v})).factorizationData f).i :=
  ((functorialFactorizationData (cofibrations CGWH.{u, v})
    (trivialFibrations CGWH.{u, v})).factorizationData f).hi

example {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    trivialFibrations CGWH.{u, v}
      ((functorialFactorizationData (cofibrations CGWH.{u, v})
        (trivialFibrations CGWH.{u, v})).factorizationData f).p :=
  ((functorialFactorizationData (cofibrations CGWH.{u, v})
    (trivialFibrations CGWH.{u, v})).factorizationData f).hp

example {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    ((functorialFactorizationData (cofibrations CGWH.{u, v})
        (trivialFibrations CGWH.{u, v})).factorizationData f).i ≫
      ((functorialFactorizationData (cofibrations CGWH.{u, v})
        (trivialFibrations CGWH.{u, v})).factorizationData f).p = f :=
  ((functorialFactorizationData (cofibrations CGWH.{u, v})
    (trivialFibrations CGWH.{u, v})).factorizationData f).fac

example {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    trivialCofibrations CGWH.{u, v}
      ((functorialFactorizationData (trivialCofibrations CGWH.{u, v})
        (fibrations CGWH.{u, v})).factorizationData f).i :=
  ((functorialFactorizationData (trivialCofibrations CGWH.{u, v})
    (fibrations CGWH.{u, v})).factorizationData f).hi

example {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    fibrations CGWH.{u, v}
      ((functorialFactorizationData (trivialCofibrations CGWH.{u, v})
        (fibrations CGWH.{u, v})).factorizationData f).p :=
  ((functorialFactorizationData (trivialCofibrations CGWH.{u, v})
    (fibrations CGWH.{u, v})).factorizationData f).hp

example {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    ((functorialFactorizationData (trivialCofibrations CGWH.{u, v})
        (fibrations CGWH.{u, v})).factorizationData f).i ≫
      ((functorialFactorizationData (trivialCofibrations CGWH.{u, v})
        (fibrations CGWH.{u, v})).factorizationData f).p = f :=
  ((functorialFactorizationData (trivialCofibrations CGWH.{u, v})
    (fibrations CGWH.{u, v})).factorizationData f).fac

end GenuineDatum

section UniverseMatrix

example : HasFunctorialFactorization (cofibrations CGWH.{0, 0})
    (trivialFibrations CGWH.{0, 0}) :=
  ⟨⟨CGWH.cofibrantGenerationData.cofibrantFactorizationData⟩⟩

example : HasFunctorialFactorization (trivialCofibrations CGWH.{1, 1})
    (fibrations CGWH.{1, 1}) :=
  ⟨⟨CGWH.cofibrantGenerationData.fibrantFactorizationData⟩⟩

example : HasFunctorialFactorization (cofibrations CGWH.{0, 1})
    (trivialFibrations CGWH.{0, 1}) :=
  ⟨⟨CGWH.cofibrantGenerationData.cofibrantFactorizationData⟩⟩

example : HasFunctorialFactorization (trivialCofibrations CGWH.{1, 0})
    (fibrations CGWH.{1, 0}) :=
  ⟨⟨CGWH.cofibrantGenerationData.fibrantFactorizationData⟩⟩

end UniverseMatrix

section Teardown

example : True := by
  fail_if_success
    let _ : HasFunctorialFactorization (cofibrations CGWH.{u, v})
        (trivialFibrations CGWH.{u, v}) := inferInstance
  fail_if_success
    let _ : HasFunctorialFactorization (trivialCofibrations CGWH.{u, v})
        (fibrations CGWH.{u, v}) := inferInstance
  trivial

end Teardown

end CofibrantlyGeneratedFactorizationTests

end MathlibExtTest.AlgebraicTopology.ModelCategory

#check CofibrantGenerationData.cofibrantFactorizationData
#check CofibrantGenerationData.fibrantFactorizationData

#print axioms CofibrantGenerationData.cofibrantFactorizationData
#print axioms CofibrantGenerationData.fibrantFactorizationData
