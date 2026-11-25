/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Existence

/-!# Actual compatible-data witness and selected-map contracts -/
set_option autoImplicit false
noncomputable section
universe w u v
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
namespace MathlibExtTest.CompatibleCofibrantGeneration
variable {M : Type u} [Category.{v} M] [ModelCategory M]

example {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData M κ) : HasCompatibleCofibrantGeneration.{w} M :=
  HasCompatibleCofibrantGeneration.ofData d

example [IsCombinatorialModelCategory.{w} M] : HasCompatibleCofibrantGeneration.{w} M :=
  HasCompatibleCofibrantGeneration.ofCombinatorial

example {κ μ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (d : CofibrantGenerationData M κ) (e : CofibrantGenerationData M μ) :
    Nonempty (HasCompatibleCofibrantGeneration.{w} M) ∧
      HasCompatibleCofibrantGeneration.ofData d = HasCompatibleCofibrantGeneration.ofData e :=
  ⟨⟨HasCompatibleCofibrantGeneration.ofData d⟩, Subsingleton.elim _ _⟩

variable [h : HasCompatibleCofibrantGeneration.{w} M]

example : Cardinal.{w} := HasCompatibleCofibrantGeneration.cardinal (M := M)
example : Fact (HasCompatibleCofibrantGeneration.cardinal (M := M)).IsRegular :=
  HasCompatibleCofibrantGeneration.cardinal_regular

example : letI : Fact (HasCompatibleCofibrantGeneration.cardinal (M := M)).IsRegular :=
      HasCompatibleCofibrantGeneration.cardinal_regular
    letI : OrderBot (HasCompatibleCofibrantGeneration.cardinal (M := M)).ord.ToType :=
      HasCompatibleCofibrantGeneration.orderBot
    CofibrantGenerationData M (HasCompatibleCofibrantGeneration.cardinal (M := M)) :=
  HasCompatibleCofibrantGeneration.data

example : (HasCompatibleCofibrantGeneration.generatingCofibrations (M := M)).rlp =
    trivialFibrations M := HasCompatibleCofibrantGeneration.generatingCofibrations_rlp

example : (HasCompatibleCofibrantGeneration.generatingTrivialCofibrations (M := M)).rlp =
    fibrations M := HasCompatibleCofibrantGeneration.generatingTrivialCofibrations_rlp

example : FunctorialFactorizationData (cofibrations M) (trivialFibrations M) :=
  HasCompatibleCofibrantGeneration.cofibrantFactorizationData

example : FunctorialFactorizationData (trivialCofibrations M) (fibrations M) :=
  HasCompatibleCofibrantGeneration.fibrantFactorizationData

example (f : Arrow M) :
    (HasCompatibleCofibrantGeneration.cofibrantFactorizationData (M := M)).i.app f ≫
      (HasCompatibleCofibrantGeneration.cofibrantFactorizationData (M := M)).p.app f = f.hom :=
  HasCompatibleCofibrantGeneration.cofibrantFactorizationData_fac f

example {f g : Arrow M} (φ : f ⟶ g) :
    φ.left ≫ (HasCompatibleCofibrantGeneration.fibrantFactorizationData (M := M)).i.app g =
      (HasCompatibleCofibrantGeneration.fibrantFactorizationData (M := M)).i.app f ≫
        (HasCompatibleCofibrantGeneration.fibrantFactorizationData (M := M)).Z.map φ :=
  HasCompatibleCofibrantGeneration.fibrantFactorizationData_i_naturality φ

example {f g k : Arrow M} (φ : f ⟶ g) (ψ : g ⟶ k) :
    (HasCompatibleCofibrantGeneration.cofibrantFactorizationData (M := M)).Z.map (φ ≫ ψ) =
      (HasCompatibleCofibrantGeneration.cofibrantFactorizationData (M := M)).Z.map φ ≫
        (HasCompatibleCofibrantGeneration.cofibrantFactorizationData (M := M)).Z.map ψ :=
  HasCompatibleCofibrantGeneration.cofibrantFactorizationData_map_comp φ ψ

example (f : Arrow M) :
    (HasCompatibleCofibrantGeneration.fibrantFactorizationData (M := M)).Z.map (𝟙 f) =
      𝟙 ((HasCompatibleCofibrantGeneration.fibrantFactorizationData (M := M)).Z.obj f) :=
  HasCompatibleCofibrantGeneration.fibrantFactorizationData_map_id f

example : True := by
  let _ : Fact (HasCompatibleCofibrantGeneration.cardinal (M := M)).IsRegular :=
    HasCompatibleCofibrantGeneration.cardinal_regular
  let _ : OrderBot (HasCompatibleCofibrantGeneration.cardinal (M := M)).ord.ToType :=
    HasCompatibleCofibrantGeneration.orderBot
  fail_if_success
    have _ : CofibrantGenerationData M
        (HasCompatibleCofibrantGeneration.cardinal (M := M)) := inferInstance
  trivial

end MathlibExtTest.CompatibleCofibrantGeneration
