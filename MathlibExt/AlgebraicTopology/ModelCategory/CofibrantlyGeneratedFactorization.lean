/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated

/-!
# Functorial factorizations from cofibrant generation data

This file converts explicit fixed-cardinal cofibrant-generation data into
the two selected functorial factorizations of a model category. It installs
no instances: a selected model scope may install these proof values when it
chooses the corresponding generation data.
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.CofibrantGenerationData

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- Explicit cofibrant-generation data supplies the selected
cofibration--trivial-fibration functorial factorization. -/
theorem hasFunctorialFactorizationCofibrationsTrivialFibrations
    (d : CofibrantGenerationData C κ) :
    HasFunctorialFactorization (cofibrations C) (trivialFibrations C) := by
  let _ : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  refine ⟨⟨?_⟩⟩
  rw [← trivialFibrations_llp, ← d.I_rlp]
  exact SmallObject.functorialFactorizationData d.I κ

/-- Explicit cofibrant-generation data supplies the selected
trivial-cofibration--fibration functorial factorization. -/
theorem hasFunctorialFactorizationTrivialCofibrationsFibrations
    (d : CofibrantGenerationData C κ) :
    HasFunctorialFactorization (trivialCofibrations C) (fibrations C) := by
  let _ : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
  refine ⟨⟨?_⟩⟩
  rw [← fibrations_llp, ← d.J_rlp]
  exact SmallObject.functorialFactorizationData d.J κ


/-- The actual I-factorization at the supplied cardinal, with only membership transported. -/
noncomputable def cofibrantFactorizationData (d : CofibrantGenerationData C κ) :
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) := by
  letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  exact (SmallObject.functorialFactorizationData d.I κ).ofLE
    (by rw [d.I_rlp, trivialFibrations_llp]) d.I_rlp.le

/-- The actual J-factorization at the same supplied cardinal, without choosing new maps. -/
noncomputable def fibrantFactorizationData (d : CofibrantGenerationData C κ) :
    FunctorialFactorizationData (trivialCofibrations C) (fibrations C) := by
  letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
  exact (SmallObject.functorialFactorizationData d.J κ).ofLE
    (by rw [d.J_rlp, fibrations_llp]) d.J_rlp.le

section RawFields

variable (d : CofibrantGenerationData C κ)

/-- The complete I middle functor is exactly the original fixed-cardinal small-object functor. -/
theorem cofibrantFactorizationData_Z :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    d.cofibrantFactorizationData.Z = (SmallObject.functorialFactorizationData d.I κ).Z := rfl

/-- The complete J middle functor is the original small-object functor at the same cardinal. -/
theorem fibrantFactorizationData_Z :
    letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
    d.fibrantFactorizationData.Z = (SmallObject.functorialFactorizationData d.J κ).Z := rfl

/-- Membership conversion keeps the entire original I left natural transformation. -/
theorem cofibrantFactorizationData_i :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    d.cofibrantFactorizationData.i = (SmallObject.functorialFactorizationData d.I κ).i := rfl

/-- Membership conversion keeps the entire original I right natural transformation. -/
theorem cofibrantFactorizationData_p :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    d.cofibrantFactorizationData.p = (SmallObject.functorialFactorizationData d.I κ).p := rfl

/-- Membership conversion keeps the entire original J left natural transformation. -/
theorem fibrantFactorizationData_i :
    letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
    d.fibrantFactorizationData.i = (SmallObject.functorialFactorizationData d.J κ).i := rfl

/-- Membership conversion keeps the entire original J right natural transformation. -/
theorem fibrantFactorizationData_p :
    letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
    d.fibrantFactorizationData.p = (SmallObject.functorialFactorizationData d.J κ).p := rfl

/-- Every I middle object is the actual original small-object endpoint. -/
theorem cofibrantFactorizationData_obj (f : Arrow C) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    d.cofibrantFactorizationData.Z.obj f = SmallObject.obj d.I κ f.hom := rfl

/-- Every J middle object is the actual original small-object endpoint. -/
theorem fibrantFactorizationData_obj (f : Arrow C) :
    letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
    d.fibrantFactorizationData.Z.obj f = SmallObject.obj d.J κ f.hom := rfl

/-- Every complete I middle map retains the original square and small-object algorithm. -/
theorem cofibrantFactorizationData_map {f g : Arrow C} (φ : f ⟶ g) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    d.cofibrantFactorizationData.Z.map φ = SmallObject.objMap d.I κ φ := rfl

/-- Every complete J middle map retains the same original square and algorithm. -/
theorem fibrantFactorizationData_map {f g : Arrow C} (φ : f ⟶ g) :
    letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
    d.fibrantFactorizationData.Z.map φ = SmallObject.objMap d.J κ φ := rfl

/-- The I left factor is the actual original cellular inclusion. -/
theorem cofibrantFactorizationData_i_app (f : Arrow C) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    d.cofibrantFactorizationData.i.app f = SmallObject.ιObj d.I κ f.hom := rfl

/-- The I right factor is the actual original small-object projection. -/
theorem cofibrantFactorizationData_p_app (f : Arrow C) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    d.cofibrantFactorizationData.p.app f = SmallObject.πObj d.I κ f.hom := rfl

/-- The J left factor is the actual original cellular inclusion. -/
theorem fibrantFactorizationData_i_app (f : Arrow C) :
    letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
    d.fibrantFactorizationData.i.app f = SmallObject.ιObj d.J κ f.hom := rfl

/-- The J right factor is the actual original small-object projection. -/
theorem fibrantFactorizationData_p_app (f : Arrow C) :
    letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
    d.fibrantFactorizationData.p.app f = SmallObject.πObj d.J κ f.hom := rfl

end RawFields


end HomotopicalAlgebra.CofibrantGenerationData
