/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization

/-!
# Original fixed-cardinal generated factorizations on every Arrow

Both complete records come from the original generating families and the
same caller cardinal and ordinal bottom. Each intermediate functor, map on
every commutative square, and natural factor arrow is the original algorithm.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedArrowFactorizations

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- Actual I generation constructs the full cofibration--trivial-fibration record. -/
abbrev cofibrant (d : CofibrantGenerationData C κ) :
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) := d.cofibrantFactorizationData

/-- Actual J generation constructs the full trivial-cofibration--fibration record. -/
abbrev fibrant (d : CofibrantGenerationData C κ) :
    FunctorialFactorizationData (trivialCofibrations C) (fibrations C) := d.fibrantFactorizationData

/-- The original whole I middle functor retains its full fixed-cardinal algorithm. -/
theorem cofibrant_Z (d : CofibrantGenerationData C κ) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    (cofibrant d).Z = (SmallObject.functorialFactorizationData d.I κ).Z := d.cofibrantFactorizationData_Z

/-- The original whole J middle functor retains its full fixed-cardinal algorithm. -/
theorem fibrant_Z (d : CofibrantGenerationData C κ) :
    letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
    (fibrant d).Z = (SmallObject.functorialFactorizationData d.J κ).Z := d.fibrantFactorizationData_Z

/-- Every original I middle map is the original map on the supplied commutative square. -/
theorem cofibrant_map (d : CofibrantGenerationData C κ) {f g : Arrow C} (φ : f ⟶ g) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    (cofibrant d).Z.map φ = SmallObject.objMap d.I κ φ := d.cofibrantFactorizationData_map φ

/-- Every original J middle map is the original map on the supplied commutative square. -/
theorem fibrant_map (d : CofibrantGenerationData C κ) {f g : Arrow C} (φ : f ⟶ g) :
    letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
    (fibrant d).Z.map φ = SmallObject.objMap d.J κ φ := d.fibrantFactorizationData_map φ

/-- The I natural factor arrows recover the original whole Arrow transformation. -/
theorem cofibrant_fac (d : CofibrantGenerationData C κ) :
    (cofibrant d).i ≫ (cofibrant d).p = (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  (cofibrant d).fac

/-- The J natural factor arrows recover the original whole Arrow transformation. -/
theorem fibrant_fac (d : CofibrantGenerationData C κ) :
    (fibrant d).i ≫ (fibrant d).p = (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  (fibrant d).fac

/-- Both original I factor maps recover every supplied original Arrow. -/
theorem cofibrant_fac_app (d : CofibrantGenerationData C κ) (f : Arrow C) :
    (cofibrant d).i.app f ≫ (cofibrant d).p.app f = f.hom := (cofibrant d).fac_app

/-- Both original J factor maps recover every supplied original Arrow. -/
theorem fibrant_fac_app (d : CofibrantGenerationData C κ) (f : Arrow C) :
    (fibrant d).i.app f ≫ (fibrant d).p.app f = f.hom := (fibrant d).fac_app

/-- The original I left-factor square retains every commutative-square source component. -/
theorem cofibrant_i_naturality (d : CofibrantGenerationData C κ) {f g : Arrow C} (φ : f ⟶ g) :
    (cofibrant d).i.app f ≫ (cofibrant d).Z.map φ = φ.left ≫ (cofibrant d).i.app g :=
  ((cofibrant d).i.naturality φ).symm

/-- The original I right-factor square retains every commutative-square target component. -/
theorem cofibrant_p_naturality (d : CofibrantGenerationData C κ) {f g : Arrow C} (φ : f ⟶ g) :
    (cofibrant d).Z.map φ ≫ (cofibrant d).p.app g = (cofibrant d).p.app f ≫ φ.right :=
  (cofibrant d).p.naturality φ

/-- The original J left-factor square retains every commutative-square source component. -/
theorem fibrant_i_naturality (d : CofibrantGenerationData C κ) {f g : Arrow C} (φ : f ⟶ g) :
    (fibrant d).i.app f ≫ (fibrant d).Z.map φ = φ.left ≫ (fibrant d).i.app g :=
  ((fibrant d).i.naturality φ).symm

/-- The original J right-factor square retains every commutative-square target component. -/
theorem fibrant_p_naturality (d : CofibrantGenerationData C κ) {f g : Arrow C} (φ : f ⟶ g) :
    (fibrant d).Z.map φ ≫ (fibrant d).p.app g = (fibrant d).p.app f ≫ φ.right :=
  (fibrant d).p.naturality φ

end HomotopicalAlgebra.GeneratedArrowFactorizations
