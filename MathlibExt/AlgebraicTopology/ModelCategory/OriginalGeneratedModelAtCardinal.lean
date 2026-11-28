/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModel
public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument

/-!
# Original two-family assembly at a supplied regular cardinal and bottom

Both records are the actual small-object constructions at the supplied
cardinal and its supplied bottom dictionary. The model assembly receives
those complete records, so its factor and replacement interfaces retain
the original small-object functors and every Arrow action.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.OriginalGeneratedModelAtCardinal

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] [HasFiniteColimits C]
  (I K W : MorphismProperty C) (κ : Cardinal.{w})
  [Fact κ.IsRegular] [B : OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ] [K.IsCardinalForSmallObjectArgument κ]
  (hW : W.HasTwoOutOfThreeProperty) (hRight : I.rlp = K.rlp ⊓ W)
  (hAcyclic : K.rlp.llp ≤ W)

/-- The entire original I record at exactly the supplied cardinal and bottom. -/
def originalI : FunctorialFactorizationData I.rlp.llp I.rlp :=
  SmallObject.functorialFactorizationData I κ

/-- The entire original K record at the same actual supplied cardinal and bottom. -/
def originalK : FunctorialFactorizationData K.rlp.llp K.rlp :=
  SmallObject.functorialFactorizationData K κ

/-- Assemble the classes using these two actual records, not an existential factor getter. -/
@[instance_reducible]
def modelCategory : ModelCategory C :=
  OriginalGeneratedModel.modelCategory I K W hW hRight hAcyclic
    (originalI I κ) (originalK K κ)

/-- The returned I record is exactly the original same-cardinal record with retyped membership. -/
def cofibrantFactorizationData :
    letI : ModelCategory C := modelCategory I K W κ hW hRight hAcyclic
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) :=
  OriginalGeneratedModel.cofibrantFactorizationData I K W hW hRight hAcyclic
    (originalI I κ) (originalK K κ)

/-- The returned K record keeps the entire original same-cardinal factor construction. -/
def fibrantFactorizationData :
    letI : ModelCategory C := modelCategory I K W κ hW hRight hAcyclic
    FunctorialFactorizationData (trivialCofibrations C) (fibrations C) :=
  OriginalGeneratedModel.fibrantFactorizationData I K W hW hRight hAcyclic
    (originalI I κ) (originalK K κ)

/-- Every I object is the original selected small-object endpoint. -/
theorem cofibrantFactorizationData_obj (F : Arrow C) :
    let : ModelCategory C := modelCategory I K W κ hW hRight hAcyclic
    (cofibrantFactorizationData I K W κ hW hRight hAcyclic).Z.obj F =
      SmallObject.obj I κ F.hom := rfl

/-- Every K object is the original selected small-object endpoint. -/
theorem fibrantFactorizationData_obj (F : Arrow C) :
    let : ModelCategory C := modelCategory I K W κ hW hRight hAcyclic
    (fibrantFactorizationData I K W κ hW hRight hAcyclic).Z.obj F =
      SmallObject.obj K κ F.hom := rfl

/-- Every I Arrow action is the original same-cardinal small-object function. -/
theorem cofibrantFactorizationData_map {F G : Arrow C} (a : F ⟶ G) :
    let : ModelCategory C := modelCategory I K W κ hW hRight hAcyclic
    (cofibrantFactorizationData I K W κ hW hRight hAcyclic).Z.map a =
      SmallObject.objMap I κ a := rfl

/-- Every K Arrow action is the original same-cardinal small-object function. -/
theorem fibrantFactorizationData_map {F G : Arrow C} (a : F ⟶ G) :
    let : ModelCategory C := modelCategory I K W κ hW hRight hAcyclic
    (fibrantFactorizationData I K W κ hW hRight hAcyclic).Z.map a =
      SmallObject.objMap K κ a := rfl

/-- The I inclusion is the original same-cardinal small-object inclusion. -/
theorem cofibrantFactorizationData_i (F : Arrow C) :
    let : ModelCategory C := modelCategory I K W κ hW hRight hAcyclic
    (cofibrantFactorizationData I K W κ hW hRight hAcyclic).i.app F =
      SmallObject.ιObj I κ F.hom := rfl

/-- The I projection is the original same-cardinal small-object projection. -/
theorem cofibrantFactorizationData_p (F : Arrow C) :
    let : ModelCategory C := modelCategory I K W κ hW hRight hAcyclic
    (cofibrantFactorizationData I K W κ hW hRight hAcyclic).p.app F =
      SmallObject.πObj I κ F.hom := rfl

/-- The K inclusion is the original same-cardinal small-object inclusion. -/
theorem fibrantFactorizationData_i (F : Arrow C) :
    let : ModelCategory C := modelCategory I K W κ hW hRight hAcyclic
    (fibrantFactorizationData I K W κ hW hRight hAcyclic).i.app F =
      SmallObject.ιObj K κ F.hom := rfl

/-- The K projection is the original same-cardinal small-object projection. -/
theorem fibrantFactorizationData_p (F : Arrow C) :
    let : ModelCategory C := modelCategory I K W κ hW hRight hAcyclic
    (fibrantFactorizationData I K W κ hW hRight hAcyclic).p.app F =
      SmallObject.πObj K κ F.hom := rfl

/-- All five constructed classes retain precisely the original same-cardinal families. -/
theorem five_classes :
    let : ModelCategory C := modelCategory I K W κ hW hRight hAcyclic
    weakEquivalences C = W ∧ cofibrations C = I.rlp.llp ∧ fibrations C = K.rlp ∧
      trivialCofibrations C = K.rlp.llp ∧ trivialFibrations C = I.rlp := by
  exact OriginalGeneratedModel.five_classes I K W hW hRight hAcyclic
    (originalI I κ) (originalK K κ)

end HomotopicalAlgebra.OriginalGeneratedModelAtCardinal
