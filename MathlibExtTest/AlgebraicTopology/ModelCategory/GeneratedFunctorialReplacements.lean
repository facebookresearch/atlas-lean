/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction

/-!
All-variable clients for the complete generated Arrow factors and replacements.
The category object/hom universes and both original cell universes are independent.
Neither incoming factorization data nor replacement outcomes are assumed.
-/

set_option autoImplicit false

noncomputable section

universe w₁ w₂ uC vC

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.GeneratedFunctorialReplacements

namespace GeneratedReplacementClients

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ₁ : Cardinal.{w₁}} [Fact κ₁.IsRegular] [OrderBot κ₁.ord.ToType]
  {κ₂ : Cardinal.{w₂}} [Fact κ₂.IsRegular] [OrderBot κ₂.ord.ToType]
  (d : CofibrantGenerationData C κ₁) (e : CofibrantGenerationData C κ₂)

-- Complete factorization construction from original generation only.
example : Nonempty (Data (C := C)) := constructs d

example : (fromGeneration d).cofibrantFactor = d.cofibrantFactorizationData :=
  fromGeneration_cofibrantFactor d

example : (fromGeneration d).fibrantFactor = d.fibrantFactorizationData :=
  fromGeneration_fibrantFactor d

example :
    (fromGeneration d).cofibrantFactor.i ≫ (fromGeneration d).cofibrantFactor.p =
      (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  (fromGeneration d).cofibrantFactor.fac

example :
    (fromGeneration d).fibrantFactor.i ≫ (fromGeneration d).fibrantFactor.p =
      (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  (fromGeneration d).fibrantFactor.fac

example (f : Arrow C) : cofibrations C ((fromGeneration d).cofibrantFactor.i.app f) :=
  (fromGeneration d).cofibrantFactor.hi f

example (f : Arrow C) : trivialFibrations C ((fromGeneration d).cofibrantFactor.p.app f) :=
  (fromGeneration d).cofibrantFactor.hp f

example (f : Arrow C) : trivialCofibrations C ((fromGeneration d).fibrantFactor.i.app f) :=
  (fromGeneration d).fibrantFactor.hi f

example (f : Arrow C) : fibrations C ((fromGeneration d).fibrantFactor.p.app f) :=
  (fromGeneration d).fibrantFactor.hp f

-- Every map on a commutative square is the original fixed-cardinal algorithm.
example {f g : Arrow C} (φ : f ⟶ g) :
    letI : d.I.IsCardinalForSmallObjectArgument κ₁ := d.I_smallObject
    (fromGeneration d).cofibrantFactor.Z.map φ = SmallObject.objMap d.I κ₁ φ :=
  rfl

example {f g : Arrow C} (φ : f ⟶ g) :
    letI : d.J.IsCardinalForSmallObjectArgument κ₁ := d.J_smallObject
    (fromGeneration d).fibrantFactor.Z.map φ = SmallObject.objMap d.J κ₁ φ :=
  rfl

example :
    letI : d.I.IsCardinalForSmallObjectArgument κ₁ := d.I_smallObject
    (fromGeneration d).cofibrantFactor.i = (SmallObject.functorialFactorizationData d.I κ₁).i :=
  rfl

example :
    letI : d.J.IsCardinalForSmallObjectArgument κ₁ := d.J_smallObject
    (fromGeneration d).fibrantFactor.p = (SmallObject.functorialFactorizationData d.J κ₁).p :=
  rfl

example {f g : Arrow C} (φ : f ⟶ g) :
    (fromGeneration d).cofibrantFactor.i.app f ≫ (fromGeneration d).cofibrantFactor.Z.map φ =
      φ.left ≫ (fromGeneration d).cofibrantFactor.i.app g :=
  ((fromGeneration d).cofibrantFactor.i.naturality φ).symm

example {f g : Arrow C} (φ : f ⟶ g) :
    (fromGeneration d).cofibrantFactor.Z.map φ ≫ (fromGeneration d).cofibrantFactor.p.app g =
      (fromGeneration d).cofibrantFactor.p.app f ≫ φ.right :=
  (fromGeneration d).cofibrantFactor.p.naturality φ

example {f g : Arrow C} (φ : f ⟶ g) :
    (fromGeneration d).fibrantFactor.i.app f ≫ (fromGeneration d).fibrantFactor.Z.map φ =
      φ.left ≫ (fromGeneration d).fibrantFactor.i.app g :=
  ((fromGeneration d).fibrantFactor.i.naturality φ).symm

example {f g : Arrow C} (φ : f ⟶ g) :
    (fromGeneration d).fibrantFactor.Z.map φ ≫ (fromGeneration d).fibrantFactor.p.app g =
      (fromGeneration d).fibrantFactor.p.app f ≫ φ.right :=
  (fromGeneration d).fibrantFactor.p.naturality φ

example (f : Arrow C) : (fromGeneration d).cofibrantFactor.Z.map (𝟙 f) = 𝟙 _ :=
  (fromGeneration d).cofibrantFactor.Z.map_id f

example {f g h : Arrow C} (φ : f ⟶ g) (ψ : g ⟶ h) :
    (fromGeneration d).fibrantFactor.Z.map (φ ≫ ψ) =
      (fromGeneration d).fibrantFactor.Z.map φ ≫ (fromGeneration d).fibrantFactor.Z.map ψ :=
  (fromGeneration d).fibrantFactor.Z.map_comp φ ψ

-- The same factors on the actual initial/terminal maps give both full functors.
example (X : C) :
    (fromGeneration d).Q.obj X = d.cofibrantFactorizationData.Z.obj (Arrow.mk (initial.to X)) :=
  Q_obj d X

example (X : C) :
    (fromGeneration d).R.obj X = d.fibrantFactorizationData.Z.obj (Arrow.mk (terminal.from X)) :=
  R_obj d X

example {X Y : C} (f : X ⟶ Y) :
    (fromGeneration d).Q.map f = d.cofibrantFactorizationData.Z.map
      (Arrow.homMk (𝟙 (⊥_ C)) f (by simp [initialMap])) := Q_map d f

example {X Y : C} (f : X ⟶ Y) :
    (fromGeneration d).R.map f = d.fibrantFactorizationData.Z.map
      (Arrow.homMk f (𝟙 (⊤_ C)) (by simp [terminalMap])) := R_map d f

example : (fromGeneration d).qInitial ≫ (fromGeneration d).q = initialMap :=
  (fromGeneration d).q_fac

example : (fromGeneration d).r ≫ (fromGeneration d).rTerminal = terminalMap :=
  (fromGeneration d).r_fac

example (X : C) : IsCofibrant ((fromGeneration d).Q.obj X) := (fromGeneration d).q_cofibrant X

example (X : C) : IsFibrant ((fromGeneration d).R.obj X) := (fromGeneration d).r_fibrant X

example (X : C) : weakEquivalences C ((fromGeneration d).q.app X) :=
  ((fromGeneration d).q_trivialFibration X).2

example (X : C) : weakEquivalences C ((fromGeneration d).r.app X) :=
  ((fromGeneration d).r_trivialCofibration X).2

example {X Y : C} (f : X ⟶ Y) :
    (fromGeneration d).Q.map f ≫ (fromGeneration d).q.app Y = (fromGeneration d).q.app X ≫ f :=
  (fromGeneration d).q.naturality f

example {X Y : C} (f : X ⟶ Y) :
    f ≫ (fromGeneration d).r.app Y = (fromGeneration d).r.app X ≫ (fromGeneration d).R.map f :=
  (fromGeneration d).r.naturality f

example {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C ((fromGeneration d).Q.map f) := (fromGeneration d).q_map_weak f hf

example {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C ((fromGeneration d).R.map f) := (fromGeneration d).r_map_weak f hf

-- Both natural weak zigzags quantify separate original families, ranks, and bottoms.
example (X : C) : weakEquivalences C ((qComparisonLeft d e).app X) :=
  Q_comparison_left_weak d e X

example (X : C) : weakEquivalences C ((qComparisonRight d e).app X) :=
  Q_comparison_right_weak d e X

example : qComparisonLeft d e ≫ (fromGeneration d).q =
    qComparisonRight d e ≫ (fromGeneration e).q := Q_comparison_counits d e

example {X Y : C} (f : X ⟶ Y) :
    (Q d ⋙ Q e).map f ≫ (qComparisonLeft d e).app Y =
      (qComparisonLeft d e).app X ≫ (Q d).map f := Q_comparison_left_naturality d e f

example {X Y : C} (f : X ⟶ Y) :
    (Q d ⋙ Q e).map f ≫ (qComparisonRight d e).app Y =
      (qComparisonRight d e).app X ≫ (Q e).map f := Q_comparison_right_naturality d e f

example (X : C) : IsCofibrant ((Q d ⋙ Q e).obj X) := Q_comparison_center_isCofibrant d e X

example (X : C) : weakEquivalences C ((rComparisonLeft d e).app X) :=
  R_comparison_left_weak d e X

example (X : C) : weakEquivalences C ((rComparisonRight d e).app X) :=
  R_comparison_right_weak d e X

example : (fromGeneration d).r ≫ rComparisonLeft d e =
    (fromGeneration e).r ≫ rComparisonRight d e := R_comparison_units d e

example {X Y : C} (f : X ⟶ Y) :
    (R d).map f ≫ (rComparisonLeft d e).app Y =
      (rComparisonLeft d e).app X ≫ (R d ⋙ R e).map f := R_comparison_left_naturality d e f

example {X Y : C} (f : X ⟶ Y) :
    (R e).map f ≫ (rComparisonRight d e).app Y =
      (rComparisonRight d e).app X ≫ (R d ⋙ R e).map f := R_comparison_right_naturality d e f

example (X : C) : IsFibrant ((R d ⋙ R e).obj X) := R_comparison_center_isFibrant d e X

end GeneratedReplacementClients
