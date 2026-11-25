/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Semi-model data with the original source restrictions

The cofibrant-source restrictions are those of White--Yau,
*Bousfield localization and algebras over colored operads*,
arXiv:1503.06720v2, Definition 2.2.1. Cofibrancy is intrinsic: the map from
the initial object lies in the chosen cofibration class. The second lifting
and functorial factorization statements retain that restriction.

The raw intermediate-object functor may be defined on all arrows. Its
factor-class proofs below are asserted only on the stated source class;
this data does not install an unrestricted factorization instance.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {D : Type u} [Category.{v} D]

/-- Intrinsic cofibrancy for a specified cofibration class. -/
def IntrinsicCofibrant [HasInitial D] (cof : MorphismProperty D) (X : D) : Prop :=
  cof (initial.to X)

/-- A functorial factorization whose class assertions retain a source condition. -/
structure SourceRestrictedFunctorialFactorizationData
    (left right : MorphismProperty D) (source : D → Prop) where
  /-- The actual intermediate-object functor on the original arrow category. -/
  Z : Arrow D ⥤ D
  /-- The actual first natural transformation. -/
  i : Arrow.leftFunc ⟶ Z
  /-- The actual second natural transformation. -/
  p : Z ⟶ Arrow.rightFunc
  /-- The two original maps compose to the original arrow. -/
  fac : i ≫ p = Arrow.leftToRight
  /-- The first factor has its asserted class for the permitted original sources. -/
  hi (f : Arrow D) : source f.left → left (i.app f)
  /-- The second factor has its asserted class for those same original sources. -/
  hp (f : Arrow D) : source f.left → right (p.app f)

namespace SourceRestrictedFunctorialFactorizationData

variable {left right : MorphismProperty D} {source : D → Prop}
  (data : SourceRestrictedFunctorialFactorizationData left right source)

/-- The original arrow is the composite of its two actual factors. -/
@[reassoc (attr := simp)]
theorem fac_app (f : Arrow D) : data.i.app f ≫ data.p.app f = f.hom := by
  change (data.i ≫ data.p).app f = f.hom
  rw [data.fac]
  rfl

/-- The source-restricted data gives a genuine factorization of an eligible arrow. -/
def factorizationData {X Y : D} (f : X ⟶ Y) (hX : source X) :
    MapFactorizationData left right f where
  Z := data.Z.obj (Arrow.mk f)
  i := data.i.app (Arrow.mk f)
  p := data.p.app (Arrow.mk f)
  fac := data.fac_app (Arrow.mk f)
  hi := data.hi (Arrow.mk f) hX
  hp := data.hp (Arrow.mk f) hX

/-- The actual comparison between intermediate objects retains arrow functoriality. -/
def mapZ {f g : Arrow D} (φ : f ⟶ g) : data.Z.obj f ⟶ data.Z.obj g := data.Z.map φ

/-- The first original map commutes with every actual arrow comparison. -/
@[reassoc (attr := simp)]
theorem i_mapZ {f g : Arrow D} (φ : f ⟶ g) :
    data.i.app f ≫ data.mapZ φ = φ.left ≫ data.i.app g :=
  (data.i.naturality φ).symm

/-- The second original map commutes with that same actual comparison. -/
@[reassoc (attr := simp)]
theorem mapZ_p {f g : Arrow D} (φ : f ⟶ g) :
    data.mapZ φ ≫ data.p.app g = data.p.app f ≫ φ.right :=
  data.p.naturality φ

/-- Enlarging factor classes preserves the source restriction and the actual maps. -/
def ofLE {left' right' : MorphismProperty D}
    (hleft : left ≤ left') (hright : right ≤ right') :
    SourceRestrictedFunctorialFactorizationData left' right' source where
  Z := data.Z
  i := data.i
  p := data.p
  fac := data.fac
  hi f h := hleft _ (data.hi f h)
  hp f h := hright _ (data.hp f h)

end SourceRestrictedFunctorialFactorizationData

/-- The actual semi-model axioms on a bicomplete carrier, with both source restrictions. -/
structure SemiModelCategoryData (D : Type u) [Category.{v} D] [HasInitial D] where
  /-- Completeness of the original carrier at the working size. -/
  complete : HasLimitsOfSize.{w, w} D
  /-- Cocompleteness of that same original carrier. -/
  cocomplete : HasColimitsOfSize.{w, w} D
  /-- The chosen weak-equivalence class. -/
  weakEquivalences : MorphismProperty D
  /-- The chosen fibration class. -/
  fibrations : MorphismProperty D
  /-- The chosen cofibration class. -/
  cofibrations : MorphismProperty D
  /-- Weak equivalences have the complete two-out-of-three property. -/
  weak_twoOutOfThree : weakEquivalences.HasTwoOutOfThreeProperty
  /-- Weak equivalences are closed under actual arrow retracts. -/
  weak_retracts : weakEquivalences.IsStableUnderRetracts
  /-- Fibrations are closed under those same retracts. -/
  fibration_retracts : fibrations.IsStableUnderRetracts
  /-- Cofibrations are the full left lifting class against trivial fibrations. -/
  cofibration_eq_llp : cofibrations = (fibrations ⊓ weakEquivalences).llp
  /-- Every original arrow has a functorial cofibration/trivial-fibration factorization. -/
  cofibrationFactorization :
    FunctorialFactorizationData cofibrations (fibrations ⊓ weakEquivalences)
  /-- Trivial cofibrations with intrinsically cofibrant source lift against all fibrations. -/
  trivialCofibration_lifting {X Y K L : D} (i : X ⟶ Y) (p : K ⟶ L) :
    IntrinsicCofibrant cofibrations X →
      (cofibrations ⊓ weakEquivalences) i → fibrations p → HasLiftingProperty i p
  /-- The other actual functorial factorization retains intrinsic source cofibrancy. -/
  trivialCofibrationFactorization :
    SourceRestrictedFunctorialFactorizationData (cofibrations ⊓ weakEquivalences)
      fibrations (IntrinsicCofibrant cofibrations)
  /-- Fibrations are closed under actual pullback squares. -/
  fibration_pullbacks : fibrations.IsStableUnderBaseChange
  /-- Trivial fibrations are closed under those same pullback squares. -/
  trivialFibration_pullbacks : (fibrations ⊓ weakEquivalences).IsStableUnderBaseChange

namespace SemiModelCategoryData

variable [HasInitial D] (data : SemiModelCategoryData.{w} D)

/-- The chosen trivial-fibration class is the original full intersection. -/
abbrev trivialFibrations : MorphismProperty D := data.fibrations ⊓ data.weakEquivalences

/-- The chosen trivial-cofibration class is the original full intersection. -/
abbrev trivialCofibrations : MorphismProperty D := data.cofibrations ⊓ data.weakEquivalences

/-- Cofibrancy refers to the original initial arrow in this carrier. -/
abbrev IsCofibrant (X : D) : Prop := IntrinsicCofibrant data.cofibrations X

/-- Cofibrations lift against all actual trivial fibrations, without a source restriction. -/
theorem cofibration_lifting {X Y K L : D} (i : X ⟶ Y) (p : K ⟶ L)
    (hi : data.cofibrations i) (hp : data.trivialFibrations p) : HasLiftingProperty i p := by
  rw [data.cofibration_eq_llp] at hi
  exact hi p hp

/-- Cofibrations satisfy the retract axiom. -/
theorem cofibration_retracts : data.cofibrations.IsStableUnderRetracts := by
  rw [data.cofibration_eq_llp]
  infer_instance

/-- The actual initial object is intrinsically cofibrant. -/
theorem initial_isCofibrant : data.IsCofibrant (⊥_ D) := by
  unfold IsCofibrant IntrinsicCofibrant
  rw [data.cofibration_eq_llp]
  have h : initial.to (⊥_ D) = 𝟙 (⊥_ D) := Subsingleton.elim _ _
  rw [h]
  exact llp_of_isIso _ _

/-- A cofibration with intrinsically cofibrant source has intrinsically cofibrant target. -/
theorem isCofibrant_of_cofibration {X Y : D} (i : X ⟶ Y)
    (hX : data.IsCofibrant X) (hi : data.cofibrations i) : data.IsCofibrant Y := by
  unfold IsCofibrant IntrinsicCofibrant at hX ⊢
  rw [data.cofibration_eq_llp] at hX hi ⊢
  rw [Subsingleton.elim (initial.to Y) (initial.to X ≫ i)]
  exact (data.fibrations ⊓ data.weakEquivalences).llp.comp_mem _ _ hX hi

end SemiModelCategoryData

end HomotopicalAlgebra
