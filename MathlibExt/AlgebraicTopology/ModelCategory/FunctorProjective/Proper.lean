/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.SourceConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.Proper

/-!
# Properness of the original ordinary projective models

Coefficient left and right properness are inherited by the actual small-index,
original-index and conventional source constructions. The coefficient
cofibration bound comes from the existing evaluated free-I cell construction,
and its original-index version uses the same full index equivalence as the
model. Every pushout and pullback below retains the original whole natural
transformations and their actual evaluated squares.

This is *Higher Topos Theory*, author version of April 9, 2017, Remark
A.2.8.4, printed page 832 (PDF page 850), extended through the project's
original small-index equivalence. Properness and the diagram model are
outputs of the original constructions.
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uS vS uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.FunctorProjective

section ActualEvaluatedSquares

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C]

/-- Coefficient left properness acts on the actual evaluated pushout squares.
This uses no model structure on the functor category. -/
private theorem objectwiseWeak_cobase [IsLeftProper C] :
    ((weakEquivalences C).functorCategory D).IsStableUnderCobaseChangeAgainst
      ((cofibrations C).functorCategory D) := by
  constructor
  intro A B i hi
  constructor
  intro X Y j f' f sq hf a
  let : Cofibration (((evaluation D C).obj a).map i) :=
    (cofibration_iff _).mpr (hi a)
  let : WeakEquivalence (((evaluation D C).obj a).map f) :=
    (weakEquivalence_iff _).mpr (hf a)
  exact (weakEquivalence_iff _).mp
    (IsLeftProper.weakEquivalence_of_isPushout (sq.map ((evaluation D C).obj a)))

/-- Coefficient right properness acts on the same original pullback maps.
No incoming functor model or target properness is used. -/
private theorem objectwiseWeak_base [IsRightProper C] :
    ((weakEquivalences C).functorCategory D).IsStableUnderBaseChangeAgainst
      ((fibrations C).functorCategory D) := by
  constructor
  intro X Y p hp
  constructor
  intro Z W f' g' g sq hg a
  let : Fibration (((evaluation D C).obj a).map p) :=
    (fibration_iff _).mpr (hp a)
  let : WeakEquivalence (((evaluation D C).obj a).map g) :=
    (weakEquivalence_iff _).mpr (hg a)
  exact (weakEquivalence_iff _).mp
    (IsRightProper.weakEquivalence_of_isPullback (sq.map ((evaluation D C).obj a)))

end ActualEvaluatedSquares

section SmallOriginalModel

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} D] [LocallySmall.{w} D] (d : CofibrantGenerationData C κ)

/-- The actual original small-index projective model inherits left properness.
Its cofibration containment is derived from the original evaluated free cells. -/
theorem modelCategory_isLeftProper [IsLeftProper C] :
    letI : ModelCategory (D ⥤ C) := modelCategory (J := D) d
    IsLeftProper (D ⥤ C) := by
  let : ModelCategory (D ⥤ C) := modelCategory (J := D) d
  constructor
  rw [weakEquivalences_eq d]
  exact (objectwiseWeak_cobase (D := D) (C := C)).of_le
    (cofibrations_le_objectwise d)

/-- The same original small-index projective model inherits right properness. -/
theorem modelCategory_isRightProper [IsRightProper C] :
    letI : ModelCategory (D ⥤ C) := modelCategory (J := D) d
    IsRightProper (D ⥤ C) := by
  let : ModelCategory (D ⥤ C) := modelCategory (J := D) d
  constructor
  rw [weakEquivalences_eq d, fibrations_eq d]
  exact objectwiseWeak_base (D := D) (C := C)

end SmallOriginalModel

namespace EssentialIndex

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} S] [LocallySmall.{w} S] (e : D ≌ S) (d : CofibrantGenerationData C κ)

/-- Actual evaluated free-I cofibrations remain objectwise on the unchanged
original category, through its complete selected index equivalence. -/
theorem cofibrations_le_objectwise :
    letI : ModelCategory (D ⥤ C) := modelCategory e d
    cofibrations (D ⥤ C) ≤ (cofibrations C).functorCategory D := by
  let : ModelCategory (S ⥤ C) := FunctorProjective.modelCategory (J := S) d
  intro F G f hf
  have h := FunctorProjective.cofibrations_le_objectwise (D := S) d
    ((e.congrLeft (E := C)).functor.map f) hf
  exact (functorCategory_inverseImage_congrLeft e (cofibrations C)) ▸ h

/-- Every original-index projective construction inherits coefficient left properness. -/
theorem isLeftProper [IsLeftProper C] :
    letI : ModelCategory (D ⥤ C) := modelCategory e d
    IsLeftProper (D ⥤ C) := by
  let : ModelCategory (D ⥤ C) := modelCategory e d
  constructor
  rw [weakEquivalences_eq e d]
  exact (objectwiseWeak_cobase (D := D) (C := C)).of_le
    (cofibrations_le_objectwise e d)

/-- Every original-index projective construction inherits coefficient right properness. -/
theorem isRightProper [IsRightProper C] :
    letI : ModelCategory (D ⥤ C) := modelCategory e d
    IsRightProper (D ⥤ C) := by
  let : ModelCategory (D ⥤ C) := modelCategory e d
  constructor
  rw [weakEquivalences_eq e d, fibrations_eq e d]
  exact objectwiseWeak_base (D := D) (C := C)

end EssentialIndex

namespace SourceConstruction.FromData

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} D C)

/-- The explicit source constructor derives the full original objectwise cofibration bound. -/
theorem cofibrations_le_objectwise :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    cofibrations (D ⥤ C) ≤ (cofibrations C).functorCategory D := by
  let : LocallySmall.{w} s.index := locallySmall_self s.index
  exact EssentialIndex.cofibrations_le_objectwise s.equivalence d

/-- Explicit coefficient/index sources produce a left proper original model. -/
theorem isLeftProper [IsLeftProper C] :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    IsLeftProper (D ⥤ C) := by
  let : LocallySmall.{w} s.index := locallySmall_self s.index
  exact EssentialIndex.isLeftProper s.equivalence d

/-- Those same sources produce a right proper original model independently. -/
theorem isRightProper [IsRightProper C] :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    IsRightProper (D ⥤ C) := by
  let : LocallySmall.{w} s.index := locallySmall_self s.index
  exact EssentialIndex.isRightProper s.equivalence d

/-- The two coefficient properness assumptions have their separate conclusions
for every actual source rank, bottom and original index choice. -/
theorem properness :
    (IsLeftProper C →
      letI : ModelCategory (D ⥤ C) := modelCategory d s
      IsLeftProper (D ⥤ C)) ∧
    (IsRightProper C →
      letI : ModelCategory (D ⥤ C) := modelCategory d s
      IsRightProper (D ⥤ C)) := by
  constructor
  · intro h
    let : IsLeftProper C := h
    exact isLeftProper d s
  · intro h
    let : IsRightProper C := h
    exact isRightProper d s

/-- Left properness preserves the weak class of the original whole pushed map. -/
theorem weakEquivalence_of_isPushout [IsLeftProper C] {A B X Y : D ⥤ C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    cofibrations (D ⥤ C) i → weakEquivalences (D ⥤ C) f →
      weakEquivalences (D ⥤ C) f' := by
  let : ModelCategory (D ⥤ C) := modelCategory d s
  let : IsLeftProper (D ⥤ C) := isLeftProper d s
  intro hi hf
  let : Cofibration i := (cofibration_iff _).mpr hi
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  exact (weakEquivalence_iff _).mp (IsLeftProper.weakEquivalence_of_isPushout sq)

/-- Right properness preserves the weak class of the original whole pulled map. -/
theorem weakEquivalence_of_isPullback [IsRightProper C] {A B X Y : D ⥤ C}
    {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    fibrations (D ⥤ C) p → weakEquivalences (D ⥤ C) f →
      weakEquivalences (D ⥤ C) f' := by
  let : ModelCategory (D ⥤ C) := modelCategory d s
  let : IsRightProper (D ⥤ C) := isRightProper d s
  intro hp hf
  let : Fibration p := (fibration_iff _).mpr hp
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  exact (weakEquivalence_iff _).mp (IsRightProper.weakEquivalence_of_isPullback sq)

end SourceConstruction.FromData

namespace SourceConstruction

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [IsCombinatorialModelCategory.{w} C]

/-- The conventional public source constructor derives the same original containment. -/
theorem cofibrations_le_objectwise :
    letI : ModelCategory (D ⥤ C) := modelCategory (D := D) (C := C)
    cofibrations (D ⥤ C) ≤ (cofibrations C).functorCategory D := by
  let : Fact (cardinal C).IsRegular := cardinal_regular C
  let : OrderBot (cardinal C).ord.ToType := orderBot C
  exact FromData.cofibrations_le_objectwise (baseData C) (essentialIndex (D := D) (C := C))

/-- Conventional source assumptions produce a left proper projective model. -/
theorem isLeftProper [IsLeftProper C] :
    letI : ModelCategory (D ⥤ C) := modelCategory (D := D) (C := C)
    IsLeftProper (D ⥤ C) := by
  let : Fact (cardinal C).IsRegular := cardinal_regular C
  let : OrderBot (cardinal C).ord.ToType := orderBot C
  exact FromData.isLeftProper (baseData C) (essentialIndex (D := D) (C := C))

/-- Conventional source assumptions independently produce a right proper model. -/
theorem isRightProper [IsRightProper C] :
    letI : ModelCategory (D ⥤ C) := modelCategory (D := D) (C := C)
    IsRightProper (D ⥤ C) := by
  let : Fact (cardinal C).IsRegular := cardinal_regular C
  let : OrderBot (cardinal C).ord.ToType := orderBot C
  exact FromData.isRightProper (baseData C) (essentialIndex (D := D) (C := C))

/-- The exact public original model inherits both coefficient properness implications. -/
theorem properness :
    (IsLeftProper C →
      letI : ModelCategory (D ⥤ C) := modelCategory (D := D) (C := C)
      IsLeftProper (D ⥤ C)) ∧
    (IsRightProper C →
      letI : ModelCategory (D ⥤ C) := modelCategory (D := D) (C := C)
      IsRightProper (D ⥤ C)) := by
  constructor
  · intro h
    let : IsLeftProper C := h
    exact isLeftProper
  · intro h
    let : IsRightProper C := h
    exact isRightProper

end SourceConstruction

end HomotopicalAlgebra.FunctorProjective
