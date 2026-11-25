/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.UnitLaws

/-!
# Associativity for colored operads

This file constructs the two substitution routes associated to a three-level colored substitution
shape. Both routes begin at the same unbiased finite tensor and end at the operation object of the
nested total profile.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe w v u

namespace ColoredOperadObj.AssocInsertion

variable {Color : Type u} {V : Type w} [Category.{v} V]

/-- Grouping A: the root operation is a singleton block and every branch contributes its complete
substitution-factor family. -/
def groupingA (O : ColoredSymmetricCollection Color V) (d : ColoredAssocData Color) :
    FiniteFamily (FiniteFamily V) where
  index := FintypeCat.of (Option d.branches.index)
  obj
    | none => (FiniteFamily.singleton (C := V)).obj (O.obj d.middleData.outerProfile)
    | some i => (ColoredOperadObj.substitutionFactors O).obj (d.localData i)

/-- Grouping B: the root block contains the factors of the middle substitution, while every
innermost operation is a singleton block. -/
def groupingB (O : ColoredSymmetricCollection Color V) (d : ColoredAssocData Color) :
    FiniteFamily (FiniteFamily V) where
  index := FintypeCat.of (Option d.middleData.totalProfile.inputs)
  obj
    | none => (ColoredOperadObj.substitutionFactors O).obj d.middleData
    | some p => (FiniteFamily.singleton (C := V)).obj (O.obj (d.innerData.inner.obj p))

/-- Flattened grouping A. -/
def flattenedGroupingA (O : ColoredSymmetricCollection Color V) (d : ColoredAssocData Color) :
    FiniteFamily V :=
  (FiniteFamily.flatten (C := V)).obj (groupingA O d)

/-- Flattened grouping B. -/
def flattenedGroupingB (O : ColoredSymmetricCollection Color V) (d : ColoredAssocData Color) :
    FiniteFamily V :=
  (FiniteFamily.flatten (C := V)).obj (groupingB O d)

/-- Identify the two flattened factor families used by associativity. -/
def flattenAToFlattenBHom (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) : flattenedGroupingA O d ⟶ flattenedGroupingB O d where
  equiv :=
    { toFun := fun x =>
        match x with
        | ⟨none, _⟩ => ⟨none, none⟩
        | ⟨some i, none⟩ => ⟨none, some i⟩
        | ⟨some i, some j⟩ => ⟨some ⟨i, j⟩, PUnit.unit⟩
      invFun := fun y =>
        match y with
        | ⟨none, none⟩ => ⟨none, PUnit.unit⟩
        | ⟨none, some i⟩ => ⟨some i, none⟩
        | ⟨some ⟨i, j⟩, _⟩ => ⟨some i, some j⟩
      left_inv := fun x => by
        rcases x with ⟨o, a⟩
        cases o with
        | none => cases a; rfl
        | some i =>
            cases a with
            | none => rfl
            | some _ => rfl
      right_inv := fun y => by
        rcases y with ⟨o, a⟩
        cases o with
        | none =>
            cases a with
            | none => rfl
            | some _ => rfl
        | some p =>
            rcases p with ⟨_, _⟩
            cases a
            rfl }
  hom := fun x =>
    match x with
    | ⟨none, _⟩ => 𝟙 _
    | ⟨some _, none⟩ => 𝟙 _
    | ⟨some _, some _⟩ => 𝟙 _

/-- After applying every local substitution, map the resulting blocks to the factor family for the
outer-after-inner datum. -/
def groupingAToFactorsHom [FiniteTensor V] (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O) (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj (groupingA O d) ⟶
      (ColoredOperadObj.substitutionFactors O).obj d.outerAfterInnerData where
  equiv := Equiv.refl _
  hom := fun o =>
    match o with
    | none => (FiniteTensor.singletonIso (V := V)).hom.app (O.obj d.middleData.outerProfile)
    | some i => γ.app (d.localData i)

/-- The grouping-A factor hom is the identity on block indices. -/
@[simp]
theorem groupingAToFactorsHom_equiv [FiniteTensor V]
    (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O)
    (d : ColoredAssocData Color) :
    (groupingAToFactorsHom O γ d).equiv = Equiv.refl _ :=
  rfl

/-- The root block collapses the singleton tensor. -/
@[simp]
theorem groupingAToFactorsHom_hom_none [FiniteTensor V]
    (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O)
    (d : ColoredAssocData Color) :
    (groupingAToFactorsHom O γ d).hom none =
      (FiniteTensor.singletonIso (V := V)).hom.app
        (O.obj d.middleData.outerProfile) :=
  rfl

/-- Each child block runs its local substitution. -/
@[simp]
theorem groupingAToFactorsHom_hom_some [FiniteTensor V]
    (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O)
    (d : ColoredAssocData Color) (i : d.branches.index) :
    (groupingAToFactorsHom O γ d).hom (some i) =
      γ.app (d.localData i) :=
  rfl

/-- After the middle substitution, map the resulting blocks to the factor family for the flat
inner datum. -/
def groupingBToFactorsHom [FiniteTensor V] (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O) (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj (groupingB O d) ⟶
      (ColoredOperadObj.substitutionFactors O).obj d.innerData where
  equiv := Equiv.refl _
  hom := fun o =>
    match o with
    | none => γ.app d.middleData
    | some p => (FiniteTensor.singletonIso (V := V)).hom.app (O.obj (d.innerData.inner.obj p))

end ColoredOperadObj.AssocInsertion

namespace ColoredOperadObj

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- Common source for the two colored associativity routes. -/
def associativityCommonSource (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) : V :=
  (FiniteTensor.tensor (V := V)).obj (AssocInsertion.flattenedGroupingA O d)

/-- First substitute inside every branch, then substitute the resulting operations at the root. -/
noncomputable def associativityRouteA (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O) (d : ColoredAssocData Color) :
    associativityCommonSource O d ⟶ O.obj d.outerAfterInnerData.totalProfile :=
  (FiniteTensor.flattenIso (V := V)).hom.app (AssocInsertion.groupingA O d) ≫
    (FiniteTensor.tensor (V := V)).map (AssocInsertion.groupingAToFactorsHom O γ d) ≫
      γ.app d.outerAfterInnerData

/-- First substitute at the root, then substitute all innermost operations, and finally apply the
canonical dependent-sum associator to the total profile. -/
noncomputable def associativityRouteB (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O) (d : ColoredAssocData Color) :
    associativityCommonSource O d ⟶ O.obj d.outerAfterInnerData.totalProfile :=
  (FiniteTensor.tensor (V := V)).map (AssocInsertion.flattenAToFlattenBHom O d) ≫
    (FiniteTensor.flattenIso (V := V)).hom.app (AssocInsertion.groupingB O d) ≫
      (FiniteTensor.tensor (V := V)).map (AssocInsertion.groupingBToFactorsHom O γ d) ≫
        γ.app d.innerData ≫ O.map d.totalHom

/-- Associativity of a colored substitution operation. -/
def IsAssociative (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O) : Prop :=
  ∀ d : ColoredAssocData Color, associativityRouteA O γ d = associativityRouteB O γ d

end ColoredOperadObj

end CategoryTheory.Operad
