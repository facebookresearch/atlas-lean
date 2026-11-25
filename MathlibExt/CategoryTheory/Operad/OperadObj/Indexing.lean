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

public import MathlibExt.CategoryTheory.Operad.Collection
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensor
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Option
import Mathlib.Basic.Finite.Sigma
public import Mathlib.Data.Fintype.Option

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe v u

/-- Substitution data: a finite family of finite bijection groupoid objects.

The index is the outer arity; each fiber is an inner arity. -/
abbrev SubstitutionData :=
  FiniteFamily FinBijGroupoid

/-- The small unary arity `PUnit` as a bundled finite type. -/
def arityOne : FintypeCat.{0} :=
  FintypeCat.of PUnit

/-- Total finite type underlying the dependent sum of fibers in `X`. -/
def substitutionTotalObj (X : SubstitutionData) : FintypeCat.{0} :=
  let total : Type := (a : X.index) × (X.obj a).of
  haveI : Finite X.index := X.index.property
  haveI : (a : X.index) → Finite (X.obj a).of := fun a => (X.obj a).of.property
  haveI : Finite total := by infer_instance
  FintypeCat.of total

/-- Total arity functor: sends a substitution datum to the dependent sum of its
inner arities. -/
def substitutionTotal : SubstitutionData ⥤ FinBijGroupoid where
  obj X := ⟨substitutionTotalObj X⟩
  map {X Y} f :=
    let eOuter : X.index ≃ Y.index := f.equiv
    let eInner : (i : X.index) → (X.obj i).of ≃ (Y.obj (eOuter i)).of :=
      fun i => FinBijGroupoid.equivOfHom (f.hom i)
    let totalEquiv : ((a : X.index) × (X.obj a).of) ≃ ((b : Y.index) × (Y.obj b).of) :=
      Equiv.sigmaCongr eOuter eInner
    let iso : substitutionTotalObj X ≅ substitutionTotalObj Y :=
      FintypeCat.equivEquivIso totalEquiv
    (Core.isoMk iso).hom
  map_id X := by
    apply Core.hom_ext
    apply FintypeCat.hom_ext
    intro x
    cases x with
    | mk a b =>
      rfl
  map_comp {X Y Z} f g := by
    apply Core.hom_ext
    apply FintypeCat.hom_ext
    intro x
    cases x with
    | mk a b =>
      rfl

/-- Index for substitution factors: outer arity as `none` and inner arities as `some i`. -/
def substitutionFactorIndex (X : SubstitutionData) : FintypeCat.{0} :=
  haveI : Finite X.index := X.index.property
  haveI : Finite (Option X.index) := inferInstance
  FintypeCat.of (Option X.index)

/-- Factor family for a symmetric collection `O` at substitution data `X`. -/
def substitutionFactorObj {V : Type u} [Category.{v} V] (O : SymmetricCollection V)
    (X : SubstitutionData) : substitutionFactorIndex X → V :=
  fun o =>
    match o with
    | none => O.obj ⟨X.index⟩
    | some i => O.obj (X.obj i)

/-- Substitution factors: Option-indexed family consisting of outer plus inner
operations for a symmetric collection `O`. -/
def substitutionFactors {V : Type u} [Category.{v} V]
    (O : SymmetricCollection V) :
    SubstitutionData ⥤ FiniteFamily V where
  obj X :=
    ⟨substitutionFactorIndex X, substitutionFactorObj O X⟩
  map {X Y} f :=
    let e : X.index ≃ Y.index := f.equiv
    let eOpt : Option X.index ≃ Option Y.index := Equiv.optionCongr e
    { equiv := eOpt
      hom := fun o =>
        match o with
        | none => O.map (Core.isoMk (FintypeCat.equivEquivIso e)).hom
        | some i => O.map (f.hom i) }
  map_id X := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro o
      cases o with
      | none => rfl
      | some i => rfl
    · intro o
      cases o with
      | none =>
        have h : (Core.isoMk (FintypeCat.equivEquivIso (Equiv.refl X.index))).hom =
            𝟙 (⟨X.index⟩ : FinBijGroupoid) := by
          apply Core.hom_ext
          apply FintypeCat.hom_ext
          intro x
          rfl
        have h2 : O.map (Core.isoMk (FintypeCat.equivEquivIso (Equiv.refl X.index))).hom =
            𝟙 (O.obj ⟨X.index⟩) := by
          rw [h, O.map_id]
        exact heq_of_eq h2
      | some i =>
        have h2 : O.map (𝟙 (X.obj i)) = 𝟙 (O.obj (X.obj i)) := by simp
        exact heq_of_eq h2
  map_comp {X Y Z} f g := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro o
      cases o with
      | none => rfl
      | some i => rfl
    · intro o
      cases o with
      | none =>
        let fCore : (⟨X.index⟩ : FinBijGroupoid) ⟶ ⟨Y.index⟩ :=
          (Core.isoMk (FintypeCat.equivEquivIso f.equiv)).hom
        let gCore : (⟨Y.index⟩ : FinBijGroupoid) ⟶ ⟨Z.index⟩ :=
          (Core.isoMk (FintypeCat.equivEquivIso g.equiv)).hom
        let fgCore : (⟨X.index⟩ : FinBijGroupoid) ⟶ ⟨Z.index⟩ :=
          (Core.isoMk (FintypeCat.equivEquivIso (f.equiv.trans g.equiv))).hom
        have h_outer : fgCore = fCore ≫ gCore := by
          apply Core.hom_ext
          apply FintypeCat.hom_ext
          intro x
          rfl
        have h_map : O.map fgCore = O.map fCore ≫ O.map gCore := by
          rw [h_outer, O.map_comp]
        exact heq_of_eq h_map
      | some i =>
        have h_map : O.map (f.hom i ≫ g.hom (f.equiv i)) =
            O.map (f.hom i) ≫ O.map (g.hom (f.equiv i)) := by
          rw [O.map_comp]
        exact heq_of_eq h_map

/-- The outer (root) index in the substitution-factor family.

It corresponds to `none` in the underlying `Option` indexing type, but is
provided with the exact bundled-family index type
`((substitutionFactors O).obj X).index` so that clients need not spell the
semireducible `Option` implementation. -/
def substitutionFactorsOuterIndex {V : Type u} [Category.{v} V]
    (O : SymmetricCollection V) (X : SubstitutionData) :
    ((substitutionFactors O).obj X).index :=
  none

/-- The inner index in the substitution-factor family attached to `i : X.index`.

It corresponds to `some i` in the underlying `Option` indexing type, but is
provided with the exact bundled-family index type
`((substitutionFactors O).obj X).index` so that clients need not spell the
semireducible `Option` implementation. -/
def substitutionFactorsInnerIndex {V : Type u} [Category.{v} V]
    (O : SymmetricCollection V) (X : SubstitutionData) (i : X.index) :
    ((substitutionFactors O).obj X).index :=
  some i

/-- Source of substitution: tensor of outer and inner factors. -/
def substitutionSource {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) : SubstitutionData ⥤ V :=
  substitutionFactors O ⋙ FiniteTensor.tensor

/-- Target of substitution: `O` evaluated at the total arity. -/
def substitutionTarget {V : Type u} [Category.{v} V]
    (O : SymmetricCollection V) : SubstitutionData ⥤ V :=
  substitutionTotal ⋙ O

end CategoryTheory.Operad
