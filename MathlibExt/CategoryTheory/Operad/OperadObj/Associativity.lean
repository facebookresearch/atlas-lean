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

public import MathlibExt.CategoryTheory.Operad.OperadObj.UnitLaws
import Mathlib.Logic.Equiv.Defs

/-!
# Associativity data for enriched operads via unbiased finite tensors

Three-level arities, common flat source via two groupings, and associativity predicate.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe v u

/-- Three-level associativity arities: outer, middle fibers, inner fibers. -/
structure AssocData where
  /-- Outer finite type. -/
  outer : FintypeCat.{0}
  /-- Middle fibers over outer. -/
  middle : outer → FintypeCat.{0}
  /-- Inner fibers over total middle. -/
  inner : ((i : outer) × middle i) → FintypeCat.{0}

namespace AssocData

/-- Middle layer as substitution data: outer index `outer`, fibers `middle`. -/
def middleData (d : AssocData) : SubstitutionData where
  index := d.outer
  obj i := ⟨d.middle i⟩

/-- Local data at `i : outer`: outer `middle i`, fibers `inner ⟨i, _⟩`. -/
def localData (d : AssocData) (i : d.outer) : SubstitutionData where
  index := d.middle i
  obj j := ⟨d.inner ⟨i, j⟩⟩

/-- Substitution data after inner substitution in each middle fiber:
outer `d.outer`, fiber `total (localData i)`. -/
def outerAfterInnerData (d : AssocData) : SubstitutionData where
  index := d.outer
  obj i := ⟨substitutionTotalObj (d.localData i)⟩

/-- Flat inner substitution data: outer `total middleData`,
fiber `inner` at each total point. -/
def innerData (d : AssocData) : SubstitutionData where
  index := substitutionTotalObj d.middleData
  obj p := ⟨d.inner p⟩

/-- Total-arity isomorphism from flat Sigma-pair total to nested total:
`Σ (Σ outer middle) inner  ≅  Σ outer (Σ middle inner)`,
via dependent-sum associativity. Direction is flat to nested. -/
def totalIso (d : AssocData) :
    substitutionTotalObj d.innerData ≅ substitutionTotalObj d.outerAfterInnerData :=
  FintypeCat.equivEquivIso
    (Equiv.sigmaAssoc (fun (i : d.outer) (j : d.middle i) => (d.inner ⟨i, j⟩ : Type)))

end AssocData

/-! Forced-public helpers for associativity insertion.

These are forced public in Lean 4.33 because the public routes depend on file-private
constants. All names are contained in `AssocInsertion`. -/
namespace AssocInsertion

/-- Grouping A: indexed by `Option d.outer`, with `none` carrying a singleton
`O(d.outer)` and `some i` carrying the substitution factors of `localData i`. -/
def groupingA {V : Type u} [Category.{v} V]
    (O : SymmetricCollection V) (d : AssocData) :
    FiniteFamily (FiniteFamily V) where
  index := FintypeCat.of (Option (d.outer : Type))
  obj
  | none => (FiniteFamily.singleton (C := V)).obj (O.eval d.outer)
  | some i => (substitutionFactors O).obj (d.localData i)

/-- `groupingA` at `none` evaluates to the singleton family on `O.eval d.outer`. -/
@[simp]
theorem groupingA_obj_none {V : Type u} [Category.{v} V]
    (O : SymmetricCollection V) (d : AssocData) :
    (groupingA O d).obj (none : Option (d.outer : Type)) =
      (FiniteFamily.singleton (C := V)).obj (O.eval d.outer) :=
  rfl

/-- `groupingA` at `some i` evaluates to the substitution factors of `d.localData i`. -/
@[simp]
theorem groupingA_obj_some {V : Type u} [Category.{v} V]
    (O : SymmetricCollection V) (d : AssocData) (i : d.outer) :
    (groupingA O d).obj (some i : Option (d.outer : Type)) =
      (substitutionFactors O).obj (d.localData i) :=
  rfl

/-- Grouping B: indexed by `Option (total middleData)`, with `none` carrying
the substitution factors of `middleData` and `some p` carrying a singleton
`O(d.inner p)`. -/
def groupingB {V : Type u} [Category.{v} V]
    (O : SymmetricCollection V) (d : AssocData) :
    FiniteFamily (FiniteFamily V) :=
  let _htotal : Finite (substitutionTotalObj d.middleData : Type) :=
    (substitutionTotalObj d.middleData).property
  { index := FintypeCat.of (Option (substitutionTotalObj d.middleData : Type))
    obj := fun o =>
      match o with
      | none => (substitutionFactors O).obj d.middleData
      | some p => (FiniteFamily.singleton (C := V)).obj (O.eval (d.inner p)) }

/-- Flattened grouping A: `flatten (groupingA O d)`. -/
def flattenedGroupingA {V : Type u} [Category.{v} V]
    (O : SymmetricCollection V) (d : AssocData) : FiniteFamily V :=
  (FiniteFamily.flatten (C := V)).obj (groupingA O d)

/-- Flattened grouping B: `flatten (groupingB O d)`. -/
def flattenedGroupingB {V : Type u} [Category.{v} V]
    (O : SymmetricCollection V) (d : AssocData) : FiniteFamily V :=
  (FiniteFamily.flatten (C := V)).obj (groupingB O d)

/-- Identity-component hom from flattened A to flattened B.

Mapping of flattened indices:
- `A(none, unit)` ↦ `B(none, none)` both `O(outer)`
- `A(some i, none)` ↦ `B(none, some i)` both `O(middle i)`
- `A(some i, some j)` ↦ `B(some ⟨i, j⟩, unit)` both `O(inner ⟨i,j⟩)`

Inverse splits accordingly, with identity component morphisms. -/
def flattenAToFlattenBHom {V : Type u} [Category.{v} V]
    (O : SymmetricCollection V) (d : AssocData) :
    flattenedGroupingA O d ⟶ flattenedGroupingB O d where
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
      left_inv := by
        intro x
        rcases x with ⟨a, b⟩
        cases a with
        | none =>
          cases b
          rfl
        | some i =>
          cases b with
          | none => rfl
          | some _ => rfl
      right_inv := by
        intro y
        rcases y with ⟨a, b⟩
        cases a with
        | none =>
          cases b with
          | none => rfl
          | some _ => rfl
        | some ab =>
          rcases ab with ⟨_, _⟩
          cases b
          rfl }
  hom := fun x =>
    match x with
    | ⟨none, _⟩ => 𝟙 _
    | ⟨some _, none⟩ => 𝟙 _
    | ⟨some _, some _⟩ => 𝟙 _

/-- Family hom for route A: `map-tensor groupingA ⟶ substitutionFactors outerAfterInnerData`.

- `none` component: `singletonIso.hom.app (O.eval d.outer)`
- `some i` component: `gamma.app (localData i)` -/
def groupingAToFactorsHom {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (γ : OperadSubstitution O) (d : AssocData) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj (groupingA O d) ⟶
      (substitutionFactors O).obj d.outerAfterInnerData where
  equiv := Equiv.refl _
  hom := fun o =>
    match o with
    | none => (FiniteTensor.singletonIso (V := V)).hom.app (O.eval d.outer)
    | some i => γ.app (d.localData i)

/-- Family hom for route B: `map-tensor groupingB ⟶ substitutionFactors innerData`.

- `none` component: `gamma.app middleData`
- `some p` component: `singletonIso.hom.app (O.eval (inner p))` -/
def groupingBToFactorsHom {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (γ : OperadSubstitution O) (d : AssocData) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj (groupingB O d) ⟶
      (substitutionFactors O).obj d.innerData where
  equiv := Equiv.refl _
  hom := fun o =>
    match o with
    | none => γ.app d.middleData
    | some p => (FiniteTensor.singletonIso (V := V)).hom.app (O.eval (d.inner p))

end AssocInsertion

/-- Common source for associativity: tensor of flattened grouping A. -/
def associativityCommonSource {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (d : AssocData) : V :=
  (FiniteTensor.tensor (V := V)).obj (AssocInsertion.flattenedGroupingA O d)

/-- Route A: apply local substitutions, then outer substitution.

1. `flattenIso.hom.app groupingA`
2. `tensor.map` of family hom with `singletonIso` at none and `gamma` at some
3. `gamma.app outerAfterInnerData` -/
noncomputable def associativityRouteA {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (γ : OperadSubstitution O) (d : AssocData) :
    associativityCommonSource O d ⟶ O.eval (substitutionTotalObj d.outerAfterInnerData) :=
  (FiniteTensor.flattenIso (V := V)).hom.app (AssocInsertion.groupingA O d) ≫
    (FiniteTensor.tensor (V := V)).map (AssocInsertion.groupingAToFactorsHom O γ d) ≫
      γ.app d.outerAfterInnerData

/-- Route B: apply outer substitution, then flat inner substitution, then relabel.

1. `tensor.map` flattenA-to-flattenB hom
2. `flattenIso.hom.app groupingB`
3. `tensor.map` of family hom with `gamma` at none and `singletonIso` at some
4. `gamma.app innerData`
5. `O.relabelIso totalIso` -/
noncomputable def associativityRouteB {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (γ : OperadSubstitution O) (d : AssocData) :
    associativityCommonSource O d ⟶ O.eval (substitutionTotalObj d.outerAfterInnerData) :=
  (FiniteTensor.tensor (V := V)).map (AssocInsertion.flattenAToFlattenBHom O d) ≫
    (FiniteTensor.flattenIso (V := V)).hom.app (AssocInsertion.groupingB O d) ≫
      (FiniteTensor.tensor (V := V)).map (AssocInsertion.groupingBToFactorsHom O γ d) ≫
        γ.app d.innerData ≫ O.relabelIso d.totalIso

/-- Associativity predicate: the two routes from the common source agree for all data. -/
def IsAssociative {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (γ : OperadSubstitution O) : Prop :=
  ∀ d : AssocData, associativityRouteA O γ d = associativityRouteB O γ d

end CategoryTheory.Operad
