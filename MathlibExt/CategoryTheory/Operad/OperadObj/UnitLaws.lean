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

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorReindexShapes
public import MathlibExt.CategoryTheory.Operad.OperadObj.Unit
public import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Logic.Equiv.Prod

/-!
# Right and left unit laws for enriched operads via unbiased finite tensors

Substitution operation, right/left unit data, total-arity isomorphisms,
insertion morphisms, and unit predicates.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe v u

/-- Substitution operation as natural transformations
`substitutionSource O ⟶ substitutionTarget O`. -/
abbrev OperadSubstitution {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) :=
  substitutionSource O ⟶ substitutionTarget O

/-- Right unit data: outer index `I`, inner arities `arityOne`. -/
def rightUnitData (I : FintypeCat) : SubstitutionData where
  index := I
  obj := fun _ => ⟨arityOne⟩

/-- Left unit data: outer index `arityOne`, inner arity `J`. -/
def leftUnitData (J : FintypeCat) : SubstitutionData where
  index := arityOne
  obj := fun _ => ⟨J⟩

/-- Right total iso: `substitutionTotalObj (rightUnitData I) ≅ I`
via `(Σ _ : I, PUnit) ≃ I`. -/
def rightUnitTotalIso (I : FintypeCat) :
    substitutionTotalObj (rightUnitData I) ≅ I :=
  FintypeCat.equivEquivIso (Equiv.sigmaPUnit (I : Type))

/-- Left total iso: `substitutionTotalObj (leftUnitData J) ≅ J`
via `(Σ _ : PUnit, J) ≃ J`. -/
def leftUnitTotalIso (J : FintypeCat) :
    substitutionTotalObj (leftUnitData J) ≅ J :=
  let e := (Equiv.sigmaEquivProd PUnit (J : Type)).trans (Equiv.punitProd (J : Type))
  FintypeCat.equivEquivIso e

/-! Insertion implementation helpers for unit laws.
These definitions are forced public in Lean 4.33 because the public
`rightUnitInsert` and `leftUnitInsert` may not depend on file-private constants. -/
namespace UnitInsertion

/-- Nested family for right insertion: `Option I` with singleton at none and empty at some. -/
def rightNestedFamily {V : Type u} [Category.{v} V] (c : V) (I : FintypeCat) :
    FiniteFamily (FiniteFamily V) where
  index := FintypeCat.of (Option (I : Type))
  obj := fun o =>
    match o with
    | none => (FiniteFamily.singleton (C := V)).obj c
    | some _ => FiniteFamily.empty

/-- Flatten of `rightNestedFamily`. -/
def rightFlattenObj {V : Type u} [Category.{v} V] (c : V) (I : FintypeCat) :
    FiniteFamily V :=
  (FiniteFamily.flatten (C := V)).obj (rightNestedFamily c I)

/-- Hom `singleton c ⟶ rightFlattenObj c I` via `PUnit ≃` total. -/
def rightSingletonToFlatten {V : Type u} [Category.{v} V] (c : V) (I : FintypeCat) :
    (FiniteFamily.singleton (C := V)).obj c ⟶ rightFlattenObj c I where
  equiv :=
    { toFun := fun _ => ⟨none, PUnit.unit⟩
      invFun := fun _ => PUnit.unit
      left_inv := by
        intro x
        cases x with
        | unit => rfl
      right_inv := by
        intro x
        obtain ⟨a, b⟩ := x
        cases a with
        | none =>
          cases b with
          | unit => rfl
        | some _ =>
          cases b }
  hom := fun _ => 𝟙 c

/-- Map-tensor family for right insertion. -/
def rightTensorFamily {V : Type u} [Category.{v} V] [FiniteTensor V] (c : V)
    (I : FintypeCat) : FiniteFamily V :=
  (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj (rightNestedFamily c I)

/-- Hom `rightTensorFamily (O.eval I) I ⟶ substitutionFactors O (rightUnitData I)`. -/
def rightFactorHom {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (η : OperadUnit O) (I : FintypeCat) :
    rightTensorFamily (O.eval I) I ⟶ (substitutionFactors O).obj (rightUnitData I) where
  equiv := Equiv.refl (Option (I : Type))
  hom := fun o =>
    match o with
    | none => (FiniteTensor.singletonIso (V := V)).hom.app (O.eval I)
    | some _ => η

/-- The color-independent coherence prefix of right-unit insertion. -/
noncomputable def rightInsertPrefix {V : Type u} [Category.{v} V] [FiniteTensor V]
    (c : V) (I : FintypeCat) :
    c ⟶ (FiniteTensor.tensor (V := V)).obj (rightTensorFamily c I) :=
  (FiniteTensor.singletonIso (V := V)).inv.app c ≫
    (FiniteTensor.tensor (V := V)).map (rightSingletonToFlatten c I) ≫
      (FiniteTensor.flattenIso (V := V)).hom.app (rightNestedFamily c I)

/-- Build a right-unit-shaped insertion from a map out of the canonical tensor family. -/
noncomputable def rightInsertFromFactor {V : Type u} [Category.{v} V] [FiniteTensor V]
    (c : V) (I : FintypeCat) {F : FiniteFamily V} (f : rightTensorFamily c I ⟶ F) :
    c ⟶ (FiniteTensor.tensor (V := V)).obj F :=
  rightInsertPrefix c I ≫ (FiniteTensor.tensor (V := V)).map f

@[reassoc]
theorem rightInsertFromFactor_comp {V : Type u} [Category.{v} V] [FiniteTensor V]
    (c : V) (I : FintypeCat) {F G : FiniteFamily V}
    (f : rightTensorFamily c I ⟶ F) (g : F ⟶ G) :
    rightInsertFromFactor c I f ≫ (FiniteTensor.tensor (V := V)).map g =
      rightInsertFromFactor c I (f ≫ g) := by
  simp [rightInsertFromFactor, Category.assoc]

/-- Nested family for left insertion: `Option PUnit` with empty at
none and singleton at some. Canonicalized on the o12b reindexing
shape to avoid a drifting duplicate API. -/
abbrev leftNestedFamily {V : Type u} [Category.{v} V] (c : V) :
    FiniteFamily (FiniteFamily V) :=
  reindexUnitInsertFam c

/-- Flatten of `leftNestedFamily`. -/
def leftFlattenObj {V : Type u} [Category.{v} V] (c : V) : FiniteFamily V :=
  (FiniteFamily.flatten (C := V)).obj (leftNestedFamily c)

/-- Hom `singleton c ⟶ leftFlattenObj c` via `PUnit ≃` total. -/
def leftSingletonToFlatten {V : Type u} [Category.{v} V] (c : V) :
    (FiniteFamily.singleton (C := V)).obj c ⟶ leftFlattenObj c where
  equiv :=
    { toFun := fun _ => ⟨some PUnit.unit, PUnit.unit⟩
      invFun := fun _ => PUnit.unit
      left_inv := by
        intro x
        cases x with
        | unit => rfl
      right_inv := by
        intro x
        obtain ⟨a, b⟩ := x
        cases a with
        | none =>
          cases b
        | some _ =>
          cases b with
          | unit => rfl }
  hom := fun _ => 𝟙 c

/-- Map-tensor family for left insertion. Canonicalized on the o12b
reindexing shape to avoid a drifting duplicate API. -/
abbrev leftTensorFamily {V : Type u} [Category.{v} V] [FiniteTensor V]
    (c : V) : FiniteFamily V :=
  reindexUnitTargetFam c

/-- Hom `leftTensorFamily (O.eval J) ⟶ substitutionFactors O (leftUnitData J)`. -/
def leftFactorHom {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (η : OperadUnit O) (J : FintypeCat) :
    leftTensorFamily (O.eval J) ⟶ (substitutionFactors O).obj (leftUnitData J) where
  equiv := Equiv.refl (Option PUnit)
  hom := fun o =>
    match o with
    | none => η
    | some _ => (FiniteTensor.singletonIso (V := V)).hom.app (O.eval J)

/-- The color-independent coherence prefix of left-unit insertion. -/
noncomputable def leftInsertPrefix {V : Type u} [Category.{v} V] [FiniteTensor V]
    (c : V) : c ⟶ (FiniteTensor.tensor (V := V)).obj (leftTensorFamily c) :=
  (FiniteTensor.singletonIso (V := V)).inv.app c ≫
    (FiniteTensor.tensor (V := V)).map (leftSingletonToFlatten c) ≫
      (FiniteTensor.flattenIso (V := V)).hom.app (leftNestedFamily c)

/-- Build a left-unit-shaped insertion from a map out of the canonical tensor family. -/
noncomputable def leftInsertFromFactor {V : Type u} [Category.{v} V] [FiniteTensor V]
    (c : V) {F : FiniteFamily V} (f : leftTensorFamily c ⟶ F) :
    c ⟶ (FiniteTensor.tensor (V := V)).obj F :=
  leftInsertPrefix c ≫ (FiniteTensor.tensor (V := V)).map f

@[reassoc]
theorem leftInsertFromFactor_comp {V : Type u} [Category.{v} V] [FiniteTensor V]
    (c : V) {F G : FiniteFamily V} (f : leftTensorFamily c ⟶ F) (g : F ⟶ G) :
    leftInsertFromFactor c f ≫ (FiniteTensor.tensor (V := V)).map g =
      leftInsertFromFactor c (f ≫ g) := by
  simp [leftInsertFromFactor, Category.assoc]

end UnitInsertion

/-- Right insertion from unbiased coherence:
`O.eval I ⟶ (substitutionSource O).obj (rightUnitData I)`. -/
noncomputable def rightUnitInsert {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (η : OperadUnit O) (I : FintypeCat) :
    O.eval I ⟶ (substitutionSource O).obj (rightUnitData I) :=
  (FiniteTensor.singletonIso (V := V)).inv.app (O.eval I) ≫
    (FiniteTensor.tensor (V := V)).map
      (UnitInsertion.rightSingletonToFlatten (O.eval I) I) ≫
      (FiniteTensor.flattenIso (V := V)).hom.app
        (UnitInsertion.rightNestedFamily (O.eval I) I) ≫
        (FiniteTensor.tensor (V := V)).map (UnitInsertion.rightFactorHom O η I)

theorem rightUnitInsert_eq_insertFromFactor {V : Type u}
    [Category.{v} V] [FiniteTensor V] (O : SymmetricCollection V)
    (η : OperadUnit O) (I : FintypeCat) :
    rightUnitInsert O η I =
      UnitInsertion.rightInsertFromFactor (O.eval I) I
        (UnitInsertion.rightFactorHom O η I) := by
  let c := O.eval I
  let N := UnitInsertion.rightNestedFamily c I
  let R := (FiniteFamily.flatten (C := V)).obj N
  let T := (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj N
  let S := (substitutionFactors O).obj (rightUnitData I)
  let a : c ⟶ (FiniteTensor.tensor (V := V)).obj ((FiniteFamily.singleton).obj c) :=
    (FiniteTensor.singletonIso (V := V)).inv.app c
  let b : (FiniteTensor.tensor (V := V)).obj ((FiniteFamily.singleton).obj c) ⟶
      (FiniteTensor.tensor (V := V)).obj R := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := V)).map
        (UnitInsertion.rightSingletonToFlatten c I)
  let h : (FiniteTensor.tensor (V := V)).obj R ⟶
      (FiniteTensor.tensor (V := V)).obj T :=
    (FiniteTensor.flattenIso (V := V)).hom.app N
  let m : (FiniteTensor.tensor (V := V)).obj T ⟶
      (FiniteTensor.tensor (V := V)).obj S := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := V)).map
        (UnitInsertion.rightFactorHom O η I)
  unfold rightUnitInsert UnitInsertion.rightInsertFromFactor UnitInsertion.rightInsertPrefix
  with_unfolding_all change a ≫ b ≫ h ≫ m = (a ≫ b ≫ h) ≫ m
  calc
    a ≫ b ≫ h ≫ m = a ≫ ((b ≫ h) ≫ m) := by
      rw [Category.assoc]
    _ = (a ≫ (b ≫ h)) ≫ m :=
      (Category.assoc a (b ≫ h) m).symm

/-- Left insertion: mirror, empty at none and singleton `O(J)` at some. -/
noncomputable def leftUnitInsert {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (η : OperadUnit O) (J : FintypeCat) :
    O.eval J ⟶ (substitutionSource O).obj (leftUnitData J) :=
  (FiniteTensor.singletonIso (V := V)).inv.app (O.eval J) ≫
    (FiniteTensor.tensor (V := V)).map
      (UnitInsertion.leftSingletonToFlatten (O.eval J)) ≫
      (FiniteTensor.flattenIso (V := V)).hom.app
        (UnitInsertion.leftNestedFamily (O.eval J)) ≫
        (FiniteTensor.tensor (V := V)).map (UnitInsertion.leftFactorHom O η J)

theorem leftUnitInsert_eq_insertFromFactor {V : Type u}
    [Category.{v} V] [FiniteTensor V] (O : SymmetricCollection V)
    (η : OperadUnit O) (J : FintypeCat) :
    leftUnitInsert O η J =
      UnitInsertion.leftInsertFromFactor (O.eval J) (UnitInsertion.leftFactorHom O η J) := by
  let c := O.eval J
  let N := UnitInsertion.leftNestedFamily c
  let R := (FiniteFamily.flatten (C := V)).obj N
  let T := (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj N
  let S := (substitutionFactors O).obj (leftUnitData J)
  let a : c ⟶ (FiniteTensor.tensor (V := V)).obj ((FiniteFamily.singleton).obj c) :=
    (FiniteTensor.singletonIso (V := V)).inv.app c
  let b : (FiniteTensor.tensor (V := V)).obj ((FiniteFamily.singleton).obj c) ⟶
      (FiniteTensor.tensor (V := V)).obj R := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := V)).map
        (UnitInsertion.leftSingletonToFlatten c)
  let h : (FiniteTensor.tensor (V := V)).obj R ⟶
      (FiniteTensor.tensor (V := V)).obj T :=
    (FiniteTensor.flattenIso (V := V)).hom.app N
  let m : (FiniteTensor.tensor (V := V)).obj T ⟶
      (FiniteTensor.tensor (V := V)).obj S := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := V)).map
        (UnitInsertion.leftFactorHom O η J)
  unfold leftUnitInsert UnitInsertion.leftInsertFromFactor UnitInsertion.leftInsertPrefix
  with_unfolding_all change a ≫ b ≫ h ≫ m = (a ≫ b ≫ h) ≫ m
  calc
    a ≫ b ≫ h ≫ m = a ≫ ((b ≫ h) ≫ m) := by
      rw [Category.assoc]
    _ = (a ≫ (b ≫ h)) ≫ m :=
      (Category.assoc a (b ≫ h) m).symm

/-- Right unit law: insertion, `γ.app`, and relabel by `rightUnitTotalIso` = identity. -/
def IsRightUnit {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (η : OperadUnit O) (γ : OperadSubstitution O) : Prop :=
  ∀ (I : FintypeCat),
    rightUnitInsert O η I ≫ γ.app (rightUnitData I) ≫
      O.relabelIso (rightUnitTotalIso I) = 𝟙 (O.eval I)

/-- Left unit law: insertion, `γ.app`, and relabel by `leftUnitTotalIso` = identity. -/
def IsLeftUnit {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) (η : OperadUnit O) (γ : OperadSubstitution O) : Prop :=
  ∀ (J : FintypeCat),
    leftUnitInsert O η J ≫ γ.app (leftUnitData J) ≫
      O.relabelIso (leftUnitTotalIso J) = 𝟙 (O.eval J)

end CategoryTheory.Operad
