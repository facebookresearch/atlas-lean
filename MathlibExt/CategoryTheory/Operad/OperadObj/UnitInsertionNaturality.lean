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

/-!
# Prefix naturality for unit-law insertions

The right/left insertion prefixes (`rightInsertPrefix`,
`leftInsertPrefix`) are natural in the inserted object: pushing a map
through the prefix yields the prefix followed by the tensor of the
nested-family map. The nested families (`rightNestedFamily`,
`leftNestedFamily`) are made functorial here, and the
singleton-to-flatten inclusions are shown natural. These let
insertion prefixes commute with maps of the inserted object in any
category with the needed tensor structure.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe v u

namespace UnitInsertion

variable {V : Type u} [Category.{v} V]

/-- Functoriality of the right nested family in the inserted object:
singleton-map at the outer block, identity on the empty inner blocks. -/
def rightNestedFamilyMap {c d : V} (f : c ⟶ d) (I : FintypeCat) :
    rightNestedFamily c I ⟶
      rightNestedFamily d I where
  equiv := Equiv.refl (Option (I : Type))
  hom := fun o =>
    match o with
    | none => (FiniteFamily.singleton (C := V)).map f
    | some _ => 𝟙 _

/-- The right nested-family map reindexes trivially. -/
@[simp]
theorem rightNestedFamilyMap_equiv {c d : V} (f : c ⟶ d) (I : FintypeCat) :
    (rightNestedFamilyMap f I).equiv = Equiv.refl (Option (I : Type)) :=
  rfl

/-- Outer block of the right nested-family map. -/
@[simp]
theorem rightNestedFamilyMap_hom_none {c d : V} (f : c ⟶ d)
    (I : FintypeCat) :
    (rightNestedFamilyMap f I).hom none =
      (FiniteFamily.singleton (C := V)).map f :=
  rfl

/-- Inner blocks of the right nested-family map are identities. -/
@[simp]
theorem rightNestedFamilyMap_hom_some {c d : V} (f : c ⟶ d)
    (I : FintypeCat) (i : (I : Type)) :
    (rightNestedFamilyMap f I).hom (some i) = 𝟙 _ :=
  rfl

/-- Functoriality of the left nested family in the inserted object:
identity on the empty outer block, singleton-map at the inner block. -/
def leftNestedFamilyMap {c d : V} (f : c ⟶ d) :
    leftNestedFamily c ⟶
      leftNestedFamily d where
  equiv := Equiv.refl (Option PUnit)
  hom := fun o =>
    match o with
    | none => 𝟙 _
    | some _ => (FiniteFamily.singleton (C := V)).map f

/-- The left nested-family map reindexes trivially. -/
@[simp]
theorem leftNestedFamilyMap_equiv {c d : V} (f : c ⟶ d) :
    (leftNestedFamilyMap f).equiv = Equiv.refl (Option PUnit) :=
  rfl

/-- Outer block of the left nested-family map is the identity. -/
@[simp]
theorem leftNestedFamilyMap_hom_none {c d : V} (f : c ⟶ d) :
    (leftNestedFamilyMap f).hom none = 𝟙 _ :=
  rfl

/-- Inner block of the left nested-family map. -/
@[simp]
theorem leftNestedFamilyMap_hom_some {c d : V} (f : c ⟶ d)
    (u : PUnit) :
    (leftNestedFamilyMap f).hom (some u) =
      (FiniteFamily.singleton (C := V)).map f :=
  rfl

/-- Naturality of the right singleton-to-flatten inclusion. -/
theorem rightSingletonToFlatten_natural {c d : V} (f : c ⟶ d)
    (I : FintypeCat) :
    (FiniteFamily.singleton (C := V)).map f ≫
        rightSingletonToFlatten d I =
      rightSingletonToFlatten c I ≫
        (FiniteFamily.flatten (C := V)).map
          (rightNestedFamilyMap f I) := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro x
    cases x with
    | unit => rfl
  · intro x
    cases x with
    | unit =>
      have e1 : ((FiniteFamily.singleton (C := V)).map f ≫
          rightSingletonToFlatten d I).hom PUnit.unit =
          f ≫ 𝟙 _ := rfl
      have e2 : (rightSingletonToFlatten c I ≫
          (FiniteFamily.flatten (C := V)).map
            (rightNestedFamilyMap f I)).hom PUnit.unit =
          𝟙 _ ≫ f := rfl
      exact heq_of_eq (e1.trans
        ((Category.comp_id _).trans
          ((Category.id_comp _).symm.trans e2.symm)))

/-- Naturality of the left singleton-to-flatten inclusion. -/
theorem leftSingletonToFlatten_natural {c d : V} (f : c ⟶ d) :
    (FiniteFamily.singleton (C := V)).map f ≫
        leftSingletonToFlatten d =
      leftSingletonToFlatten c ≫
        (FiniteFamily.flatten (C := V)).map
          (leftNestedFamilyMap f) := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro x
    cases x with
    | unit => rfl
  · intro x
    cases x with
    | unit =>
      have e1 : ((FiniteFamily.singleton (C := V)).map f ≫
          leftSingletonToFlatten d).hom PUnit.unit =
          f ≫ 𝟙 _ := rfl
      have e2 : (leftSingletonToFlatten c ≫
          (FiniteFamily.flatten (C := V)).map
            (leftNestedFamilyMap f)).hom PUnit.unit =
          𝟙 _ ≫ f := rfl
      exact heq_of_eq (e1.trans
        ((Category.comp_id _).trans
          ((Category.id_comp _).symm.trans e2.symm)))

/-- The right insertion prefix is natural in the inserted object. -/
theorem rightInsertPrefix_natural {c d : V} [FiniteTensor V] (f : c ⟶ d)
    (I : FintypeCat) :
    f ≫ rightInsertPrefix d I =
      rightInsertPrefix c I ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (rightNestedFamilyMap f I)) := by
  have h1 : f ≫ (FiniteTensor.singletonIso (V := V)).inv.app d =
      (FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.singleton (C := V)).map f) := by
    have h := (FiniteTensor.singletonIso (V := V)).inv.naturality f
    simpa using h
  have h2 : (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.singleton (C := V)).map f) ≫
        (FiniteTensor.tensor (V := V)).map
          (rightSingletonToFlatten d I) =
      (FiniteTensor.tensor (V := V)).map
          (rightSingletonToFlatten c I) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flatten (C := V)).map
            (rightNestedFamilyMap f I)) := by
    exact (Functor.map_comp _ _ _).symm.trans
      ((congrArg (FiniteTensor.tensor (V := V)).map
        (rightSingletonToFlatten_natural f I)).trans
        (Functor.map_comp _ _ _))
  have h3 : (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flatten (C := V)).map
            (rightNestedFamilyMap f I)) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (rightNestedFamily d I) =
      (FiniteTensor.flattenIso (V := V)).hom.app
          (rightNestedFamily c I) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (rightNestedFamilyMap f I)) := by
    have h := (FiniteTensor.flattenIso (V := V)).hom.naturality
      (rightNestedFamilyMap f I)
    simpa using h
  change f ≫ ((FiniteTensor.singletonIso (V := V)).inv.app d ≫
      (FiniteTensor.tensor (V := V)).map
        (rightSingletonToFlatten d I) ≫
      (FiniteTensor.flattenIso (V := V)).hom.app
        (rightNestedFamily d I)) =
    ((FiniteTensor.singletonIso (V := V)).inv.app c ≫
      (FiniteTensor.tensor (V := V)).map
        (rightSingletonToFlatten c I) ≫
      (FiniteTensor.flattenIso (V := V)).hom.app
        (rightNestedFamily c I)) ≫
      (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
          (rightNestedFamilyMap f I))
  have step1 : f ≫ ((FiniteTensor.singletonIso (V := V)).inv.app d ≫
        ((FiniteTensor.tensor (V := V)).map
          (rightSingletonToFlatten d I) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (rightNestedFamily d I))) =
      ((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.singleton (C := V)).map f)) ≫
        ((FiniteTensor.tensor (V := V)).map
          (rightSingletonToFlatten d I) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (rightNestedFamily d I)) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ ((FiniteTensor.tensor (V := V)).map
        (rightSingletonToFlatten d I) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (rightNestedFamily d I))) h1)
  have step2 : (((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.singleton (C := V)).map f)) ≫
        (FiniteTensor.tensor (V := V)).map
          (rightSingletonToFlatten d I)) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (rightNestedFamily d I) =
      (((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          (rightSingletonToFlatten c I)) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flatten (C := V)).map
            (rightNestedFamilyMap f I))) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (rightNestedFamily d I) :=
    congrArg (· ≫ (FiniteTensor.flattenIso (V := V)).hom.app
        (rightNestedFamily d I))
      ((Category.assoc _ _ _).trans
        ((congrArg ((FiniteTensor.singletonIso (V := V)).inv.app c ≫ ·)
          h2).trans (Category.assoc _ _ _).symm))
  have step3 : ((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          (rightSingletonToFlatten c I)) ≫
        ((FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flatten (C := V)).map
            (rightNestedFamilyMap f I)) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (rightNestedFamily d I)) =
      ((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          (rightSingletonToFlatten c I)) ≫
        ((FiniteTensor.flattenIso (V := V)).hom.app
          (rightNestedFamily c I) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (rightNestedFamilyMap f I))) :=
    congrArg (((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          (rightSingletonToFlatten c I)) ≫ ·) h3
  exact (step1.trans ((Category.assoc _ _ _).symm.trans
    (step2.trans ((Category.assoc _ _ _).trans
      (step3.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun x => x ≫ (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (rightNestedFamilyMap f I)))
          (Category.assoc _ _ _))))))))

/-- The left insertion prefix is natural in the inserted object. -/
theorem leftInsertPrefix_natural {c d : V} [FiniteTensor V] (f : c ⟶ d) :
    f ≫ leftInsertPrefix d =
      leftInsertPrefix c ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (leftNestedFamilyMap f)) := by
  have h1 : f ≫ (FiniteTensor.singletonIso (V := V)).inv.app d =
      (FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.singleton (C := V)).map f) := by
    have h := (FiniteTensor.singletonIso (V := V)).inv.naturality f
    simpa using h
  have h2 : (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.singleton (C := V)).map f) ≫
        (FiniteTensor.tensor (V := V)).map
          (leftSingletonToFlatten d) =
      (FiniteTensor.tensor (V := V)).map
          (leftSingletonToFlatten c) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flatten (C := V)).map
            (leftNestedFamilyMap f)) := by
    exact (Functor.map_comp _ _ _).symm.trans
      ((congrArg (FiniteTensor.tensor (V := V)).map
        (leftSingletonToFlatten_natural f)).trans
        (Functor.map_comp _ _ _))
  have h3 : (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flatten (C := V)).map
            (leftNestedFamilyMap f)) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (leftNestedFamily d) =
      (FiniteTensor.flattenIso (V := V)).hom.app
          (leftNestedFamily c) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (leftNestedFamilyMap f)) := by
    have h := (FiniteTensor.flattenIso (V := V)).hom.naturality
      (leftNestedFamilyMap f)
    simpa using h
  change f ≫ ((FiniteTensor.singletonIso (V := V)).inv.app d ≫
      (FiniteTensor.tensor (V := V)).map
        (leftSingletonToFlatten d) ≫
      (FiniteTensor.flattenIso (V := V)).hom.app
        (leftNestedFamily d)) =
    ((FiniteTensor.singletonIso (V := V)).inv.app c ≫
      (FiniteTensor.tensor (V := V)).map
        (leftSingletonToFlatten c) ≫
      (FiniteTensor.flattenIso (V := V)).hom.app
        (leftNestedFamily c)) ≫
      (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
          (leftNestedFamilyMap f))
  have step1 : f ≫ ((FiniteTensor.singletonIso (V := V)).inv.app d ≫
        ((FiniteTensor.tensor (V := V)).map
          (leftSingletonToFlatten d) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (leftNestedFamily d))) =
      ((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.singleton (C := V)).map f)) ≫
        ((FiniteTensor.tensor (V := V)).map
          (leftSingletonToFlatten d) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (leftNestedFamily d)) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ ((FiniteTensor.tensor (V := V)).map
        (leftSingletonToFlatten d) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (leftNestedFamily d))) h1)
  have step2 : (((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.singleton (C := V)).map f)) ≫
        (FiniteTensor.tensor (V := V)).map
          (leftSingletonToFlatten d)) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (leftNestedFamily d) =
      (((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          (leftSingletonToFlatten c)) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flatten (C := V)).map
            (leftNestedFamilyMap f))) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (leftNestedFamily d) :=
    congrArg (· ≫ (FiniteTensor.flattenIso (V := V)).hom.app
        (leftNestedFamily d))
      ((Category.assoc _ _ _).trans
        ((congrArg ((FiniteTensor.singletonIso (V := V)).inv.app c ≫ ·)
          h2).trans (Category.assoc _ _ _).symm))
  have step3 : ((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          (leftSingletonToFlatten c)) ≫
        ((FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flatten (C := V)).map
            (leftNestedFamilyMap f)) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (leftNestedFamily d)) =
      ((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          (leftSingletonToFlatten c)) ≫
        ((FiniteTensor.flattenIso (V := V)).hom.app
          (leftNestedFamily c) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (leftNestedFamilyMap f))) :=
    congrArg (((FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          (leftSingletonToFlatten c)) ≫ ·) h3
  exact (step1.trans ((Category.assoc _ _ _).symm.trans
    (step2.trans ((Category.assoc _ _ _).trans
      (step3.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun x => x ≫ (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (leftNestedFamilyMap f)))
          (Category.assoc _ _ _))))))))

end UnitInsertion

end CategoryTheory.Operad
