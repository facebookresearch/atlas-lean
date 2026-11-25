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

import MathlibExt.CategoryTheory.Operad.OperadObj.UnitInsertionNaturality

/-!
# Focused O7E insertion-prefix public-contract packet

Pins the stable downstream-facing contracts for unit-law insertion
prefixes: functoriality of the right/left nested families with block
laws, naturality of the singleton-to-flatten inclusions, and
naturality of the insertion prefixes letting legs pass through.
-/

open CategoryTheory
open CategoryTheory.Operad

universe v u

variable {V : Type u} [Category.{v} V]

-- Functoriality of the right nested family.
example {c d : V} (f : c ⟶ d) (I : FintypeCat) :
    UnitInsertion.rightNestedFamily c I ⟶
      UnitInsertion.rightNestedFamily d I :=
  UnitInsertion.rightNestedFamilyMap f I

-- The right nested-family map reindexes trivially.
example {c d : V} (f : c ⟶ d) (I : FintypeCat) :
    (UnitInsertion.rightNestedFamilyMap f I).equiv =
      Equiv.refl (Option (I : Type)) :=
  UnitInsertion.rightNestedFamilyMap_equiv f I

-- Outer block of the right nested-family map.
example {c d : V} (f : c ⟶ d) (I : FintypeCat) :
    (UnitInsertion.rightNestedFamilyMap f I).hom none =
      (FiniteFamily.singleton (C := V)).map f :=
  UnitInsertion.rightNestedFamilyMap_hom_none f I

-- Inner blocks of the right nested-family map are identities.
example {c d : V} (f : c ⟶ d) (I : FintypeCat) (i : (I : Type)) :
    (UnitInsertion.rightNestedFamilyMap f I).hom (some i) = 𝟙 _ :=
  UnitInsertion.rightNestedFamilyMap_hom_some f I i

-- Functoriality of the left nested family.
example {c d : V} (f : c ⟶ d) :
    UnitInsertion.leftNestedFamily c ⟶
      UnitInsertion.leftNestedFamily d :=
  UnitInsertion.leftNestedFamilyMap f

-- The left nested-family map reindexes trivially.
example {c d : V} (f : c ⟶ d) :
    (UnitInsertion.leftNestedFamilyMap f).equiv = Equiv.refl (Option PUnit) :=
  UnitInsertion.leftNestedFamilyMap_equiv f

-- Outer block of the left nested-family map is the identity.
example {c d : V} (f : c ⟶ d) :
    (UnitInsertion.leftNestedFamilyMap f).hom none = 𝟙 _ :=
  UnitInsertion.leftNestedFamilyMap_hom_none f

-- Inner block of the left nested-family map.
example {c d : V} (f : c ⟶ d) (u : PUnit) :
    (UnitInsertion.leftNestedFamilyMap f).hom (some u) =
      (FiniteFamily.singleton (C := V)).map f :=
  UnitInsertion.leftNestedFamilyMap_hom_some f u

-- Naturality of the right singleton-to-flatten inclusion.
example {c d : V} (f : c ⟶ d) (I : FintypeCat) :
    (FiniteFamily.singleton (C := V)).map f ≫
        UnitInsertion.rightSingletonToFlatten d I =
      UnitInsertion.rightSingletonToFlatten c I ≫
        (FiniteFamily.flatten (C := V)).map
          (UnitInsertion.rightNestedFamilyMap f I) :=
  UnitInsertion.rightSingletonToFlatten_natural f I

-- Naturality of the left singleton-to-flatten inclusion.
example {c d : V} (f : c ⟶ d) :
    (FiniteFamily.singleton (C := V)).map f ≫
        UnitInsertion.leftSingletonToFlatten d =
      UnitInsertion.leftSingletonToFlatten c ≫
        (FiniteFamily.flatten (C := V)).map
          (UnitInsertion.leftNestedFamilyMap f) :=
  UnitInsertion.leftSingletonToFlatten_natural f

-- The right insertion prefix is natural in the inserted object.
example {c d : V} [FiniteTensor V] (f : c ⟶ d) (I : FintypeCat) :
    f ≫ UnitInsertion.rightInsertPrefix d I =
      UnitInsertion.rightInsertPrefix c I ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (UnitInsertion.rightNestedFamilyMap f I)) :=
  UnitInsertion.rightInsertPrefix_natural f I

-- The left insertion prefix is natural in the inserted object.
example {c d : V} [FiniteTensor V] (f : c ⟶ d) :
    f ≫ UnitInsertion.leftInsertPrefix d =
      UnitInsertion.leftInsertPrefix c ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (UnitInsertion.leftNestedFamilyMap f)) :=
  UnitInsertion.leftInsertPrefix_natural f
