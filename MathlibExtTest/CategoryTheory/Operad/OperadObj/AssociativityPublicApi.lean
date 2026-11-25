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

import MathlibExt.CategoryTheory.Operad.OperadObj.Associativity

/-!
# Focused O7E associativity public-contract packet

Pins the stable downstream-facing contracts for one-color operadic
associativity: the three-level data and its derived substitutions,
the two route groupings, the reindexing hom, the factor homs, the
two routes from the common source, and the associativity equation.
-/

open CategoryTheory
open CategoryTheory.Operad

universe v u

variable {V : Type u} [Category.{v} V]

-- Derived substitution data.
noncomputable example (d : AssocData) : SubstitutionData :=
  d.middleData

noncomputable example (d : AssocData) (i : d.outer) :
    SubstitutionData :=
  d.localData i

noncomputable example (d : AssocData) : SubstitutionData :=
  d.outerAfterInnerData

noncomputable example (d : AssocData) : SubstitutionData :=
  d.innerData

noncomputable example (d : AssocData) :
    substitutionTotalObj d.innerData ≅
      substitutionTotalObj d.outerAfterInnerData :=
  d.totalIso

-- Grouping A signature and computation.
noncomputable example (O : SymmetricCollection V) (d : AssocData) :
    FiniteFamily (FiniteFamily V) :=
  AssocInsertion.groupingA O d

example (O : SymmetricCollection V) (d : AssocData) :
    (AssocInsertion.groupingA O d).obj (none : Option (d.outer : Type)) =
      (FiniteFamily.singleton (C := V)).obj (O.eval d.outer) :=
  AssocInsertion.groupingA_obj_none O d

example (O : SymmetricCollection V) (d : AssocData) (i : d.outer) :
    (AssocInsertion.groupingA O d).obj (some i : Option (d.outer : Type)) =
      (substitutionFactors O).obj (d.localData i) :=
  AssocInsertion.groupingA_obj_some O d i

-- Grouping B and flattened groupings.
noncomputable example (O : SymmetricCollection V) (d : AssocData) :
    FiniteFamily (FiniteFamily V) :=
  AssocInsertion.groupingB O d

noncomputable example (O : SymmetricCollection V) (d : AssocData) :
    FiniteFamily V :=
  AssocInsertion.flattenedGroupingA O d

noncomputable example (O : SymmetricCollection V) (d : AssocData) :
    FiniteFamily V :=
  AssocInsertion.flattenedGroupingB O d

-- Reindexing hom from flattened A to flattened B.
noncomputable example (O : SymmetricCollection V) (d : AssocData) :
    AssocInsertion.flattenedGroupingA O d ⟶
      AssocInsertion.flattenedGroupingB O d :=
  AssocInsertion.flattenAToFlattenBHom O d

variable [FiniteTensor V]

-- Route-A factor hom signature.
noncomputable example (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : AssocData) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj
          (AssocInsertion.groupingA O d) ⟶
      (substitutionFactors O).obj d.outerAfterInnerData :=
  AssocInsertion.groupingAToFactorsHom O γ d

-- Route-B factor hom signature.
noncomputable example (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : AssocData) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj
          (AssocInsertion.groupingB O d) ⟶
      (substitutionFactors O).obj d.innerData :=
  AssocInsertion.groupingBToFactorsHom O γ d

-- Common source signature.
noncomputable example (O : SymmetricCollection V) (d : AssocData) :
    V :=
  associativityCommonSource O d

-- Route A signature.
noncomputable example (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : AssocData) :
    associativityCommonSource O d ⟶
      O.eval (substitutionTotalObj d.outerAfterInnerData) :=
  associativityRouteA O γ d

-- Route B signature.
noncomputable example (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : AssocData) :
    associativityCommonSource O d ⟶
      O.eval (substitutionTotalObj d.outerAfterInnerData) :=
  associativityRouteB O γ d

-- Associativity equation.
example (O : SymmetricCollection V) (γ : OperadSubstitution O)
    (h : IsAssociative O γ) (d : AssocData) :
    associativityRouteA O γ d = associativityRouteB O γ d :=
  h d
