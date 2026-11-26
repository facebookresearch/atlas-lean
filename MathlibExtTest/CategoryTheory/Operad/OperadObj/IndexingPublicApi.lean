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

import MathlibExt.CategoryTheory.Operad.OperadObj.Indexing

/-!
# Focused O7E indexing public-contract packet

Pins the stable downstream-facing contracts for one-color operadic
substitution indexing: the factor/source/target functors and the
outer/inner factor-index helpers.
-/

open CategoryTheory
open CategoryTheory.Operad

universe v u

variable {V : Type u} [Category.{v} V]

-- Factor functor signature.
noncomputable example (O : SymmetricCollection V) :
    SubstitutionData ⥤ FiniteFamily V :=
  substitutionFactors O

-- Outer factor-index helper.
noncomputable example (O : SymmetricCollection V)
    (X : SubstitutionData) :
    ((substitutionFactors O).obj X).index :=
  substitutionFactorsOuterIndex O X

-- Inner factor-index helper.
noncomputable example (O : SymmetricCollection V)
    (X : SubstitutionData) (i : X.index) :
    ((substitutionFactors O).obj X).index :=
  substitutionFactorsInnerIndex O X i

variable [FiniteTensor V]

-- Source functor signature.
noncomputable example (O : SymmetricCollection V) :
    SubstitutionData ⥤ V :=
  substitutionSource O

-- Target functor signature.
noncomputable example (O : SymmetricCollection V) :
    SubstitutionData ⥤ V :=
  substitutionTarget O
