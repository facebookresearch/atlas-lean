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

public import MathlibExt.CategoryTheory.Operad.OperadObj.Associativity

/-!
# Enriched operad objects

Bundled enriched one-coloured operad relative to `FiniteTensor`:
symmetric collection, unit, substitution, and unit/associativity laws.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe v u

/-- Enriched one-coloured operad relative to `FiniteTensor`.

A symmetric collection equipped with an operadic unit, substitution,
and the coherent right-unit, left-unit, and associativity laws. -/
structure OperadObj (V : Type u) [Category.{v} V] [FiniteTensor V] where
  /-- The underlying symmetric collection. -/
  toCollection : SymmetricCollection V
  /-- The operadic unit `emptyTensor ⟶ O(1)`. -/
  unit : OperadUnit toCollection
  /-- Operadic substitution. -/
  subst : OperadSubstitution toCollection
  /-- Right unit law. -/
  right_unit : IsRightUnit toCollection unit subst
  /-- Left unit law. -/
  left_unit : IsLeftUnit toCollection unit subst
  /-- Associativity law. -/
  assoc : IsAssociative toCollection subst

end CategoryTheory.Operad
