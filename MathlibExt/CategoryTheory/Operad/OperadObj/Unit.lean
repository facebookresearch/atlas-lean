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

public import MathlibExt.CategoryTheory.Operad.OperadObj.Indexing

/-!
# Operadic unit foundation

The operadic unit source as the empty finite tensor and the enriched unit
morphism type for a symmetric collection.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe v u

/-- The operadic unit source: the abstract monoidal unit supplied by the empty
finite tensor.

It is defined as the image of the empty finite family under the unbiased
finite tensor functor `FiniteTensor.tensor`. This provides the domain for the
enriched operadic unit without assuming a terminal, initial, or binary monoidal
presentation beyond the `FiniteTensor` coherence. Arity-zero operations are
preserved as a distinct concept. -/
def operadUnitSource {V : Type u} [Category.{v} V] [FiniteTensor V] : V :=
  (FiniteTensor.tensor (V := V)).obj FiniteFamily.empty

/-- The enriched operadic unit of a symmetric collection `O`.

A unit is a morphism from the abstract monoidal unit given by the empty finite
tensor `operadUnitSource` to the unary operations `O.eval arityOne`. The target
arity `arityOne` is the standard singleton `PUnit`-bundled finite type. -/
abbrev OperadUnit {V : Type u} [Category.{v} V] [FiniteTensor V]
    (O : SymmetricCollection V) : Type v :=
  operadUnitSource (V := V) ⟶ O.eval arityOne

end CategoryTheory.Operad
