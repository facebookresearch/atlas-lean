/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensor
public import Mathlib.Data.Fintype.Option
public import Mathlib.Basic.Finite.Sum

/-!
# Singleton insertion shapes for finite tensor products

The families `reindexUnitSectionFam`, `reindexUnitNestedFam`,
`reindexUnitInsertFam` and `reindexUnitTargetFam` describe the section,
nested-graft, insertion and tensor-image shapes of singleton insertion.
They are built from `FiniteFamily` and `FiniteTensor.tensor` and occur in
finite-tensor reindexing coherence and operad unit laws. The singleton
index in `Type 0` is written `PUnit.{1}`, since `PUnit` is defined in `Sort`.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {V : Type u} [Category.{v} V]

variable [FiniteTensor V]
/-! ## Singleton-insertion shapes -/

/-- A family over `Option J`, with `Snone` at `none` and the tensors of
`Vf j` at `some j`. -/
def reindexUnitSectionFam (J : FintypeCat.{0}) (Snone : V)
    (Vf : J.obj → FiniteFamily V) : FiniteFamily V where
  index :=
    haveI : Finite J.obj := J.property
    haveI : Finite (Option J.obj) := inferInstance
    FintypeCat.of (Option J.obj)
  obj := fun o => match o with
    | none => Snone
    | some j => (FiniteTensor.tensor (V := V)).obj (Vf j)

/-- A two-level graft family indexed by `PUnit.{1} ⊕ Lf.obj`. -/
def reindexUnitNestedFam (Lf : FintypeCat.{0})
    (Nobj : (PUnit.{1} ⊕ Lf.obj) → FiniteFamily V) :
    FiniteFamily (FiniteFamily V) where
  index :=
    haveI : Finite Lf.obj := Lf.property
    haveI : Finite (PUnit.{1} ⊕ Lf.obj) := inferInstance
    FintypeCat.of (PUnit.{1} ⊕ Lf.obj)
  obj := Nobj

/-- The insertion family over `Option PUnit.{1}`, empty at `none` and
singleton at `some`. -/
def reindexUnitInsertFam (X : V) : FiniteFamily (FiniteFamily V) where
  index := FintypeCat.of (Option PUnit.{1})
  obj := fun o => match o with
    | none => FiniteFamily.empty
    | some _ => (FiniteFamily.singleton (C := V)).obj X

/-- The tensor image of the insertion family, which is the target family
of `flattenIso`. -/
def reindexUnitTargetFam (X : V) : FiniteFamily V :=
  (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj
    (reindexUnitInsertFam (V := V) X)

end CategoryTheory
