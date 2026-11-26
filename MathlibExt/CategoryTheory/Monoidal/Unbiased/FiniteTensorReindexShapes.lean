/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
Module: MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorReindexShapes
Authors: toskua-Avocado
Status: proven
Scope: shared singleton-insertion reindex shape families,
  neutral of any coherence class or model instance
Inputs: FiniteTensor, FiniteFamily, Fintype.Option,
  Finite.Sum
Outputs: reindexUnitSectionFam/TargetFam/NestedFam/InsertFam
Invariants: std-only axioms; lines ≤100 cols; docstring on every
  public decl; no sorry/admit/unsafe/partial/native_decide
Inventory: shape families (4 defs); no theorems
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensor
public import Mathlib.Data.Fintype.Option
public import Mathlib.Basic.Finite.Sum

/-!
# Singleton-insertion reindex shapes (neutral shared module)

The four shape families of the singleton-insertion unit case:
section, nested-graft, insertion, and target families. They use
only `FiniteTensor.tensor` and the `FiniteFamily` API, so they
live here — free of the coherence class and of the `Type`/`SSet`/
cartesian model proofs — and are shared by the coherence module
(`FiniteTensorReindexCoherent`) and generic consumers such as the
operad unit laws.

Elaboration-pinning note: `PUnit` lives in `Sort u`, so the
`Type 0` inhabitants are written `PUnit.{1}` explicitly, and the
`FintypeCat` carriers are written `J.obj`/`Lf.obj` rather than
`↑J`/`↑Lf`. Both pins reproduce the original elaboration of these
families exactly (verified by `#print` with `pp.universes`),
keeping downstream `rfl`-proofs intact while making elaboration
independent of the importing closure's instance set.

Public-import note: the two Mathlib imports must stay `public`.
In a public section, term-mode `inferInstance` resolves instances
only from publicly imported modules, so `Finite (Option _)` needs
`instFiniteOption` publicly visible and `Finite (_ ⊕ _)` needs
`Finite.instSum` publicly visible. Demoting either to a private
`import` breaks synthesis (top-level `#synth` still succeeds then,
which is misleading: commands see private imports, public defs do
not). Same pattern as `CartesianTensor`'s public Fintype imports.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {V : Type u} [Category.{v} V]

variable [FiniteTensor V]
/-! ## Singleton-insertion shapes -/

/-- Section-shaped family over `Option J`: an opaque outer slot and
tensor inner slots. The abstract section family of the unit case. -/
def reindexUnitSectionFam (J : FintypeCat.{0}) (Snone : V)
    (Vf : J.obj → FiniteFamily V) : FiniteFamily V where
  index :=
    haveI : Finite J.obj := J.property
    haveI : Finite (Option J.obj) := inferInstance
    FintypeCat.of (Option J.obj)
  obj := fun o => match o with
    | none => Snone
    | some j => (FiniteTensor.tensor (V := V)).obj (Vf j)

/-- Nested graft-shaped family over `PUnit ⊕ Lf`. The abstract
two-level graft vertex family. -/
def reindexUnitNestedFam (Lf : FintypeCat.{0})
    (Nobj : (PUnit.{1} ⊕ Lf.obj) → FiniteFamily V) :
    FiniteFamily (FiniteFamily V) where
  index :=
    haveI : Finite Lf.obj := Lf.property
    haveI : Finite (PUnit.{1} ⊕ Lf.obj) := inferInstance
    FintypeCat.of (PUnit.{1} ⊕ Lf.obj)
  obj := Nobj

/-- Nested insertion family over `Option PUnit`: empty at none and the
singleton family at some. The abstract left-nested family. -/
def reindexUnitInsertFam (X : V) : FiniteFamily (FiniteFamily V) where
  index := FintypeCat.of (Option PUnit.{1})
  obj := fun o => match o with
    | none => FiniteFamily.empty
    | some _ => (FiniteFamily.singleton (C := V)).obj X

/-- Target family: the tensor family of the insertion family. The
abstract left-unit tensor family, definitionally the `flattenIso`
target so the class conclusion elaborates. -/
def reindexUnitTargetFam (X : V) : FiniteFamily V :=
  (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj
    (reindexUnitInsertFam (V := V) X)

end CategoryTheory
