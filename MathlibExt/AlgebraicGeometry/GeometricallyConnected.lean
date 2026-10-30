/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected.lean` and
`P2M/Sol/S_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometrically irreducible implies geometrically connected

An irreducible space is connected, universally: the implication lifts to
morphism properties via the universal quantifier over base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-- A geometrically irreducible morphism is geometrically connected. -/
theorem AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIrreducible f] :
    GeometricallyConnected f := by
  refine ⟨?_⟩
  have h := GeometricallyIrreducible.geometrically_irreducibleSpace (f := f)
  rw [geometrically_eq_universally] at h ⊢
  refine MorphismProperty.universally_mono ?_ _ h
  intro X' Y' g hg hI hS
  have : IrreducibleSpace X' := hg hI hS
  infer_instance
