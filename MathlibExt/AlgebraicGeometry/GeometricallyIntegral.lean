/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.lean`
and
`P2M/Sol/S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import MathlibExt.AlgebraicGeometry.GeometricallyIrreducible
import MathlibExt.AlgebraicGeometry.GeometricallyReduced

/-!
# Geometrically integral schemes over an algebraically closed field

An integral scheme over an algebraically closed field is geometrically
integral: every base change to a field extension stays integral.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- An integral scheme over an algebraically closed field is geometrically integral. -/
theorem GeometricallyIntegral.of_isIntegral_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] : GeometricallyIntegral f := by
  let _ : GeometricallyIrreducible f :=
    GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed f
  let _ : GeometricallyReduced f :=
    GeometricallyReduced.of_isReduced_of_perfectField f
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

end AlgebraicGeometry
