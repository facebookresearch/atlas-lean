/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_ModulesDet.lean`
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

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.ExteriorPower

/-!
# Exterior powers of sheaves of modules over a scheme

Sheafification of the pointwise presheaf exterior power; `det` is the
top exterior power functor applied to a sheaf of modules.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

noncomputable abbrev presheafExteriorPower (n : ℕ) : X.PresheafOfModules ⥤ X.PresheafOfModules :=
  _root_.PresheafOfModules.exteriorPowerFunctor X.sheaf.obj n

noncomputable def exteriorPower (n : ℕ) : X.Modules ⥤ X.Modules :=
  Modules.toPresheafOfModules X ⋙ presheafExteriorPower X n ⋙
    _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

variable {X} in

noncomputable abbrev det (n : ℕ) (M : X.Modules) : X.Modules := (exteriorPower X n).obj M

variable {X} in
@[simp] lemma exteriorPower_obj (n : ℕ) (M : X.Modules) :
    (exteriorPower X n).obj M =
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        ((presheafExteriorPower X n).obj M.val) := rfl

end AlgebraicGeometry.Scheme.Modules
