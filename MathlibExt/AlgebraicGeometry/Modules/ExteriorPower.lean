/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Definitions/Def_AlgebraicGeometry_ModulesDet.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.ExteriorPower

/-!
# Exterior powers of sheaves of modules over a scheme

`exteriorPower X n` sends a sheaf of modules to the sheafification of its sectionwise `n`-th
exterior power. The degree `n` is chosen by the caller: `det n M = (exteriorPower X n).obj M` is
the object part, for any `n`, and it is the determinant (top exterior power) of `M` only when `M`
is locally free of rank `n`. `MathlibExt.AlgebraicGeometry.SheafExteriorSectionModels.exteriorSheaf`
is the same construction for schemes in universe `0`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- **Sectionwise exterior power of presheaves of modules on a scheme.** The functor
`PresheafOfModules.exteriorPowerFunctor` for the structure sheaf of `X`, sending a presheaf of
`𝒪_X`-modules to its sectionwise `n`-th exterior power. -/
noncomputable abbrev presheafExteriorPower (n : ℕ) : X.PresheafOfModules ⥤ X.PresheafOfModules :=
  _root_.PresheafOfModules.exteriorPowerFunctor X.sheaf.obj n

/-- **Exterior power of sheaves of modules on a scheme.** The functor sending a sheaf of
`𝒪_X`-modules `M` to the sheafification of its sectionwise `n`-th exterior power, for a degree
`n` chosen by the caller. -/
noncomputable def exteriorPower (n : ℕ) : X.Modules ⥤ X.Modules :=
  Modules.toPresheafOfModules X ⋙ presheafExteriorPower X n ⋙
    _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

variable {X} in
/-- **Exterior power of a sheaf of modules in a chosen degree.** `det n M` is the object
`(exteriorPower X n).obj M`; the functor is `exteriorPower X n`. The degree `n` is not inferred
from a rank: this is the determinant (top exterior power) of `M` only when `M` is locally free
of rank `n`. -/
noncomputable abbrev det (n : ℕ) (M : X.Modules) : X.Modules := (exteriorPower X n).obj M

variable {X} in
@[simp] lemma exteriorPower_obj (n : ℕ) (M : X.Modules) :
    (exteriorPower X n).obj M =
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        ((presheafExteriorPower X n).obj M.val) := rfl

end AlgebraicGeometry.Scheme.Modules
