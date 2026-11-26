/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_PresheafOfModules_InternalHom.lean`,
`Definitions/Def_SheafOfModules_MonoidalV2.lean`,
`Theorems/Thm_PresheafOfModules_isSheaf_ihomObj.lean`,
`P2M/Sol/S_PresheafOfModules_isSheaf_ihomObj.lean`
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

public import MathlibExt.Algebra.Category.ModuleCat.PresheafTensorLocality
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Presheaves of modules are monoidal closed

For a presheaf of commutative rings `R`, the internal hom `PresheafOfModules.ihom F N` and the
adjunction bijection `PresheafOfModules.ihomHomEquiv` of
`MathlibExt.Algebra.Category.ModuleCat.PresheafTensorLocality` make the category of presheaves of
modules over `R` monoidal closed (`PresheafOfModules.instMonoidalClosed`). The internal hom into
a sheaf is a sheaf (`PresheafOfModules.isSheaf_ihom`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Presheaves of modules over a presheaf of commutative rings are monoidal closed, with internal
hom `PresheafOfModules.ihom`. -/
noncomputable instance instMonoidalClosed :
    MonoidalClosed (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  closed F :=
    { rightAdj := Adjunction.rightAdjointOfEquiv (G_obj := fun N => ihom.{u, u, u} F N)
        (fun _ _ => ihomHomEquiv) (fun _ _ _ f g => curry_naturality_left f g)
      adj := Adjunction.adjunctionOfEquivRight _ _ }

end PresheafOfModules
