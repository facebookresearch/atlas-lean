/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_SheafOfModules_Monoidal.lean`,
`Definitions/Def_SheafOfModules_MonoidalV2.lean`,
`Theorems/Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.lean`,
`P2M/Sol/S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.lean`
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

public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The monoidal structure on sheaves of modules on a scheme

For a scheme `X`, the presheaves of modules `X.PresheafOfModules` and the sheaves of modules
`X.Modules` are symmetric monoidal closed categories, with the structures of
`MathlibExt.Algebra.Category.ModuleCat.Sheaf.Monoidal`. Sheafification
`Scheme.Modules.sheafify X` is a monoidal functor, and `L ⊗ M` is the sheafified presheaf tensor
product (`Scheme.Modules.tensorIsoSheafify`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

variable (X : Scheme.{u})

instance Scheme.PresheafOfModules.monoidalCategory : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂
    CommRingCat RingCat)))
instance Scheme.PresheafOfModules.symmetricCategory : SymmetricCategory X.PresheafOfModules :=
  inferInstanceAs (SymmetricCategory (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂
    CommRingCat RingCat)))
instance Scheme.PresheafOfModules.monoidalClosed : MonoidalClosed X.PresheafOfModules :=
  inferInstanceAs (MonoidalClosed (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat
    RingCat)))

/-- Sheaves of modules on a scheme form a monoidal category. -/
instance Scheme.Modules.monoidalCategory : MonoidalCategory X.Modules :=
  inferInstanceAs (MonoidalCategory
    (SheafOfModules.{u} (SheafOfModules.ringSheaf X.sheaf.obj X.ringCatSheaf.property)))
instance Scheme.Modules.symmetricCategory : SymmetricCategory X.Modules :=
  inferInstanceAs (SymmetricCategory
    (SheafOfModules.{u} (SheafOfModules.ringSheaf X.sheaf.obj X.ringCatSheaf.property)))
instance Scheme.Modules.monoidalClosed : MonoidalClosed X.Modules :=
  inferInstanceAs (MonoidalClosed
    (SheafOfModules.{u} (SheafOfModules.ringSheaf X.sheaf.obj X.ringCatSheaf.property)))

variable {X}

@[simp] theorem Scheme.Modules.tensorUnit_eq :
    𝟙_ X.Modules = SheafOfModules.unit X.ringCatSheaf := rfl

variable (X) in
/-- Sheafification of presheaves of modules on a scheme. -/
abbrev Scheme.Modules.sheafify : X.PresheafOfModules ⥤ X.Modules :=
  SheafOfModules.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property

instance : (Scheme.Modules.sheafify X).Monoidal :=
  inferInstanceAs (SheafOfModules.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property).Monoidal

/-- On a scheme, `L ⊗ M` is the sheafified presheaf tensor product. -/
def Scheme.Modules.tensorIsoSheafify (L M : X.Modules) :
    (Scheme.Modules.sheafify X).obj (L.val ⊗ M.val) ≅ L ⊗ M :=
  SheafOfModules.tensorIsoSheafify X.sheaf.obj X.ringCatSheaf.property L M

end AlgebraicGeometry

end
