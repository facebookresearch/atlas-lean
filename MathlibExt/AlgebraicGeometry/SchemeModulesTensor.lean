/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public noncomputable section

/-!
# Tensor products and tensor powers of sheaves of modules on a scheme

The tensor product of two sheaves of modules on a scheme is the
sheafification of the tensor product of their underlying presheaves of
modules. Tensor powers iterate it, starting from the structure sheaf:
`L^{⊗ 0} = 𝒪_X` and `L^{⊗ (n + 1)} = L^{⊗ n} ⊗ L`.

These are the single definitions of the sheaf tensor product and tensor
powers used by the line-bundle interfaces of `MathlibExt.AlgebraicGeometry`.
-/

namespace MathlibExt.AlgebraicGeometry.SchemeModulesTensor

open CategoryTheory CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

universe u

/-- The tensor product `L ⊗ M` of sheaves of modules on a scheme: the tensor
product of the underlying presheaves of modules, sheafified. -/
def moduleTensor (X : Scheme.{u}) (L M : X.Modules) : X.Modules :=
  let P := PresheafOfModulesOfCommRing.{u} X.sheaf.obj
  let U := SheafOfModules.forget X.ringCatSheaf
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    ((curriedTensor P).obj (U.obj L) |>.obj (U.obj M))

/-- The tensor power `L^{⊗ n}`: `L^{⊗ 0}` is the structure sheaf and
`L^{⊗ (n + 1)} = L^{⊗ n} ⊗ L`. -/
def power {X : Scheme.{u}} (L : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => moduleTensor X (power L n) L

end MathlibExt.AlgebraicGeometry.SchemeModulesTensor
