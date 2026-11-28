/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Modules.Monoidal
public import MathlibExt.AlgebraicGeometry.SchemeModulesTensor

@[expose] public section

open CategoryTheory MonoidalCategory MonoidalClosed AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

/-- Instance synthesis for presheaves and sheaves of modules on a scheme. -/
example : MonoidalClosed X.PresheafOfModules := inferInstance

example : SymmetricCategory X.Modules := inferInstance

example : MonoidalClosed X.Modules := inferInstance

example : (Scheme.Modules.sheafify X).Monoidal := inferInstance

/-- The monoidal unit of `X.Modules` is the structure sheaf. -/
example : 𝟙_ X.Modules = SheafOfModules.unit X.ringCatSheaf := Scheme.Modules.tensorUnit_eq

/-- The internal hom of the presheaves underlying two sheaves of modules on `X` is a sheaf of
modules on `X`. -/
example (L M : X.Modules) : X.Modules :=
  ⟨(ihom L.val).obj M.val,
    PresheafOfModules.isSheaf_ihom (R₀ := X.sheaf.obj) L.val M.val M.isSheaf⟩

/-- `L ⊗ M` is the sheafified presheaf tensor product. -/
example (L M : X.Modules) : (Scheme.Modules.sheafify X).obj (L.val ⊗ M.val) ≅ L ⊗ M :=
  Scheme.Modules.tensorIsoSheafify L M

/-- The sheafified presheaf tensor product is `SchemeModulesTensor.moduleTensor`, and the named
comparison `moduleTensorIso` is `tensorIsoSheafify`. -/
example (L M : X.Modules) :
    Scheme.Modules.moduleTensorIso L M = Scheme.Modules.tensorIsoSheafify L M :=
  rfl

end
