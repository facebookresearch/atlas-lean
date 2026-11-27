/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.LineBundleTensor

/-!
# Tests for tensor products of line bundles

Tensor products and tensor powers of line bundles are line bundles. Restriction to an open
subscheme commutes with the tensor product, which trivializes `𝒪_X ⊗ 𝒪_X` on every open
subscheme. Restriction of scalars along a surjective ring map commutes with tensor products
elementwise, and restriction of module sheaves is restriction of their underlying presheaves.
-/

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.SchemeModulesTensor
open MathlibExt.AlgebraicGeometry.LineBundleTensor

universe u

variable {X : Scheme.{u}}

example {L M : X.Modules} (hL : IsLineBundle L) (hM : IsLineBundle M) :
    IsLineBundle (moduleTensor X (moduleTensor X L M) L) :=
  (hL.moduleTensor hM).moduleTensor hL

example {L : X.Modules} (hL : IsLineBundle L) : IsLineBundle (power L 3) :=
  hL.power 3

example {L : X.Modules} (hL : IsLineBundle L) (m n : ℕ) :
    IsLineBundle (moduleTensor X (power L m) (power L n)) :=
  (hL.power m).moduleTensor (hL.power n)

example : IsLineBundle (moduleTensor X (structureModule X) (structureModule X)) :=
  (isLineBundle_structureModule X).moduleTensor (isLineBundle_structureModule X)

/-- `𝒪_X ⊗ 𝒪_X` restricts to `𝒪_U` on an open subscheme `U`. -/
noncomputable example {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] :
    (moduleTensor X (structureModule X) (structureModule X)).restrict f ≅ structureModule U :=
  restrictModuleTensorIso f _ _ ≪≫
    moduleTensorMapIso (Scheme.Modules.restrictUnitIso f) (Scheme.Modules.restrictUnitIso f) ≪≫
      unitTensorUnitIso U

/-- Restriction of a module sheaf along an open immersion restricts its underlying presheaf. -/
example {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (M : X.Modules) :
    ((Scheme.Modules.restrictFunctor f).obj M).val = (presheafRestrict f).obj M.val :=
  rfl

example {A B : CommRingCat.{u}} (g : A ⟶ B) (hg : Function.Surjective g.hom)
    (M N : ModuleCat.{u} B) (m : M) (n : N) :
    (restrictScalarsTensorIso g hg M N).inv.hom (m ⊗ₜ[B] n) =
      TensorProduct.tmul A (M := (ModuleCat.restrictScalars g.hom).obj M)
        (N := (ModuleCat.restrictScalars g.hom).obj N) m n :=
  restrictScalarsTensorIso_inv_tmul g hg M N m n

example {A B : CommRingCat.{u}} (g : A ⟶ B) (hg : Function.Surjective g.hom)
    (M N : ModuleCat.{u} B) (x : TensorProduct B M N) :
    (restrictScalarsTensorIso g hg M N).hom.hom ((restrictScalarsTensorIso g hg M N).inv.hom x) =
      x :=
  congrArg (fun f ↦ ModuleCat.Hom.hom f x) (restrictScalarsTensorIso g hg M N).inv_hom_id
