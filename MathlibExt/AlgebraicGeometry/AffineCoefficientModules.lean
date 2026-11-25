/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The completed tilde/Gamma and scalar-extension producers are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, under Apache License 2.0:
Mathlib/AlgebraicGeometry/Modules/Tilde.lean (copyright 2024 Weihong Xu;
authors Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent), and
Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean (copyright 2022 and
author Jujian Zhang).
Adaptation: compose their actual native adjunctions and the native Spec
pushforward/Gamma comparison; use native adjoint uniqueness and prove its
unit equation. No replacement coefficient functor or new Wanted is used.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Native affine coefficient pullback and scalar extension

For every ring map `R -> S`, compare actual sheaf pullback on `Spec S`
with actual extension of scalars before tilde. The comparison is determined
by the native tilde, pullback and scalar-extension adjunction units.
This coefficient construction has no amplitude or relative-dimension bound.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineCoefficientModules

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry

universe u

variable {R S : CommRingCat.{u}} (g : R ⟶ S)

/-- The actual pushforward/global-section comparison, with native scalar restriction. -/
def gammaPushforwardIso :
    Scheme.Modules.pushforward (Spec.map g) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars g.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso g)
    (TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R) ⋙
      (evaluation _ _).obj (op (⊤ : (Spec R).Opens))) ≪≫ Iso.refl _

/-- The native tilde-then-pullback adjunction, transported through the fixed Gamma comparison. -/
def pullbackTildeAdjunction :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map g) ⊣
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars g.hom :=
  ((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))).ofNatIsoRight
    (gammaPushforwardIso g)

/-- The native extension-of-scalars-then-tilde adjunction. -/
def scalarTildeAdjunction :
    ModuleCat.extendScalars g.hom ⋙ tilde.functor S ⊣
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars g.hom :=
  (ModuleCat.extendRestrictScalarsAdj g.hom).comp (tilde.adjunction (R := S))

/-- The actual coefficient comparison is constructed by native adjoint uniqueness. -/
def pullbackTildeIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map g) ≅
      ModuleCat.extendScalars g.hom ⋙ tilde.functor S :=
  Adjunction.leftAdjointUniq (pullbackTildeAdjunction g) (scalarTildeAdjunction g)

/-- Every coefficient generator is normalized by the actual native adjunction-unit equation. -/
theorem pullbackTildeIso_unit (M : ModuleCat.{u} R) :
    (pullbackTildeAdjunction g).unit.app M ≫
      (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars g.hom).map
        ((pullbackTildeIso g).hom.app M) =
      (scalarTildeAdjunction g).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app (pullbackTildeAdjunction g)
    (scalarTildeAdjunction g) M

end MathlibExt.AlgebraicGeometry.AffineCoefficientModules
