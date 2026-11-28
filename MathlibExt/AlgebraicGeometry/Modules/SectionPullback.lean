/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Pullbacks of sections of sheaves of modules on schemes

For a morphism of schemes `f : X ⟶ Y` and a sheaf of modules `L` on `Y`:

* `LineBundleTaskContracts.pullbackSection f s` pulls a global section `s`, a morphism
  `structureModule Y ⟶ L` (`LineBundleTaskContracts.Section L`), back to a global section of
  `(Scheme.Modules.pullback f).obj L`, through the comparison of the pullback of the structure
  sheaf with the structure sheaf;
* `ModuleTensorPullbackSections.localPullback f L U s` pulls a section `s` of `L` over an open
  `U` back to a section of `(Scheme.Modules.pullback f).obj L` over `f ⁻¹ᵁ U`, through the unit
  of the pullback–pushforward adjunction.

These definitions keep their names and namespaces from
`MathlibExt.AlgebraicGeometry.LineBundleTaskContracts` and
`MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections`, which import this module; they live
here so that a module can use them with these light imports only.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

open CategoryTheory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

/-- The actual structure-sheaf morphisms, equivalently global sections. -/
abbrev Section {X : Scheme.{u}} (L : X.Modules) := structureModule X ⟶ L

/-- The canonical pullback of a section, with its source fixed by the
actual adjunction-induced structure-sheaf comparison. -/
def pullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (s : Section L) : Section ((Scheme.Modules.pullback f).obj L) := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  exact (asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)).inv ≫
    (Scheme.Modules.pullback f).map s

end MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

namespace MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections

open _root_.CategoryTheory _root_.Opposite
open _root_.AlgebraicGeometry

universe u

/-- The actual pullback of a local section, read through the native unit. -/
def localPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    (U : Y.Opens) (s : Γ(L,U)) :
    Γ((Scheme.Modules.pullback f).obj L, f ⁻¹ᵁ U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (op U)).hom s

end MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections
