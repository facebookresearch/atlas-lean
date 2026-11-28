/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

/-!
# Actual scalar action and global-section maps for line families

A top-open section is extended by the native restriction maps and then
converted to a structure-module arrow through the existing unit-Hom
bijection. Scalar multiplication is composition with that actual regular
function endomorphism. These are completed ordinary operations, not Wanted
Hitchin or characteristic-coefficient maps.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LineSectionScalars
open _root_.CategoryTheory _root_.Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
universe u

/-- Native restriction of an actual global module section to every open. -/
def compatibleSections {X : Scheme.{u}} (M : X.Modules) (s : Γ(M,⊤)) : M.sections :=
  M.val.sectionsMk (fun U => M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s)
    (by
      intro U V f
      rw [← M.val.map_comp_apply]
      congr 1)

def fromTop {X : Scheme.{u}} (M : X.Modules) (s : Γ(M,⊤)) : structureModule X ⟶ M :=
  M.unitHomEquiv.symm (compatibleSections M s)

/-- The actual structure-module multiplication by a global regular function. -/
def scalarEnd (X : Scheme.{u}) (r : Γ(X,⊤)) : structureModule X ⟶ structureModule X :=
  fromTop (structureModule X) r

def scale {X : Scheme.{u}} {M : X.Modules} (r : Γ(X,⊤)) (s : Section M) : Section M :=
  scalarEnd X r ≫ s

/-- Pullback of a regular function is the actual top-open scheme map. -/
def pullFunction {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y,⊤)) : Γ(X,⊤) :=
  f.appTop r

end MathlibExt.AlgebraicGeometry.LineSectionScalars
