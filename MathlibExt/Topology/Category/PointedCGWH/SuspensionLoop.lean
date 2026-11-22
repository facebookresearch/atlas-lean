/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.Topology.Category.PointedCGWH.SphereOne

/-!
# Native suspension and loop functors on pointed CGWH spaces

This file keeps the strict suspension-loop adjunction in the point-set
topology layer. Model-category files may add Quillen and derived structure
without becoming dependencies of ordinary loop-space clients.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory MonoidalCategory

namespace PointedCGWH

/-- Strict suspension of pointed CGWH spaces by fixed-left smash with the
native one-sphere. -/
noncomputable def suspension :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  PointedCGWH.copower PointedCGWH.sphereOne

/-- Strict loops of pointed CGWH spaces, as the native based internal Hom
from the one-sphere. -/
noncomputable def loop :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  PointedCGWH.power PointedCGWH.sphereOne

/-- Fixed-left smash by the one-sphere is left adjoint to based internal Hom
from the one-sphere. -/
noncomputable def suspensionLoopAdjunction :
    PointedCGWH.suspension.{u, v} ⊣ PointedCGWH.loop.{u, v} :=
  PointedCGWH.smashBasedHomAdjunction PointedCGWH.sphereOne

/-- Strict suspension of the smash unit is the native one-sphere. -/
noncomputable def suspensionSphereZeroIso :
    PointedCGWH.suspension.{u, v}.obj PointedCGWH.sphereZero ≅
      PointedCGWH.sphereOne := by
  change (PointedCGWH.sphereOne.{u, v} ⊗
      PointedCGWH.sphereZero.{u, v}) ≅ PointedCGWH.sphereOne.{u, v}
  exact ρ_ PointedCGWH.sphereOne.{u, v}

end PointedCGWH
