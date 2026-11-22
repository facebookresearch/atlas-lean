/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SuspendedSphereHom
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionReflection

/-!
# The original scalar suspension class and positive group map

The actual sphere suspension class and the original group suspension map
use the same original scalar unit and the same underlying loop comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift

open PointedCGWH.SuspensionReflectionGeometry
open PointedCGWH.NativeLoopShiftGeometry

/-- The complete positive group suspension function is the original sphere unit class. -/
theorem spaceSuspensionGroupMap_eq_class (k : ℕ) (A : PointedCGWH.{u, v})
    (a : PointedCGWH.piN (k + 1) A) :
    ((spaceSuspensionGroupMap k).app A).hom a =
      PointedCGWH.SphereHom.sphereSuspensionClass (k + 1) A a := by
  rw [spaceSuspensionGroupMap_app]
  change ((nativeLoopGroupShiftNatIso k).hom.app (PointedCGWH.suspension.obj A)).hom
      ((PointedCGWH.piNPositiveMap k ((ihom.coev PointedCGWH.sphereOne).app A)).hom a) = _
  rw [PointedCGWH.piNPositiveMap_apply, nativeLoopGroupShiftNatIso_hom_eq_allDegree]
  rfl

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift
