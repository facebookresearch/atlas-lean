/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.Generic

/-!
# Predicate Transport

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
universe u
/-- An arbitrary proposition survives the two standard equality type-transport eliminators. -/
theorem predicate_eq_mp {α β : Sort u} (h : α = β) (p : α) (P : β → Prop)
    (hP : P (cast h p)) : P (Eq.mp h p) := by
  cases h
  exact hP
end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
