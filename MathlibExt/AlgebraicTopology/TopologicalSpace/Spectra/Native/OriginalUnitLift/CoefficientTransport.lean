/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.Generic

/-!
# Coefficient Transport

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped MonoidalClosed
namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {J : Type uJ} [EnrichedCategory V J]

/-- Propositional type transport relates the two original equality eliminators without reducing a pair. -/
theorem coefficientFamily_eq_mp
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (a : ℕ → J) (t : ℕ → ℕ → ℕ)
    (T : Type _) (hType : T = Independent.PairFormula M (fun n X => Free.object (a n) X) t)
    (p : T) (h : CoefficientFamily M a t (cast hType p)) :
    CoefficientFamily M a t (Eq.mp hType p) := by
  cases hType
  exact h

end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
