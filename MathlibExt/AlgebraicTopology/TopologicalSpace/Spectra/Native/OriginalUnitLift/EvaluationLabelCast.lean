/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.Generic

/-!
# Evaluation Label Cast

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed
namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {J : Type uJ} [EnrichedCategory V J]

/-- Evaluation of the actual source label equality retains the same original target equality. -/
theorem evaluate_label_cast (a : ℕ → J) {m n : ℕ} (h : m = n) (K : V)
    (X : EnrichedFunctorCat V J) (g : Free.object (a n) K ⟶ X) :
    Free.evaluate (a m) K X
      (eqToHom (congrArg (fun j => Free.object (a j) K) h) ≫ g) =
        Free.evaluate (a n) K X g ≫
          eqToHom (congrArg (fun j => X.toEnrichedFunctor.obj (a j)) h.symm) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
