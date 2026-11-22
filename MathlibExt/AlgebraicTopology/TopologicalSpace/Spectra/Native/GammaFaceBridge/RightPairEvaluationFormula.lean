/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.RightPairEvaluation

/-!
# Right Pair Evaluation Formula

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]

/-- Expose the complete literal evaluated right pair arrow while the pair family,
objects, coefficient maps and native tensor dictionary are still typed parameters. -/
theorem right_pair_evaluation_word_formula
    (M : MonoidalCategory (EnrichedFunctorCat V J)) (a : ℕ → J) (t : ℕ → ℕ → ℕ)
    (p : Independent.PairFormula M (fun n K => Free.object (a n) K) t) :
  letI := M
  ∀ (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (a n) K ⟶ N)
    (g : Free.object (a r) L ⟶ 𝟙_ (EnrichedFunctorCat V J)),
    RightPairEvaluationWord M a t p n r K L N f g =
      Free.evaluate (a (t n r)) (K ⊗ L) N
        ((p n r K L).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom) := by
  let := M
  intro n r K L N f g
  rfl

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
