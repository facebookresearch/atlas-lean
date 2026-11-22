/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftPairEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftFacePostcomposition

/-!
# Left Face Evaluation

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uV vV uJ
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]

/-- Every full original face satisfying its original pair formula evaluates to
the complete pair word after every entire native free map. -/
theorem left_faces_evaluation_word_formula
    (M : MonoidalCategory (EnrichedFunctorCat V J)) (a : ℕ → J) (S : ℕ → V)
    (gamma : Independent.GammaType M (fun n K => Free.object (a n) K) S)
    (p : Independent.PairFormula M (fun n K => Free.object (a n) K) (fun n r => n + r))
    (faces : Independent.LeftFaceType (fun n K => Free.object (a n) K) S)
    (hFaces : Independent.LeftFaceFormula M (fun n K => Free.object (a n) K) S gamma p faces)
    (n r : ℕ) (K : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (a r) K ⟶ N) :
    Free.evaluate (a (n + r)) (S n ⊗ K) N (faces n r K ≫ f) =
    LeftPairEvaluationWord M a (fun n r => n + r) p n r (S n) K N (gamma n) f := by
  let := M
  have hFace : faces n r K =
      Independent.leftFaceFamily M (fun n K => Free.object (a n) K) S gamma p n r K :=
    (hFaces n r K).trans
      (Independent.leftFaceFamily_original M (fun n K => Free.object (a n) K) S gamma p n r K).symm
  have hPost := (congrArg (fun z => z ≫ f) hFace).trans
    (Independent.left_face_postcompose M (fun n K => Free.object (a n) K) S gamma p n r K N f)
  exact (congrArg (Free.evaluate (a (n + r)) (S n ⊗ K) N) hPost).trans
    (left_pair_evaluation_word_formula M a (fun n r => n + r) p n r (S n) K N (gamma n) f).symm

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
