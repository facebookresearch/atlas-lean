/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.RightPairEvaluationFormula

/-!
# Right Face Evaluation

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

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Independent
universe uV vV uD vD
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {D : Type uD} [Category.{vD} D]

/-- Postcomposing an original right face retains the full pair inverse, original
Gamma and right unitor of the actual target. -/
theorem right_face_postcompose (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V)
    (gamma : GammaType M P S) (pair : PairFormula M P (fun n r => n + r))
    (n r : ℕ) (K : V) (N : D) (f : P r K ⟶ N) :
    letI := M
    rightFaceFamily M P S gamma pair n r K ≫ f =
      (pair r n K (S n)).inv ≫ (f ⊗ₘ gamma n) ≫ (ρ_ N).hom := by
  let := M
  simp only [rightFaceFamily, Category.assoc]
  rw [← rightUnitor_naturality f]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Independent

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]

/-- Every whole original right face satisfying its original pair formula evaluates
to the complete pair word after every entire free map. -/
theorem right_faces_evaluation_word_formula
    (M : MonoidalCategory (EnrichedFunctorCat V J)) (a : ℕ → J) (S : ℕ → V)
    (gamma : Independent.GammaType M (fun n K => Free.object (a n) K) S)
    (p : Independent.PairFormula M (fun n K => Free.object (a n) K) (fun n r => n + r))
    (faces : Independent.RightFaceType (fun n K => Free.object (a n) K) S)
    (hFaces : Independent.RightFaceFormula M (fun n K => Free.object (a n) K) S gamma p faces)
    (n r : ℕ) (K : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (a r) K ⟶ N) :
    Free.evaluate (a (r + n)) (K ⊗ S n) N (faces n r K ≫ f) =
    RightPairEvaluationWord M a (fun n r => n + r) p r n K (S n) N f (gamma n) := by
  let := M
  have hFace : faces n r K =
      Independent.rightFaceFamily M (fun n K => Free.object (a n) K) S gamma p n r K :=
    (hFaces n r K).trans
      (Independent.rightFaceFamily_original M (fun n K => Free.object (a n) K) S gamma p n r K).symm
  have hPost := (congrArg (fun z => z ≫ f) hFace).trans
    (Independent.right_face_postcompose M (fun n K => Free.object (a n) K) S gamma p n r K N f)
  exact (congrArg (Free.evaluate (a (r + n)) (K ⊗ S n) N) hPost).trans
    (right_pair_evaluation_word_formula M a (fun n r => n + r) p r n K (S n) N f (gamma n)).symm

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
