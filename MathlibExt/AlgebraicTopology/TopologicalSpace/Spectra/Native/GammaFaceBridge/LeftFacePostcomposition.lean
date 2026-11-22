/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaSmashFaces

/-!
# Left Face Postcomposition

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
noncomputable section
universe uV vV uD vD
open CategoryTheory MonoidalCategory

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Independent
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {D : Type uD} [Category.{vD} D]

/-- Postcomposing an original left face retains the complete pair inverse, Gamma map and
the left unitor of the actual target. -/
theorem left_face_postcompose (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V)
    (gamma : GammaType M P S) (pair : PairFormula M P (fun n r => n + r))
    (n r : ℕ) (K : V) (N : D) (f : P r K ⟶ N) :
    letI := M
    leftFaceFamily M P S gamma pair n r K ≫ f =
      (pair n r (S n) K).inv ≫ (gamma n ⊗ₘ f) ≫ (λ_ N).hom := by
  let := M
  simp only [leftFaceFamily, Category.assoc]
  rw [← leftUnitor_naturality f]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Independent
