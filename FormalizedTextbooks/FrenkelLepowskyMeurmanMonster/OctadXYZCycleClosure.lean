/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Two actual octad-XYZ cubic color transitions determine the third. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOctadXYZ

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The transpose Fourier action on the cubic coefficient's octad sign index. -/
noncomputable def octadCoefficientFourier (v : Fin 64 → ℝ) : Fin 64 → ℝ :=
  trialityRealMatrix.transpose.mulVec v

theorem octadCoefficientFourier_apply (v : Fin 64 → ℝ) (e : Fin 64) :
    octadCoefficientFourier v e = ∑ f, trialityRealMatrix f e * v f := rfl

/-- The actual coefficient Fourier action has the same period three as triality. -/
theorem octadCoefficientFourier_triple (v : Fin 64 → ℝ) :
    octadCoefficientFourier (octadCoefficientFourier (octadCoefficientFourier v)) = v := by
  have ht : trialityRealMatrix.transpose * trialityRealMatrix.transpose *
      trialityRealMatrix.transpose = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.mul_assoc,
      trialityRealMatrix_cube, Matrix.transpose_one]
  simp only [octadCoefficientFourier, Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, ht, Matrix.one_mulVec]

/-- The two color transitions X→Y and Y→Z imply Z→X by the actual matrix cube. -/
theorem trialityOctadXYZ_same_color_of_two
    (hX : ∀ (o : Fin 759) (e : Fin 64) (k l : Fin 49152),
      griessForm (griessProd (sExtra (trialityOctadBasis o e))
        (sExtra (trialityXYZBasis 0 k))) (sExtra (trialityXYZBasis 0 l)) =
        griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis 0 k))
          (trialityXYZBasis 0 l))
    (hY : ∀ (o : Fin 759) (e : Fin 64) (k l : Fin 49152),
      griessForm (griessProd (sExtra (trialityOctadBasis o e))
        (sExtra (trialityXYZBasis 1 k))) (sExtra (trialityXYZBasis 1 l)) =
        griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis 1 k))
          (trialityXYZBasis 1 l))
    (o : Fin 759) (e : Fin 64) (s : Fin 3) (k l : Fin 49152) :
    griessForm (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityXYZBasis s k))) (sExtra (trialityXYZBasis s l)) =
      griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis s k))
        (trialityXYZBasis s l) := by
  fin_cases s
  · exact hX o e k l
  · exact hY o e k l
  · let C (t : Fin 3) (a : Fin 64) :=
      griessForm (griessProd (trialityOctadBasis o a) (trialityXYZBasis t k))
        (trialityXYZBasis t l)
    have h0 : C 0 = octadCoefficientFourier (C 1) := by
      funext a
      have h := hX o a k l
      rw [trialityOctadXYZ_cubic_transform] at h
      exact h.symm
    have h1 : C 1 = octadCoefficientFourier (C 2) := by
      funext a
      have h := hY o a k l
      rw [trialityOctadXYZ_cubic_transform] at h
      exact h.symm
    rw [trialityOctadXYZ_cubic_transform]
    change octadCoefficientFourier (C 0) e = C 2 e
    rw [h0, h1, octadCoefficientFourier_triple]

/-- Once octad products are preserved, the two actual color transitions
close every octad×XYZ product by the complete source cubic tests. -/
theorem sExtra_octadXYZ_product_of_two_transitions
    (hOO : ∀ (o : Fin 759) (e : Fin 64) (p : Fin 759) (f : Fin 64),
      TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis p f))
    (hX : ∀ (o : Fin 759) (e : Fin 64) (k l : Fin 49152),
      griessForm (griessProd (sExtra (trialityOctadBasis o e))
        (sExtra (trialityXYZBasis 0 k))) (sExtra (trialityXYZBasis 0 l)) =
        griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis 0 k))
          (trialityXYZBasis 0 l))
    (hY : ∀ (o : Fin 759) (e : Fin 64) (k l : Fin 49152),
      griessForm (griessProd (sExtra (trialityOctadBasis o e))
        (sExtra (trialityXYZBasis 1 k))) (sExtra (trialityXYZBasis 1 l)) =
        griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis 1 k))
          (trialityXYZBasis 1 l))
    (o : Fin 759) (e : Fin 64) (s : Fin 3) (k : Fin 49152) :
    TrialityProductPreserved (trialityOctadBasis o e) (trialityXYZBasis s k) :=
  trialityOctadXYZ_of_same_color_cubic hOO
    (trialityOctadXYZ_same_color_of_two hX hY) o e s k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
