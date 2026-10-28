/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual octad triality cubic is the normalized ambient binary Fourier sum. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCosetCubic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Reindex the three actual sign labels as the canonical triple sign space. -/
noncomputable def octadTripleLabelEquiv : (Fin 3 → Fin 64) ≃ OctadTripleSignSpace :=
  Equiv.piCongrRight (fun _ => octadSignLabelEquiv)

private def octadTernaryTupleEquiv (A : Type*) : A × A × A ≃ (Fin 3 → A) where
  toFun x := ![x.1,x.2.1,x.2.2]
  invFun x := (x 0,x 1,x 2)
  left_inv x := rfl
  right_inv x := by ext s; fin_cases s <;> rfl

private theorem octad_sum_ternary {A : Type*} [Fintype A] (h : (Fin 3 → A) → ℝ) :
    (∑ x, h x) = ∑ a, ∑ b, ∑ c, h ![a,b,c] := by
  rw [← (octadTernaryTupleEquiv A).sum_comp h]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Sums over canonical triples are the actual three nested 64-label sums. -/
theorem octad_sum_triple_labels (h : OctadTripleSignSpace → ℝ) :
    (∑ x, h x) = ∑ a, ∑ b, ∑ c, h (octadTripleSignLabel a b c) := by
  rw [← octadTripleLabelEquiv.sum_comp h, octad_sum_ternary]
  have ht (a b c : Fin 64) : octadTripleLabelEquiv ![a,b,c] =
      octadTripleSignLabel a b c := by
    ext s
    fin_cases s <;> rfl
  simp_rw [ht]

/-- The actual triple pairing is the sum of its three actual label pairings. -/
theorem octadTripleForm_label (a b c e f g : Fin 64) :
    octadTripleForm (octadTripleSignLabel a b c) (octadTripleSignLabel e f g) =
      trialityBinaryPair a e + trialityBinaryPair b f + trialityBinaryPair c g := by
  change (∑ s, octadSignForm (octadTripleSignLabel a b c s)
    (octadTripleSignLabel e f g s)) = _
  rw [Fin.sum_univ_three]
  change octadSignForm (octadSignLabelEquiv a) (octadSignLabelEquiv e) +
    octadSignForm (octadSignLabelEquiv b) (octadSignLabelEquiv f) +
    octadSignForm (octadSignLabelEquiv c) (octadSignLabelEquiv g) = _
  rw [octadSignForm_label, octadSignForm_label, octadSignForm_label]

/-- Actual real triality entries are the quadratic row sign times the binary character. -/
theorem trialityRealMatrix_character (a e : Fin 64) :
    trialityRealMatrix a e = (1/8 : ℝ) * (trialityIntegerDiagonal a : ℝ) *
      qSign (trialityBinaryPair a e) := by
  change (1/8 : ℝ) * ((trialityIntegerDiagonal a * trialityHadamard a e : ℤ) : ℝ) = _
  rw [Int.cast_mul, trialityHadamard_binary]
  simp only [trialityIntegerSign, qSign, Int.cast_ite, Int.cast_one, Int.cast_neg]
  ring

/-- On actual cubic support, the three quadratic row signs cancel. -/
theorem trialityRealMatrix_triple_cubic (o p u : Fin 759) (a b c e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    (trialityRealMatrix a e * trialityRealMatrix b f * trialityRealMatrix c g) *
      griessForm (griessProd (trialityOctadBasis o a) (trialityOctadBasis p b))
        (trialityOctadBasis u c) =
      (1/512 : ℝ) * qSign (octadTripleForm (octadTripleSignLabel a b c)
        (octadTripleSignLabel e f g)) *
        griessForm (griessProd (trialityOctadBasis o a) (trialityOctadBasis p b))
          (trialityOctadBasis u c) := by
  rw [trialityRealMatrix_character, trialityRealMatrix_character, trialityRealMatrix_character,
    octadTripleForm_label, qSign_add, qSign_add]
  calc
    _ = (1/512 : ℝ) * (qSign (trialityBinaryPair a e) * qSign (trialityBinaryPair b f) *
      qSign (trialityBinaryPair c g)) *
      ((trialityIntegerDiagonal a : ℝ) * (trialityIntegerDiagonal b : ℝ) *
        (trialityIntegerDiagonal c : ℝ) *
        griessForm (griessProd (trialityOctadBasis o a) (trialityOctadBasis p b))
          (trialityOctadBasis u c)) := by ring
    _ = _ := by rw [griessForm_octad_cubic_four_diagonal o p u a b c hfour hu]

/-- The actual transformed cubic is precisely the affine-coset Fourier contraction. -/
theorem griessForm_transformed_octad_coset_four (o p u : Fin 759) (e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    griessForm (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityOctadBasis p f))) (sExtra (trialityOctadBasis u g)) =
      qSign (spinDot (sourceWordTheta (golayOctadLabel p))
        (golayLabelCoefficients (golayOctadLabel o))) / 512 *
      ∑ x : OctadTripleSignSpace,
        (if octadTripleCosetShift o p + x ∈ octadTripleSyndromeKernel o p u then
          qSign (octadTripleForm (octadTripleCosetShift o p) x) else 0) *
            qSign (octadTripleForm x (octadTripleSignLabel e f g)) := by
  rw [griessForm_transformed_octad_cubic, octad_sum_triple_labels]
  simp_rw [trialityRealMatrix_triple_cubic o p u _ _ _ e f g hfour hu,
    griessForm_octad_cubic_four_coset o p u _ _ _ hfour hu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
