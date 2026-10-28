/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineParameterData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQParameterCount
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Fourteen literal parameters give translation coefficients and twelve modulation bits. -/
def generatedAxisFourthQAffineParameterDecode (w : Fin 14 → ZMod 2) : SpinIndex × SpinIndex :=
  (w 0 • golayLabelCoefficients 14 + w 1 • golayLabelCoefficients 2048,
    fun i => w (Fin.natAdd 2 i))

/-- The actual two annihilator rows followed by the twenty-two affine fixation equations. -/
def generatedAxisFourthQAffineParameterDerivedMatrix : Matrix (Fin 24) (Fin 14) (ZMod 2) :=
  Fin.append
    ![Fin.append ![0, 0] (golayLabelCoefficients 14),
      Fin.append ![0, 0] (golayLabelCoefficients 2048)]
    (fun j => Fin.append
      ![spinDot (generatedAxisFourthQAffineParameterCharacters j +
          generatedAxisFourthQAffineParameterCharacters 0) (golayLabelCoefficients 14),
        spinDot (generatedAxisFourthQAffineParameterCharacters j +
          generatedAxisFourthQAffineParameterCharacters 0) (golayLabelCoefficients 2048)]
      (generatedAxisFourthQAffineParameterBases j + generatedAxisFourthQAffineParameterBases 0))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel evaluates all 336 finite binary entries, including their twelve-term dot products.
/-- The kernel checks that every declared affine equation is exactly the counted syndrome row. -/
theorem generatedAxisFourthQAffineParameter_matrix_eq :
    generatedAxisFourthQAffineParameterDerivedMatrix = generatedFourthQParameterMatrix := by
  decide +kernel

private theorem parameter_row (c : Fin 2 → ZMod 2) (v : SpinIndex)
    (w : Fin 14 → ZMod 2) :
    (∑ i, Fin.append c v i * w i) =
      c 0 * w 0 + c 1 * w 1 + spinDot (fun i => w (Fin.natAdd 2 i)) v := by
  rw [Fin.sum_univ_add (a := 2) (b := 12)]
  simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_two]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

private theorem parameter_decode_plane (w : Fin 14 → ZMod 2) :
    (generatedAxisFourthQAffineParameterDecode w).1 ∈ generatedAxisFourthQAffineParameterPlane :=
  Submodule.mem_span_pair.mpr ⟨w 0, w 1, rfl⟩

/-- Vanishing of the counted syndrome is precisely membership in the actual affine family kernel. -/
theorem generatedAxisFourthQAffineParameter_decode_mem_iff (w : Fin 14 → ZMod 2) :
    generatedAxisFourthQAffineParameterDecode w ∈ generatedAxisFourthQAffineFamilyKernel
      generatedAxisFourthQAffineParameterPlane generatedAxisFourthQAffineParameterBases
      generatedAxisFourthQAffineParameterCharacters 0 ↔
        w ∈ generatedFourthQParameterSpace := by
  rw [generatedAxisFourthQAffineFamilyKernel_mem]
  change (_ ∧ (∀ s ∈ _, spinDot _ s = 0) ∧ ∀ j, _ = 0) ↔
    generatedFourthQParameterMatrix *ᵥ w = 0
  rw [← generatedAxisFourthQAffineParameter_matrix_eq]
  have hf (j : Fin 22) :
      (generatedAxisFourthQAffineParameterDerivedMatrix *ᵥ w) (Fin.natAdd 2 j) =
        spinDot (generatedAxisFourthQAffineParameterDecode w).2
          (generatedAxisFourthQAffineParameterBases j +
            generatedAxisFourthQAffineParameterBases 0) +
        spinDot (generatedAxisFourthQAffineParameterCharacters j +
          generatedAxisFourthQAffineParameterCharacters 0)
          (generatedAxisFourthQAffineParameterDecode w).1 := by
    simp only [Matrix.mulVec, dotProduct,
      generatedAxisFourthQAffineParameterDerivedMatrix, Fin.append_right]
    rw [parameter_row]
    simp only [generatedAxisFourthQAffineParameterDecode, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, spinDot_add_right,
      generatedAxisFourthQAffineParameter_dot_smul_right]
    ring
  have hz (i : Fin 2) :
      (generatedAxisFourthQAffineParameterDerivedMatrix *ᵥ w) (Fin.castAdd 22 i) =
        spinDot (generatedAxisFourthQAffineParameterDecode w).2
          (![golayLabelCoefficients 14, golayLabelCoefficients 2048] i) := by
    simp only [Matrix.mulVec, dotProduct,
      generatedAxisFourthQAffineParameterDerivedMatrix, Fin.append_left]
    fin_cases i
    · change (∑ i : Fin 14, Fin.append ![0, 0] (golayLabelCoefficients 14) i * w i) = _
      rw [parameter_row]
      simp [generatedAxisFourthQAffineParameterDecode]
    · change (∑ i : Fin 14, Fin.append ![0, 0] (golayLabelCoefficients 2048) i * w i) = _
      rw [parameter_row]
      simp [generatedAxisFourthQAffineParameterDecode]
  constructor
  · rintro ⟨hu, hm, hj⟩
    apply funext
    intro i
    induction i using Fin.addCases (m := 2) (n := 22) with
    | left i =>
      rw [hz]
      fin_cases i
      · exact hm _ generatedAxisFourthQAffineParameter_plane_first_mem
      · exact hm _ generatedAxisFourthQAffineParameter_plane_last_mem
    | right j => exact (hf j).trans (hj j)
  · intro hw
    refine ⟨parameter_decode_plane w, ?_, ?_⟩
    · apply (generatedAxisFourthQAffineParameter_plane_annihilator_iff _).mpr
      have h0 := congrFun hw (Fin.castAdd 22 (0 : Fin 2))
      have h1 := congrFun hw (Fin.castAdd 22 (1 : Fin 2))
      rw [hz] at h0 h1
      exact ⟨h0, h1⟩
    · intro j
      exact (hf j).symm.trans (congrFun hw (Fin.natAdd 2 j))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
