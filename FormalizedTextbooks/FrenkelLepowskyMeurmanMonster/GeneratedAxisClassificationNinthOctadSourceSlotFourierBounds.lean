/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotFourierData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadFourierBounds

/-! Structural sparse Fourier bounds use the original two-term triangle inequality and
four-term negative-product identity. The actual source shape is certified separately. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

private theorem ninthEightTermSum (f : Fin 8 → ℤ) :
    ∑ j, f j = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  simp [Fin.sum_univ_succ]
  ring

/-- Every two-slot source block has sparse Fourier numerator at most four at every row. -/
theorem generatedNinth_octad_two_slot_fourier_abs_le (o : Fin 759)
    (h : GeneratedNinthOctadTwoSlotShape o) (e : Fin 64) :
    |generatedNinthFinalOctadSlotFastNumerator o e| ≤ 4 := by
  unfold GeneratedNinthOctadTwoSlotShape at h
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  have h6 := h 6 (by decide)
  have h7 := h 7 (by decide)
  unfold generatedNinthFinalOctadSlotFastNumerator
  rw [ninthEightTermSum]
  simp only [h2, h3, h4, h5, h6, h7, mul_zero, add_zero]
  exact generatedNinth_octad_fourier_two_terms_abs_le e _ _ _ _
    (generatedNinth_octad_slot_fast_abs_le_two o 0)
    (generatedNinth_octad_slot_fast_abs_le_two o 1)

/-- A four-slot block satisfying the checked source shape has numerator at most four
at every row. -/
theorem generatedNinth_octad_four_slot_fourier_abs_le (o : Fin 759)
    (h : GeneratedNinthOctadFourSlotShape o) (e : Fin 64) :
    |generatedNinthFinalOctadSlotFastNumerator o e| ≤ 4 := by
  obtain ⟨hzero, h0, h1, h2, h3, hxor, hp⟩ := h
  have h4 := hzero 4 (by decide)
  have h5 := hzero 5 (by decide)
  have h6 := hzero 6 (by decide)
  have h7 := hzero 7 (by decide)
  unfold generatedNinthFinalOctadSlotFastNumerator
  rw [ninthEightTermSum]
  simp only [h4, h5, h6, h7, mul_zero, add_zero]
  exact generatedNinth_octad_fourier_four_terms_abs_le e _ _ _ _ _ _ _ _
    h0 h1 h2 h3 hxor hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
