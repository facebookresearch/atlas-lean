/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignFourierCache

/-! Exact character transport through the original quadratic octad Fourier matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The unnormalized Walsh character, evaluated through the checked integer DH cache. -/
def generatedFifthSignHadamardCache (l f : Fin 64) : ℤ :=
  trialityIntegerDiagonal l * generatedFifthSignFourierCache l f

/-- The cached character is the genuine original even-subset character. -/
theorem generatedFifth_sign_hadamard_cache (l f : Fin 64) :
    generatedFifthSignHadamardCache l f = trialityHadamard l f := by
  rw [generatedFifthSignHadamardCache, generatedFifth_sign_fourier_cache,
    trialityIntegerMatrix, ← mul_assoc, trialityIntegerDiagonal_sq, one_mul]

private theorem hadamard_sq (l e : Fin 64) :
    trialityHadamard l e * trialityHadamard l e = 1 := by
  unfold trialityHadamard
  split <;> norm_num

/-- Exact quadratic Fourier transport cancels the source and correcting Walsh characters. -/
theorem generatedFifth_sign_fourier_character (l s e : Fin 64) :
    (trialityIntegerDiagonal s * trialityIntegerDiagonal (trialityXor l s) *
      trialityHadamard l e) *
      (∑ f : Fin 64, trialityIntegerMatrix f e * trialityHadamard l f *
        trialityIntegerMatrix s f) = 8 * trialityIntegerMatrix e s := by
  have ht (f : Fin 64) :
      trialityIntegerMatrix f e * trialityHadamard l f * trialityIntegerMatrix s f =
      trialityIntegerDiagonal s *
        (trialityIntegerDiagonal f * trialityHadamard (trialityXor e (trialityXor l s)) f) := by
    simp only [trialityIntegerMatrix]
    rw [trialityHadamard_xor, trialityHadamard_xor, trialityHadamard_symmetric f e]
    ring
  simp_rw [ht]
  rw [← Finset.mul_sum, trialityIntegerDiagonal_fourier,
    trialityIntegerDiagonal_xor e (trialityXor l s)]
  rw [trialityHadamard_symmetric e (trialityXor l s), trialityHadamard_xor,
    trialityHadamard_symmetric s e]
  calc
    _ = 8 * (trialityIntegerDiagonal s * trialityIntegerDiagonal s) *
        (trialityIntegerDiagonal (trialityXor l s) * trialityIntegerDiagonal (trialityXor l s)) *
        (trialityHadamard l e * trialityHadamard l e) *
        (trialityIntegerDiagonal e * trialityHadamard e s) := by ring
    _ = _ := by
      rw [trialityIntegerDiagonal_sq, trialityIntegerDiagonal_sq, hadamard_sq,
        trialityIntegerMatrix]
      ring

/-- A common source sign cancels from the full character-conjugated Fourier convolution. -/
theorem generatedFifth_sign_fourier_character_signed (α : ℤ) (hα : α * α = 1)
    (l s e : Fin 64) :
    (α * (trialityIntegerDiagonal s * trialityIntegerDiagonal (trialityXor l s) *
      trialityHadamard l e)) *
      (∑ f : Fin 64, trialityIntegerMatrix f e * (α * trialityHadamard l f) *
        trialityIntegerMatrix s f) = 8 * trialityIntegerMatrix e s := by
  have hs : (∑ f : Fin 64, trialityIntegerMatrix f e * (α * trialityHadamard l f) *
      trialityIntegerMatrix s f) =
      α * ∑ f : Fin 64, trialityIntegerMatrix f e * trialityHadamard l f *
        trialityIntegerMatrix s f := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    ring
  rw [hs]
  calc
    _ = (α * α) *
        ((trialityIntegerDiagonal s * trialityIntegerDiagonal (trialityXor l s) *
          trialityHadamard l e) *
          ∑ f : Fin 64, trialityIntegerMatrix f e * trialityHadamard l f *
            trialityIntegerMatrix s f) := by ring
    _ = _ := by rw [hα, one_mul, generatedFifth_sign_fourier_character]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
