/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact DH/8 transforms of the local octad characters and quadratic characters. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOctadXYZCoefficients

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Orthogonality of the actual even-subset character table. -/
theorem trialityHadamard_character_sum (e c : Fin 64) :
    (∑ f, trialityHadamard e f * trialityHadamard c f) =
      if e = c then (64 : ℤ) else 0 := by
  have ht : trialityHadamard.conjTranspose = trialityHadamard.transpose := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
  have hh := triality_hadamard_isHadamard.mul_conjTranspose
  rw [ht] at hh
  have he := congrArg (fun M : Matrix (Fin 64) (Fin 64) ℤ => M e c) hh
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Fintype.card_fin, Nat.cast_ofNat, Matrix.one_apply] at he
  simpa only [mul_ite, mul_one, mul_zero] using he

/-- DH/8 sends a local binary character to its shifted quadratic diagonal. -/
theorem trialityOctad_fourier_character (e c : Fin 64) :
    (∑ f, trialityRealMatrix f e * (trialityHadamard c f : ℝ)) =
      (trialityIntegerDiagonal (trialityXor e c) : ℝ) := by
  have hh (f : Fin 64) :
      trialityIntegerDiagonal f * trialityHadamard f e * trialityHadamard c f =
      trialityIntegerDiagonal f * trialityHadamard (trialityXor e c) f := by
    rw [trialityHadamard_xor, trialityHadamard_symmetric f e]
    ring
  have hs : (∑ f, trialityIntegerDiagonal f * trialityHadamard f e *
      trialityHadamard c f) = 8 * trialityIntegerDiagonal (trialityXor e c) := by
    simp_rw [hh]
    exact trialityIntegerDiagonal_fourier _
  have hr := congrArg (fun n : ℤ => (n : ℝ)) hs
  push_cast at hr
  change (∑ f, (1 / 8 : ℝ) *
    ((trialityIntegerDiagonal f * trialityHadamard f e : ℤ) : ℝ) *
      (trialityHadamard c f : ℝ)) = _
  push_cast
  have ht (f : Fin 64) :
      (1 / 8 : ℝ) * ((trialityIntegerDiagonal f : ℝ) * trialityHadamard f e) *
        trialityHadamard c f =
      (1 / 8 : ℝ) * ((trialityIntegerDiagonal f : ℝ) *
        trialityHadamard f e * trialityHadamard c f) := by ring
  simp_rw [ht]
  rw [← Finset.mul_sum, hr]
  ring

/-- DH/8 sends a quadratic character to eight times its unique matching basis vector. -/
theorem trialityOctad_fourier_quadratic_character (e c : Fin 64) :
    (∑ f, trialityRealMatrix f e *
      ((trialityIntegerDiagonal f : ℝ) * trialityHadamard c f)) =
      if e = c then (8 : ℝ) else 0 := by
  have hs := trialityHadamard_character_sum e c
  have hr := congrArg (fun n : ℤ => (n : ℝ)) hs
  push_cast at hr
  change (∑ f, (1 / 8 : ℝ) *
    ((trialityIntegerDiagonal f * trialityHadamard f e : ℤ) : ℝ) *
      ((trialityIntegerDiagonal f : ℝ) * trialityHadamard c f)) = _
  push_cast
  have ht (f : Fin 64) :
      (1 / 8 : ℝ) * ((trialityIntegerDiagonal f : ℝ) * trialityHadamard f e) *
        ((trialityIntegerDiagonal f : ℝ) * trialityHadamard c f) =
      (1 / 8 : ℝ) * ((trialityHadamard e f : ℝ) * trialityHadamard c f) := by
    have hd := congrArg (fun n : ℤ => (n : ℝ)) (trialityIntegerDiagonal_sq f)
    push_cast at hd
    rw [trialityHadamard_symmetric f e]
    calc
      _ = (1 / 8 : ℝ) *
          ((trialityIntegerDiagonal f : ℝ) * trialityIntegerDiagonal f) *
          (trialityHadamard e f * trialityHadamard c f) := by ring
      _ = _ := by rw [hd]; ring
  simp_rw [ht]
  rw [← Finset.mul_sum, hr]
  split_ifs <;> norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
