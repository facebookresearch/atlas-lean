/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Inverse
public import CSLibExt.Algorithms.Lean.Fourier.FFT.DFTCorrectness
public import Mathlib.Algebra.Star.BigOperators
public import Init.Data.Vector.Lemmas

/-!
# Correctness of the executed conjugate/FFT/conjugate/normalize procedure

Every equality below concerns the actual returned Vector. The proof transports
the complete executed FFT coefficient sum through the canonical star ring
automorphism. The source normalization remains the explicitly executed scale.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open MathlibExt.Analysis.Fourier.FastFourierTransformWanted

private theorem fft_star_primitive (d : Nat) (omega : ℂ)
    (hroot : IsPrimitiveRoot omega (2 ^ d)) :
    IsPrimitiveRoot (star omega) (2 ^ d) := by
  exact hroot.map_of_injective (f := (starRingAut : ℂ ≃+* ℂ))
    (starRingAut : ℂ ≃+* ℂ).injective

private theorem fftConjugate_sample {n : Nat} (xs : Vector ℂ n)
    (j : Nat) (hj : j < n) :
    (fftConjugate xs).ret.toArray.getD j 0 = star (xs.toArray.getD j 0) := by
  change (xs.map star).toArray.getD j 0 = star (xs.toArray.getD j 0)
  rw [← Array.getElem_eq_getD (h := by simpa using hj) 0,
    ← Array.getElem_eq_getD (h := by simpa using hj) 0]
  exact Vector.getElem_map star hj

/-- Conjugate the input, execute FFT and conjugate its returned coefficients. -/
theorem fft_conjugate_ret (d : Nat) (omega : ℂ)
    (hroot : IsPrimitiveRoot omega (2 ^ d)) (xs : Vector ℂ (2 ^ d)) :
    (fftConjugate (fft d omega (fftConjugate xs).ret).ret).ret =
      (fft d (star omega) xs).ret := by
  apply Vector.ext
  intro k hk
  change ((fft d omega (fftConjugate xs).ret).ret.map star)[k] =
    (fft d (star omega) xs).ret[k]
  rw [Vector.getElem_map]
  rw [fft_correct d omega hroot (fftConjugate xs).ret ⟨k, hk⟩,
    fft_correct d (star omega) (fft_star_primitive d omega hroot) xs ⟨k, hk⟩]
  unfold dftSum
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < 2 ^ d := Finset.mem_range.mp hj
  dsimp only
  rw [fftConjugate_sample xs j hjn]
  simp only [star_mul, star_star, star_pow]
  exact mul_comm _ _

/-- The actual inverse returns the normalized actual FFT at the conjugated root. -/
theorem ifft_ret (d : Nat) (omega : ℂ)
    (hroot : IsPrimitiveRoot omega (2 ^ d)) (xs : Vector ℂ (2 ^ d)) :
    (ifft d omega xs).ret =
      (fft d (star omega) xs).ret.map (fun x => (2 ^ d : ℂ)⁻¹ * x) := by
  change (fftConjugate (fft d omega (fftConjugate xs).ret).ret).ret.map
      (fun x => ((2 ^ d : Nat) : ℂ)⁻¹ * x) = _
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [fft_conjugate_ret d omega hroot xs]

/-- Every coefficient of the executed inverse equals its full normalized DFT sum. -/
theorem ifft_correct (d : Nat) (omega : ℂ)
    (hroot : IsPrimitiveRoot omega (2 ^ d)) (xs : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ d)) :
    (ifft d omega xs).ret[k.val] =
      (2 ^ d : ℂ)⁻¹ *
        dftSum (2 ^ d) (star omega) (fun j => xs.toArray.getD j 0) k.val := by
  rw [ifft_ret d omega hroot xs, Vector.getElem_map]
  rw [fft_correct d (star omega) (fft_star_primitive d omega hroot) xs k]

end Cslib.Algorithms.Lean.TimeM
