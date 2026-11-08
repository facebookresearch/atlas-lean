/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Array
public import CSLibExt.Algorithms.Lean.Fourier.FFT.DFTCorrectness
public import CSLibExt.Algorithms.Lean.Fourier.FFT.Cost

/-! # The admitted array has the actual FFT coefficients and actual execution charge -/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

/-- Every admissible vector runs the same actual FFT through array admission. -/
theorem fftArray_ret_of_vector {R : Type u} [CommRing R]
    (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (fftArray omega xs.toArray).ret = some (fft d omega xs).ret.toArray := by
  rcases xs with ⟨values, hsize⟩
  have hlog : values.size.log2 = d := by rw [hsize, Nat.log2_two_pow]
  subst d
  unfold fftArray
  rw [dite_eq_left hsize]
  rfl

/-- Admission preserves the charge of the actual FFT on each valid vector. -/
theorem fftArray_time_of_vector {R : Type u} [CommRing R]
    (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (fftArray omega xs.toArray).time = (fft d omega xs).time := by
  rcases xs with ⟨values, hsize⟩
  have hlog : values.size.log2 = d := by rw [hsize, Nat.log2_two_pow]
  subst d
  unfold fftArray
  rw [dite_eq_left hsize]
  rfl

/-- An actual admitted Complex array has its full source coefficient at every valid frequency. -/
theorem fftArray_correct (d : Nat) (omega : ℂ)
    (hroot : IsPrimitiveRoot omega (2 ^ d)) (xs : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ d)) :
    ∃ ys : Array ℂ, (fftArray omega xs.toArray).ret = some ys ∧
      ys.size = 2 ^ d ∧
      ys.getD k.val 0 =
        MathlibExt.Analysis.Fourier.FastFourierTransformWanted.dftSum
          (2 ^ d) omega (fun j => xs.toArray.getD j 0) k.val := by
  refine ⟨(fft d omega xs).ret.toArray, fftArray_ret_of_vector d omega xs,
    (fft d omega xs).ret.size_toArray, ?_⟩
  have hsample : (fft d omega xs).ret.toArray.getD k.val 0 =
      (fft d omega xs).ret[k.val] :=
    (Array.getElem_eq_getD (h := by simp) 0).symm
  exact hsample.trans (fft_correct d omega hroot xs k)

/-- The admitted array's actual execution satisfies the same exact count. -/
theorem fftArray_time_add_one {R : Type u} [CommRing R]
    (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    (fftArray omega xs.toArray).time + 1 = (7 * d + 1) * 2 ^ d := by
  rw [fftArray_time_of_vector]
  exact fft_time_add_one d omega xs

end Cslib.Algorithms.Lean.TimeM
