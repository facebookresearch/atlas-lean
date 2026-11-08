/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.ConvolutionCharacteristic
public import CSLibExt.Algorithms.Lean.Fourier.FFT.ConvolutionCost

/-! # Actual convolution array admission, stored returns, lengths and charges -/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

/-- Circular array admission returns the same actual stored circular execution. -/
theorem fftCircularArray_ret_of_vector {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftCircularArray omega xs.toArray ys.toArray).ret =
      some (fftCircular d omega xs ys).ret.toArray := by
  rcases xs with ⟨left, hleft⟩
  rcases ys with ⟨right, hright⟩
  have hlog : left.size.log2 = d := by rw [hleft, Nat.log2_two_pow]
  subst d
  have hvalid : left.size = 2 ^ left.size.log2 ∧ right.size = left.size :=
    ⟨hleft, hright.trans hleft.symm⟩
  unfold fftCircularArray
  rw [dite_eq_left hvalid]
  rfl

/-- Circular array admission preserves all actually executed charges. -/
theorem fftCircularArray_time_of_vector {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftCircularArray omega xs.toArray ys.toArray).time = (fftCircular d omega xs ys).time := by
  rcases xs with ⟨left, hleft⟩
  rcases ys with ⟨right, hright⟩
  have hlog : left.size.log2 = d := by rw [hleft, Nat.log2_two_pow]
  subst d
  have hvalid : left.size = 2 ^ left.size.log2 ∧ right.size = left.size :=
    ⟨hleft, hright.trans hleft.symm⟩
  unfold fftCircularArray
  rw [dite_eq_left hvalid]
  rfl

/-- Circular array admission has the exact actual FFT/product/IFFT charge. -/
theorem fftCircularArray_time_add_two {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftCircularArray omega xs.toArray ys.toArray).time + 2 = (21 * d + 16) * 2 ^ d := by
  rw [fftCircularArray_time_of_vector]
  exact fftCircular_time_add_two d omega xs ys

/-- Every successful raw circular output has exactly the source input length. -/
theorem fftCircularArray_size_of_eq_some {R : Type u} [Field R] [StarRing R]
    (omega : R) (xs ys out : Array R)
    (hout : (fftCircularArray omega xs ys).ret = some out) :
    out.size = xs.size := by
  unfold fftCircularArray at hout
  by_cases h : xs.size = 2 ^ xs.size.log2 ∧ ys.size = xs.size
  · rw [dite_eq_left h] at hout
    change some (fftCircular xs.size.log2 omega
      ⟨xs, h.1⟩ ⟨ys, h.2.trans h.1⟩).ret.toArray = some out at hout
    have heq := Option.some.inj hout
    rw [← heq]
    exact (fftCircular xs.size.log2 omega
      ⟨xs, h.1⟩ ⟨ys, h.2.trans h.1⟩).ret.size_toArray.trans h.1.symm
  · rw [dite_eq_right h] at hout
    change (none : Option (Array R)) = some out at hout
    cases hout

/-- Linear array admission returns the same actual twice-sized padded execution. -/
theorem fftLinearArray_ret_of_vector {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftLinearArray omega xs.toArray ys.toArray).ret =
      some (fftLinear d omega xs ys).ret.toArray := by
  rcases xs with ⟨left, hleft⟩
  rcases ys with ⟨right, hright⟩
  have hlog : left.size.log2 = d := by rw [hleft, Nat.log2_two_pow]
  subst d
  have hvalid : left.size = 2 ^ left.size.log2 ∧ right.size = left.size :=
    ⟨hleft, hright.trans hleft.symm⟩
  unfold fftLinearArray
  rw [dite_eq_left hvalid]
  rfl

/-- Linear array admission preserves both padding and actual convolution charges. -/
theorem fftLinearArray_time_of_vector {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftLinearArray omega xs.toArray ys.toArray).time = (fftLinear d omega xs ys).time := by
  rcases xs with ⟨left, hleft⟩
  rcases ys with ⟨right, hright⟩
  have hlog : left.size.log2 = d := by rw [hleft, Nat.log2_two_pow]
  subst d
  have hvalid : left.size = 2 ^ left.size.log2 ∧ right.size = left.size :=
    ⟨hleft, hright.trans hleft.symm⟩
  unfold fftLinearArray
  rw [dite_eq_left hvalid]
  rfl

/-- Linear array admission has the exact actual padding/FFT/product/IFFT charge. -/
theorem fftLinearArray_time_add_two {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftLinearArray omega xs.toArray ys.toArray).time + 2 = (42 * d + 80) * 2 ^ d := by
  rw [fftLinearArray_time_of_vector]
  exact fftLinear_time_add_two d omega xs ys

/-- Every successful raw linear output has exactly twice the source input length. -/
theorem fftLinearArray_size_of_eq_some {R : Type u} [Field R] [StarRing R]
    (omega : R) (xs ys out : Array R)
    (hout : (fftLinearArray omega xs ys).ret = some out) :
    out.size = 2 * xs.size := by
  unfold fftLinearArray at hout
  by_cases h : xs.size = 2 ^ xs.size.log2 ∧ ys.size = xs.size
  · rw [dite_eq_left h] at hout
    change some (fftLinear xs.size.log2 omega
      ⟨xs, h.1⟩ ⟨ys, h.2.trans h.1⟩).ret.toArray = some out at hout
    have heq := Option.some.inj hout
    rw [← heq]
    calc
      _ = 2 ^ (xs.size.log2 + 1) := (fftLinear xs.size.log2 omega
        ⟨xs, h.1⟩ ⟨ys, h.2.trans h.1⟩).ret.size_toArray
      _ = 2 * xs.size := by rw [pow_succ, ← h.1, Nat.mul_comm]
  · rw [dite_eq_right h] at hout
    change (none : Option (Array R)) = some out at hout
    cases hout

end Cslib.Algorithms.Lean.TimeM
