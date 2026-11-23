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

/-- **Array circular FFT convolution agrees with the vector version.** Let $R$ be a field
with a star-ring structure, let $d$ be a natural number, let $\omega \in R$ be arbitrary, and
let $x, y$ be vectors over $R$ of length $2^d$. Then array circular FFT convolution with root
$\omega$, run on the arrays underlying $x$ and $y$, succeeds and returns the array underlying
the output of vector circular FFT convolution of $x$ and $y$ at size $2^d$ with root $\omega$. -/
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

/-- **Array circular FFT convolution costs the same as the vector version.** Let $R$ be a
field with a star-ring structure, let $d$ be a natural number, let $\omega \in R$, and let
$x, y$ be vectors over $R$ of length $2^d$. The time charged by array circular FFT convolution
with root $\omega$ on the arrays underlying $x$ and $y$ equals the time charged by vector
circular FFT convolution of $x$ and $y$ at size $2^d$ with root $\omega$. -/
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

/-- **Exact cost of array circular FFT convolution.** Let $R$ be a field with a star-ring
structure, let $d$ be a natural number, let $\omega \in R$, and let $x, y$ be vectors over $R$
of length $2^d$. The time charged by array circular FFT convolution with root $\omega$ on the
arrays underlying $x$ and $y$, plus $2$, equals $(21d + 16) \cdot 2^d$. -/
theorem fftCircularArray_time_add_two {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftCircularArray omega xs.toArray ys.toArray).time + 2 = (21 * d + 16) * 2 ^ d := by
  rw [fftCircularArray_time_of_vector]
  exact fftCircular_time_add_two d omega xs ys

/-- **Output length of array circular FFT convolution.** Let $R$ be a field with a star-ring
structure, let $\omega \in R$, and let $x, y$ be arrays over $R$. If array circular FFT
convolution with root $\omega$ on $x$ and $y$ returns an array $z$, then $z$ has the same
length as $x$. -/
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

/-- **Array linear FFT convolution agrees with the vector version.** Let $R$ be a field with
a star-ring structure, let $d$ be a natural number, let $\omega \in R$ be arbitrary, and let
$x, y$ be vectors over $R$ of length $2^d$. Then array zero-padded linear FFT convolution with
root $\omega$, run on the arrays underlying $x$ and $y$, succeeds and returns the array
underlying the output (of length $2^{d+1}$) of vector zero-padded linear FFT convolution of
$x$ and $y$ at size $2^d$ with root $\omega$. -/
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

/-- **Array linear FFT convolution costs the same as the vector version.** Let $R$ be a field
with a star-ring structure, let $d$ be a natural number, let $\omega \in R$, and let $x, y$ be
vectors over $R$ of length $2^d$. The time charged by array zero-padded linear FFT convolution
with root $\omega$ on the arrays underlying $x$ and $y$ equals the time charged by vector
zero-padded linear FFT convolution of $x$ and $y$ at size $2^d$ with root $\omega$. -/
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

/-- **Exact cost of array linear FFT convolution.** Let $R$ be a field with a star-ring
structure, let $d$ be a natural number, let $\omega \in R$, and let $x, y$ be vectors over $R$
of length $2^d$. The time charged by array zero-padded linear FFT convolution with root
$\omega$ on the arrays underlying $x$ and $y$, plus $2$, equals $(42d + 80) \cdot 2^d$. -/
theorem fftLinearArray_time_add_two {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs ys : Vector R (2 ^ d)) :
    (fftLinearArray omega xs.toArray ys.toArray).time + 2 = (42 * d + 80) * 2 ^ d := by
  rw [fftLinearArray_time_of_vector]
  exact fftLinear_time_add_two d omega xs ys

/-- **Output length of array linear FFT convolution.** Let $R$ be a field with a star-ring
structure, let $\omega \in R$, and let $x, y$ be arrays over $R$. If array zero-padded linear
FFT convolution with root $\omega$ on $x$ and $y$ returns an array $z$, then the length of $z$
is twice the length of $x$. -/
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
