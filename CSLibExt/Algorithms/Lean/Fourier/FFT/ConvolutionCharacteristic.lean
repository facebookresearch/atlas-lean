/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Convolution
public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn

/-! # Characteristics of the actual product, direct padding and array admission -/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

/-- **Entries of the pointwise product.** Let $R$ be a type with a multiplication, let $n$ be a
natural number and let $x$ and $y$ be vectors of length $n$ over $R$. For every index $i < n$,
entry $i$ of the pointwise product of $x$ and $y$ equals $x_i y_i$. -/
theorem fftPointwise_ret {R : Type u} [Mul R] {n : Nat}
    (xs ys : Vector R n) (i : Fin n) :
    (fftPointwise xs ys).ret[i.val] = xs[i.val] * ys[i.val] := by
  exact Vector.getElem_zipWith i.isLt

/-- **Zero padding keeps the input prefix.** Let $R$ be a type with a zero, let $d$ be a natural
number and let $x$ be a vector of length $2^d$ over $R$. For every index $i < 2^d$, entry $i$
of the zero-padded vector of length $2^{d+1}$ produced from $x$ equals $x_i$. -/
theorem fftPad_ret_low {R : Type u} [Zero R] (d : Nat)
    (xs : Vector R (2 ^ d)) (i : Fin (2 ^ d)) :
    (fftPad d xs).ret[i.val]'(by
      have h := i.isLt
      simp only [pow_succ]
      omega) = xs[i.val] := by
  simp [fftPad, Vector.getElem_ofFn, i.isLt]

/-- **Zero padding fills the second half with zeros.** Let $R$ be a type with a zero, let $d$
be a natural number and let $x$ be a vector of length $2^d$ over $R$. For every index $i$ with
$2^d \le i < 2^{d+1}$, entry $i$ of the zero-padded vector of length $2^{d+1}$ produced from
$x$ is $0$. -/
theorem fftPad_ret_high {R : Type u} [Zero R] (d : Nat)
    (xs : Vector R (2 ^ d)) (i : Fin (2 ^ (d + 1))) (hi : 2 ^ d ≤ i.val) :
    (fftPad d xs).ret[i.val] = 0 := by
  simp [fftPad, Vector.getElem_ofFn, not_lt_of_ge hi]

/-- **Rejection by array circular convolution.** Let $R$ be a field with a star-ring
structure, let $\omega \in R$, and let $x$ and $y$ be arrays over $R$. The array
circular-convolution procedure with root $\omega$ returns no result on $x$ and $y$ if and only
if it is not the case that the length of $x$ is a power of two $2^k$ with $k \ge 0$ and $y$ has
the same length as $x$. -/
theorem fftCircularArray_eq_none_iff {R : Type u} [Field R] [StarRing R]
    (omega : R) (xs ys : Array R) :
    (fftCircularArray omega xs ys).ret = none ↔
      ¬ (xs.size = 2 ^ xs.size.log2 ∧ ys.size = xs.size) := by
  unfold fftCircularArray
  by_cases h : xs.size = 2 ^ xs.size.log2 ∧ ys.size = xs.size
  · rw [dite_eq_left h]
    constructor
    · intro hbad
      change (some _ : Option (Array R)) = none at hbad
      cases hbad
    · intro hnot
      exact False.elim (hnot h)
  · rw [dite_eq_right h]
    constructor
    · intro _
      exact h
    · intro _
      rfl

/-- **Rejection by array linear convolution.** Let $R$ be a field with a star-ring structure,
let $\omega \in R$, and let $x$ and $y$ be arrays over $R$. The array zero-padded
linear-convolution procedure with root $\omega$ returns no result on $x$ and $y$ if and only if
it is not the case that the length of $x$ is a power of two $2^k$ with $k \ge 0$ and $y$ has the
same length as $x$. -/
theorem fftLinearArray_eq_none_iff {R : Type u} [Field R] [StarRing R]
    (omega : R) (xs ys : Array R) :
    (fftLinearArray omega xs ys).ret = none ↔
      ¬ (xs.size = 2 ^ xs.size.log2 ∧ ys.size = xs.size) := by
  unfold fftLinearArray
  by_cases h : xs.size = 2 ^ xs.size.log2 ∧ ys.size = xs.size
  · rw [dite_eq_left h]
    constructor
    · intro hbad
      change (some _ : Option (Array R)) = none at hbad
      cases hbad
    · intro hnot
      exact False.elim (hnot h)
  · rw [dite_eq_right h]
    constructor
    · intro _
      exact h
    · intro _
      rfl

end Cslib.Algorithms.Lean.TimeM
