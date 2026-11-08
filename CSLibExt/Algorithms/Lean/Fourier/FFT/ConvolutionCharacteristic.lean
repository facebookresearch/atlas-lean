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

/-- Each materialized pointwise entry multiplies the two stored input entries. -/
theorem fftPointwise_ret {R : Type u} [Mul R] {n : Nat}
    (xs ys : Vector R n) (i : Fin n) :
    (fftPointwise xs ys).ret[i.val] = xs[i.val] * ys[i.val] := by
  exact Vector.getElem_zipWith i.isLt

/-- Direct padding preserves every original input entry in its original order. -/
theorem fftPad_ret_low {R : Type u} [Zero R] (d : Nat)
    (xs : Vector R (2 ^ d)) (i : Fin (2 ^ d)) :
    (fftPad d xs).ret[i.val]'(by
      have h := i.isLt
      simp only [pow_succ]
      omega) = xs[i.val] := by
  simp [fftPad, Vector.getElem_ofFn, i.isLt]

/-- Every entry in the materialized padding suffix is zero. -/
theorem fftPad_ret_high {R : Type u} [Zero R] (d : Nat)
    (xs : Vector R (2 ^ d)) (i : Fin (2 ^ (d + 1))) (hi : 2 ^ d ≤ i.val) :
    (fftPad d xs).ret[i.val] = 0 := by
  simp [fftPad, Vector.getElem_ofFn, not_lt_of_ge hi]

/-- Circular admission fails exactly when its tested source size conditions fail. -/
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

/-- Linear admission fails exactly when its tested input size conditions fail. -/
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
