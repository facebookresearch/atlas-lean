/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT
public import Mathlib.Data.Nat.Log

/-!
# Array admission for the actual radix-two FFT

An admitted array has exactly `2^d` entries for its computed binary logarithm.
Zero and other lengths return `none`. Length checks and admission control are
free in the declared scalar-operation and array-access cost model.
-/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

variable {R : Type u} [CommRing R]

/-- Check the actual array length, then run the actual materialized radix-two FFT. -/
def fftArray (omega : R) (xs : Array R) : TimeM Nat (Option (Array R)) :=
  if h : xs.size = 2 ^ xs.size.log2 then
    TimeM.bind (fft xs.size.log2 omega ⟨xs, h⟩) fun out => pure (some out.toArray)
  else
    pure none

/-- Admission fails exactly for lengths outside the positive powers of two. -/
theorem fftArray_eq_none_iff (omega : R) (xs : Array R) :
    (fftArray omega xs).ret = none ↔ ∀ d : Nat, xs.size ≠ 2 ^ d := by
  by_cases h : xs.size = 2 ^ xs.size.log2
  · constructor
    · intro hbad
      simp only [fftArray, dif_pos h] at hbad
      change (some _ : Option (Array R)) = none at hbad
      cases hbad
    · intro hall
      exact False.elim (hall xs.size.log2 h)
  · constructor
    · intro _ d hd
      apply h
      rw [hd, Nat.log2_two_pow]
    · intro _
      simp only [fftArray, dif_neg h]
      rfl

end Cslib.Algorithms.Lean.TimeM
