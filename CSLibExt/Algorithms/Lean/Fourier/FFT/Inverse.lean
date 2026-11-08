/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Field.Defs

/-!
# The source conjugate/FFT/conjugate/normalize inverse executor

Sedgewick and Wayne's FFT.java, lines 149–172. Every map materializes its
output and charges one read, one scalar operation and one write per entry.
A common `1/n` scale is computed once and charged once in this executor.
FFT.java recomputes `1.0/n` in its per-entry scaling loop.
The known natural-number input length is represented in the coefficient type
as free length data before the charged reciprocal operation.
-/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

/-- Materialize every conjugated entry and charge its read, conjugation and write. -/
def fftConjugate {R : Type u} [Star R] {n : Nat} (xs : Vector R n) :
    TimeM Nat (Vector R n) :=
  ⟨xs.map star, 3 * n⟩

/-- Materialize every normalized entry and charge its read, multiplication and write. -/
def fftScale {R : Type u} [Mul R] {n : Nat} (scale : R) (xs : Vector R n) :
    TimeM Nat (Vector R n) :=
  ⟨xs.map (fun x => scale * x), 3 * n⟩

/-- Run the actual source inverse procedure on exactly `2^d` entries. -/
def ifft {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    TimeM Nat (Vector R (2 ^ d)) := do
  let conjugated ← fftConjugate xs
  let transformed ← fft d omega conjugated
  let restored ← fftConjugate transformed
  let scale ← (⟨((2 ^ d : Nat) : R)⁻¹, 1⟩ : TimeM Nat R)
  fftScale scale restored

end Cslib.Algorithms.Lean.TimeM
