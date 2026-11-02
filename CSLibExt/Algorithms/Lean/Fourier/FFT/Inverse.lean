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

/-- **Charged entrywise conjugation.** For a type with a star operation $z \mapsto \bar z$ and a
vector $x = (x_0, \dots, x_{n-1})$ of length $n$ over it, this costed computation returns
$(\bar x_0, \dots, \bar x_{n-1})$ and charges $3n$ operations: one read, one conjugation and one
write per entry. -/
def fftConjugate {R : Type u} [Star R] {n : Nat} (xs : Vector R n) :
    TimeM Nat (Vector R n) :=
  ⟨xs.map star, 3 * n⟩

/-- **Charged entrywise scaling.** For a type with a multiplication, a scalar $c$ and a vector
$x = (x_0, \dots, x_{n-1})$ of length $n$ over it, this costed computation returns
$(c x_0, \dots, c x_{n-1})$ and charges $3n$ operations: one read, one multiplication and one
write per entry. -/
def fftScale {R : Type u} [Mul R] {n : Nat} (scale : R) (xs : Vector R n) :
    TimeM Nat (Vector R n) :=
  ⟨xs.map (fun x => scale * x), 3 * n⟩

/-- **Inverse FFT by conjugation.** Let $R$ be a field that is a star ring, with star operation
$z \mapsto \bar z$. For a natural number $d$, an element $\omega \in R$ and a vector
$x \in R^{2^d}$, the inverse FFT conjugates every entry of $x$, applies the radix-two FFT with
root $\omega$, conjugates every entry of the result, and multiplies every entry by the inverse
$(2^d)^{-1}$ of $2^d$ in $R$ (which is $0$ when $2^d = 0$ in $R$). It charges $3 \cdot 2^d$
operations for each of the two conjugation passes and for the scaling pass, one operation for
computing $(2^d)^{-1}$, and the cost of the FFT. -/
def ifft {R : Type u} [Field R] [StarRing R]
    (d : Nat) (omega : R) (xs : Vector R (2 ^ d)) :
    TimeM Nat (Vector R (2 ^ d)) := do
  let conjugated ← fftConjugate xs
  let transformed ← fft d omega conjugated
  let restored ← fftConjugate transformed
  let scale ← (⟨((2 ^ d : Nat) : R)⁻¹, 1⟩ : TimeM Nat R)
  fftScale scale restored

end Cslib.Algorithms.Lean.TimeM
