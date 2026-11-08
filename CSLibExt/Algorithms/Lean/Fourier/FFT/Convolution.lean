/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Inverse

/-!
# Executed FFT circular and zero-padded linear convolution

Sedgewick and Wayne's FFT.java, circular and linear convolution procedures.
Pointwise multiplication reads both stored coefficients, multiplies and writes.
Direct padding copies each input coefficient once and writes the final zeros.
The linear procedure supplies a root for the padded length, twice the input length.
-/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

/-- Materialize the products of two equally sized stored coefficient vectors. -/
def fftPointwise {R : Type u} [Mul R] {n : Nat} (xs ys : Vector R n) :
    TimeM Nat (Vector R n) :=
  ⟨xs.zipWith (fun x y => x * y) ys, 4 * n⟩

/-- Copy the input prefix and materialize an equally long zero suffix directly. -/
def fftPad {R : Type u} [Zero R] (d : Nat) (xs : Vector R (2 ^ d)) :
    TimeM Nat (Vector R (2 ^ (d + 1))) :=
  ⟨Vector.ofFn (fun i => if h : i.val < 2 ^ d then xs[i.val] else 0), 3 * 2 ^ d⟩

/-- Execute both forward transforms, their stored product and the source inverse. -/
def fftCircular {R : Type u} [Field R] [StarRing R] (d : Nat)
    (omega : R) (xs ys : Vector R (2 ^ d)) : TimeM Nat (Vector R (2 ^ d)) := do
  let left ← fft d omega xs
  let right ← fft d omega ys
  let product ← fftPointwise left right
  ifft d omega product

/-- Pad both inputs, then execute circular convolution at exactly twice their size. -/
def fftLinear {R : Type u} [Field R] [StarRing R] (d : Nat)
    (omega : R) (xs ys : Vector R (2 ^ d)) :
    TimeM Nat (Vector R (2 ^ (d + 1))) := do
  let left ← fftPad d xs
  let right ← fftPad d ys
  fftCircular (d + 1) omega left right

/-- Reject unequal or inadmissible source lengths before circular execution. -/
def fftCircularArray {R : Type u} [Field R] [StarRing R] (omega : R)
    (xs ys : Array R) : TimeM Nat (Option (Array R)) :=
  if h : xs.size = 2 ^ xs.size.log2 ∧ ys.size = xs.size then
    let left : Vector R (2 ^ xs.size.log2) := ⟨xs, h.1⟩
    let right : Vector R (2 ^ xs.size.log2) := ⟨ys, h.2.trans h.1⟩
    do
      let out ← fftCircular xs.size.log2 omega left right
      pure (some out.toArray)
  else pure none

/-- Reject unequal or inadmissible input lengths before zero-padded execution. -/
def fftLinearArray {R : Type u} [Field R] [StarRing R] (omega : R)
    (xs ys : Array R) : TimeM Nat (Option (Array R)) :=
  if h : xs.size = 2 ^ xs.size.log2 ∧ ys.size = xs.size then
    let left : Vector R (2 ^ xs.size.log2) := ⟨xs, h.1⟩
    let right : Vector R (2 ^ xs.size.log2) := ⟨ys, h.2.trans h.1⟩
    do
      let out ← fftLinear xs.size.log2 omega left right
      pure (some out.toArray)
  else pure none

end Cslib.Algorithms.Lean.TimeM
