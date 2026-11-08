/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Init.Data.Vector.OfFn
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Init.Data.List.FinRange
import Lean.Elab.Tactic.Omega

/-!
# An array-backed radix-two FFT executor

Sources: MIT 6.046J Spring 2015 Lecture 3, pages 3–6; Sedgewick and Wayne's
FFT.java, commit 7bb62c32f03fec900f0cc796a548ab992feffe4e. The primitive-root
interface permits both source signs. Arithmetic is exact, as the author code
requires. Canonical `Vector` materializes each subsequence and each recursive
result; no transform is represented by a function that repeats child calls.

Cost model: one unit per scalar addition, subtraction, multiplication, and
array element read/write. Loop control, binding and erased proofs are free.
Splitting charges four operations per pair; each butterfly charges two reads,
three scalar operations, two writes and one twiddle multiplication. Squaring
the root costs one; initializing the output charges one write per entry.
-/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

variable {R : Type u} [CommRing R]

/-- Materialize the ordered even and odd subsequences, charging their reads and writes. -/
def fftSplit {m : Nat} (xs : Vector R (m * 2)) :
    TimeM Nat (Vector R m × Vector R m) :=
  let even := Vector.ofFn fun i : Fin m =>
    xs[2 * i.val]'(by have hi := i.isLt; omega)
  let odd := Vector.ofFn fun i : Fin m =>
    xs[2 * i.val + 1]'(by have hi := i.isLt; omega)
  ⟨(even, odd), 4 * m⟩

/-- Write one butterfly pair and advance the stored twiddle. -/
def fftButterfly {m : Nat} (omega : R) (q r : Vector R m)
    (state : R × Vector R (m * 2)) (k : Fin m) :
    TimeM Nat (R × Vector R (m * 2)) :=
  let (w, out) := state
  let a := q[k.val]
  let b := r[k.val]
  let t := w * b
  let low := out.set k.val (a + t) (by have hk := k.isLt; omega)
  let both := low.set (k.val + m) (a - t) (by have hk := k.isLt; omega)
  ⟨(w * omega, both), 8⟩

/-- Apply each butterfly once in increasing index order. -/
def fftButterflies {m : Nat} (omega : R) (q r : Vector R m)
    (out : Vector R (m * 2)) : TimeM Nat (R × Vector R (m * 2)) :=
  (List.finRange m).foldlM (fftButterfly omega q r) (1, out)

/-- Radix-two FFT on `2^d` actual array entries, with supplied sample root.
The two transformed subsequences are stored once and combined with a running
twiddle. Root assumptions are needed for correctness, not for execution. -/
def fft : (d : Nat) → R → Vector R (2 ^ d) → TimeM Nat (Vector R (2 ^ d))
  | 0, _, xs => pure xs
  | d + 1, omega, xs => do
      let halves ← fftSplit xs
      let square ← (⟨omega * omega, 1⟩ : TimeM Nat R)
      let q ← fft d square halves.1
      let r ← fft d square halves.2
      let out ← (⟨Vector.replicate (2 ^ d * 2) 0, 2 ^ d * 2⟩ :
        TimeM Nat (Vector R (2 ^ d * 2)))
      let combined ← fftButterflies omega q r out
      pure combined.2

end Cslib.Algorithms.Lean.TimeM
