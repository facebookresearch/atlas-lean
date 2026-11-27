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

/-- **Timed pointwise product.** For a type $R$ with a multiplication and vectors $x, y$ of
length $n$ over $R$, the pointwise product returns the vector of length $n$ whose $i$-th entry
is $x_i \cdot y_i$ for every $i < n$, and charges $4n$ time units: two reads, one multiplication
and one write per entry. -/
def fftPointwise {R : Type u} [Mul R] {n : Nat} (xs ys : Vector R n) :
    TimeM Nat (Vector R n) :=
  ⟨xs.zipWith (fun x y => x * y) ys, 4 * n⟩

/-- **Zero padding to twice the length.** For a type $R$ with a zero, a natural number $d$ and a
vector $x$ of length $2^d$ over $R$, padding returns the vector of length $2^{d+1}$ whose $i$-th
entry is $x_i$ for $i < 2^d$ and $0$ for $2^d \le i < 2^{d+1}$, and charges $3 \cdot 2^d$ time
units. -/
def fftPad {R : Type u} [Zero R] (d : Nat) (xs : Vector R (2 ^ d)) :
    TimeM Nat (Vector R (2 ^ (d + 1))) :=
  ⟨Vector.ofFn (fun i => if h : i.val < 2 ^ d then xs[i.val] else 0), 3 * 2 ^ d⟩

/-- **FFT circular convolution.** Let $R$ be a field that is a star ring, $d$ a natural number,
$\omega \in R$, and $x, y$ vectors of length $2^d$ over $R$. Circular convolution runs the timed
radix-two FFT of length $2^d$ with root $\omega$ on $x$ and then on $y$, multiplies the two
transforms pointwise, and applies the timed inverse FFT of length $2^d$ with root $\omega$ to the
product. It returns the result of the inverse transform, and its cost is the sum of the costs of
these four steps.

The definition imposes no condition on $\omega$. -/
def fftCircular {R : Type u} [Field R] [StarRing R] (d : Nat)
    (omega : R) (xs ys : Vector R (2 ^ d)) : TimeM Nat (Vector R (2 ^ d)) := do
  let left ← fft d omega xs
  let right ← fft d omega ys
  let product ← fftPointwise left right
  ifft d omega product

/-- **FFT linear convolution.** Let $R$ be a field that is a star ring, $d$ a natural number,
$\omega \in R$, and $x, y$ vectors of length $2^d$ over $R$. Linear convolution zero-pads $x$ and
$y$ to length $2^{d+1}$ and returns the FFT circular convolution of the two padded vectors at
length $2^{d+1}$ with root $\omega$. Its cost is the cost of the two paddings plus the cost of
the circular convolution.

The root $\omega$ is used for the padded length $2^{d+1}$, twice the input length. -/
def fftLinear {R : Type u} [Field R] [StarRing R] (d : Nat)
    (omega : R) (xs ys : Vector R (2 ^ d)) :
    TimeM Nat (Vector R (2 ^ (d + 1))) := do
  let left ← fftPad d xs
  let right ← fftPad d ys
  fftCircular (d + 1) omega left right

/-- **FFT circular convolution on arrays.** Let $R$ be a field that is a star ring, $\omega \in R$,
and $x, y$ arrays over $R$, where $x$ has length $n$. If $n = 2^d$ for some natural number $d$
and $y$ also has length $n$, the procedure returns the FFT circular convolution of $x$ and $y$
(read as vectors of length $2^d$) with root $\omega$, converted to an array, at the cost of that
convolution. Otherwise it returns no result, at cost $0$. -/
def fftCircularArray {R : Type u} [Field R] [StarRing R] (omega : R)
    (xs ys : Array R) : TimeM Nat (Option (Array R)) :=
  if h : xs.size = 2 ^ xs.size.log2 ∧ ys.size = xs.size then
    let left : Vector R (2 ^ xs.size.log2) := ⟨xs, h.1⟩
    let right : Vector R (2 ^ xs.size.log2) := ⟨ys, h.2.trans h.1⟩
    do
      let out ← fftCircular xs.size.log2 omega left right
      pure (some out.toArray)
  else pure none

/-- **FFT linear convolution on arrays.** Let $R$ be a field that is a star ring, $\omega \in R$,
and $x, y$ arrays over $R$, where $x$ has length $n$. If $n = 2^d$ for some natural number $d$
and $y$ also has length $n$, the procedure returns the FFT linear convolution of $x$ and $y$
(read as vectors of length $2^d$) with root $\omega$, an array of length $2n$, at the cost of
that convolution. Otherwise it returns no result, at cost $0$. -/
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
