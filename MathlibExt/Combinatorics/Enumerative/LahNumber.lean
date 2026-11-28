/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Unsigned Lah number.** For natural numbers $n$ and $k$, the unsigned Lah number $L(n, k)$
is $\binom{n-1}{k-1} \frac{n!}{k!}$ when $1 \le k \le n$, $L(0, 0) = 1$, and $L(n, k) = 0$
otherwise.

$L(n, k)$ counts the partitions of an $n$-element set into $k$ nonempty linearly ordered blocks.

Source: closed formula from Maxie D. Schmidt, *Jacobi-Type Continued
Fractions for the Ordinary Generating Functions of Generalized Factorial
Functions*, Journal of Integer Sequences 20 (2017):
https://cs.uwaterloo.ca/journals/JIS/VOL20/Schmidt/schmidt14.tex. -/
def unsignedLahNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
    Nat.choose n k * Nat.factorial (n + 1) / Nat.factorial (k + 1)

/-- **Signed Lah number.** For natural numbers $n$ and $k$, the signed Lah number is the integer
$(-1)^{n-k} L(n, k)$ when $k \le n$, where $L(n, k)$ is the unsigned Lah number, and $0$ when
$k > n$.

Source: sign convention from Toufik Mansour, Matthias Schork, and Mark Shattuck,
*The Generalized Stirling and Bell Numbers Revisited*, Journal of Integer
Sequences 15 (2012):
https://cs.uwaterloo.ca/journals/JIS/VOL15/Schork/schork2.tex. -/
def signedLahNumber (n k : ℕ) : ℤ :=
  if k ≤ n then (-1 : ℤ) ^ (n - k) * unsignedLahNumber n k else 0

end MetaMathlibExt
