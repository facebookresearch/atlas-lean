/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Octanacci numbers

The order-eight all-ones Fibonacci sequence appears in Emanuele Munarini,
*Shifting Property for Riordan, Sheffer and Connection Constants Matrices*,
and Tian-Xiao He, *Impulse Response Sequences and Construction of Number
Sequence Identities*.
-/

namespace MetaMathlibExt

@[expose]
public section

/-- **Octanacci window.** The octanacci window is the sequence $(w_n)_{n \ge 0}$ of $8$-tuples of
natural numbers with $w_0 = (1, 1, 2, 4, 8, 16, 32, 64)$ and, if $w_n = (a_1, \dots, a_8)$, then
$w_{n+1} = (a_2, \dots, a_8, a_1 + a_2 + \dots + a_8)$. The octanacci numbers $f_n$ are the first
entries of these tuples, so $w_n = (f_n, f_{n+1}, \dots, f_{n+7})$. -/
def octanacciWindow : Nat → Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat
  | 0 => (1, 1, 2, 4, 8, 16, 32, 64)
  | n + 1 =>
    match octanacciWindow n with
    | (a, b, c, d, e, f, g, h) =>
      (b, c, d, e, f, g, h, a + b + c + d + e + f + g + h)

/-- **Octanacci numbers.** The octanacci sequence $(f_n)_{n \ge 0}$ of natural numbers is defined by
$f_0 = f_1 = 1$, $f_n = 2^{n-1}$ for $2 \le n \le 7$, and
$f_n = f_{n-1} + f_{n-2} + \dots + f_{n-8}$ for $n \ge 8$. It begins
$1, 1, 2, 4, 8, 16, 32, 64, 128, 255, \dots$, and its generating function is
$1/(1 - t - t^2 - \dots - t^8)$.

Source: concept `jis_sem_89f2f2ec1c72d6db5f92b1d0`; statements
`jis_cb7e03aa435f1bbd253660ca` and `jis_f311834ff91269ae7cf94a4b`.
-/
def octanacciNumber (n : Nat) : Nat :=
  (octanacciWindow n).1

end

end MetaMathlibExt
