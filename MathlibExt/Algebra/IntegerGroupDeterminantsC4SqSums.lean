/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

/-!
# The sums `b_i`, `c_i` and differences `d_i` of a function on `C₄ × C₄`

Notation from Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for C_4^2*,
INTEGERS 24 (2024), Article A30, Section 2, for an integer-valued function `a` on
`C₄² = Fin 4 × Fin 4`: the sums `b_i`, the alternating sums `c_i` and the differences
`d_0, …, d_7`. The paper's variable `a_j`, `j = r + 4 s`, is `a (r, s)`.

## Main results

* `MetaMathlibExt.c4SqD_sum_sq_sq_sub_sq`: Lemma 4 of the paper (Lemma 2.9 of
  arXiv:2211.01597v2), a polynomial identity in the `d_i`. It is a difference of two squares:
  the two bracketed sums of squares differ by `4 (d_0 d_2 + d_4 d_6 + d_1 d_3 + d_5 d_7)` and
  add up to `2 ∑ d_i ^ 2`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The sums $b_i$.** For $a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$ and
$i \in \mathbb{Z}/4$, $b_i = \bigl(a(i, 0) + a(i, 2)\bigr) + \bigl(a(i, 1) + a(i, 3)\bigr)$. In the
paper's indexing $a_{r + 4s} = a(r, s)$ this is $b_i = (a_i + a_{i+8}) + (a_{i+4} + a_{i+12})$
for $0 \le i \le 3$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public def c4SqB (a : Fin 4 × Fin 4 → ℤ) (i : Fin 4) : ℤ :=
  a (i, 0) + a (i, 2) + (a (i, 1) + a (i, 3))

/-- **The alternating sums $c_i$.** For $a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$
and $i \in \mathbb{Z}/4$, $c_i = \bigl(a(i, 0) + a(i, 2)\bigr) - \bigl(a(i, 1) + a(i, 3)\bigr)$. In
the paper's indexing $a_{r + 4s} = a(r, s)$ this is $c_i = (a_i + a_{i+8}) - (a_{i+4} + a_{i+12})$
for $0 \le i \le 3$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public def c4SqC (a : Fin 4 × Fin 4 → ℤ) (i : Fin 4) : ℤ :=
  a (i, 0) + a (i, 2) - (a (i, 1) + a (i, 3))

/-- **The differences $d_i$ of a function on $C_4^2$.** For
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$, the integers $d_0, \dots, d_7$ are
$d_i = a(i, 0) - a(i, 2)$ and $d_{i+4} = a(i, 1) - a(i, 3)$ for $0 \le i \le 3$. Writing
$a_{r + 4s}$ for $a(r, s)$, this is the paper's $d_i = a_i - a_{i+8}$ for $0 \le i \le 7$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public def c4SqD (a : Fin 4 × Fin 4 → ℤ) : Fin 8 → ℤ :=
  ![a (0, 0) - a (0, 2), a (1, 0) - a (1, 2), a (2, 0) - a (2, 2), a (3, 0) - a (3, 2),
    a (0, 1) - a (0, 3), a (1, 1) - a (1, 3), a (2, 1) - a (2, 3), a (3, 1) - a (3, 3)]

/-- **Difference of the squared sums of squares of the $d_i$.** Let
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$, and let $d_i = a(i, 0) - a(i, 2)$ and
$d_{i+4} = a(i, 1) - a(i, 3)$ for $0 \le i \le 3$. Then

$$
\bigl((d_0 + d_2)^2 + (d_4 + d_6)^2 + (d_1 + d_3)^2 + (d_5 + d_7)^2\bigr)^2 -
\bigl((d_0 - d_2)^2 + (d_4 - d_6)^2 + (d_1 - d_3)^2 + (d_5 - d_7)^2\bigr)^2 =
8 \Bigl(\sum_{i=0}^{7} d_i^2\Bigr)(d_0 d_2 + d_4 d_6 + d_1 d_3 + d_5 d_7).
$$

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 4 (`integers-2024-A30-lem-4`). -/
public theorem c4SqD_sum_sq_sq_sub_sq (a : Fin 4 × Fin 4 → ℤ) :
    let d := c4SqD a
    ((d 0 + d 2) ^ 2 + (d 4 + d 6) ^ 2 + (d 1 + d 3) ^ 2 + (d 5 + d 7) ^ 2) ^ 2 -
        ((d 0 - d 2) ^ 2 + (d 4 - d 6) ^ 2 + (d 1 - d 3) ^ 2 + (d 5 - d 7) ^ 2) ^ 2 =
      8 * (d 0 ^ 2 + d 2 ^ 2 + d 4 ^ 2 + d 6 ^ 2 + d 1 ^ 2 + d 3 ^ 2 + d 5 ^ 2 + d 7 ^ 2) *
        (d 0 * d 2 + d 4 * d 6 + d 1 * d 3 + d 5 * d 7) := by
  intro d
  ring

end

end MetaMathlibExt
