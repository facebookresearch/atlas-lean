/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Tribonacci sequence with initial values 1, 1, 1

This module records JIS concept `jis_sem_1ac6ba3055559c782c485e0e`, the convention for the
Tribonacci sequence corresponding to OEIS A000213. It is distinct from the `0, 0, 1`
Tribonacci convention.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Tribonacci sequence with initial values 1, 1, 1.** The sequence $(T_n)_{n \ge 0}$ of natural
numbers defined by $T_0 = T_1 = T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for every
$n \ge 0$. It begins $1, 1, 1, 3, 5, 9, 17, \dots$ (OEIS A000213).

Sources:
* Roman Zatorsky and Taras Goy, *Parapermanents of Triangular Matrices and Some General
  Theorems on Number Sequences*,
  <https://cs.uwaterloo.ca/journals/JIS/VOL19/Goy/goy2.tex>.
* Thomas Garrity, *A Multidimensional Continued Fraction Generalization of Stern's Diatomic
  Sequence*, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Garrity/garrity4.tex>.
-/
def tribonacciWithInitialValues111 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 =>
      tribonacciWithInitialValues111 (n + 2) +
        tribonacciWithInitialValues111 (n + 1) + tribonacciWithInitialValues111 n

end

end MetaMathlibExt
