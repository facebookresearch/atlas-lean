/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Tribonacci sequence with initial values 0, 0, 1

This module records the JIS concept `jis_sem_1b39589c4b5afc1c43ad6e8e`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Tribonacci sequence.** The Tribonacci sequence $(T_n)_{n \ge 0}$ is defined by $T_0 = 0$,
$T_1 = 0$, $T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for $n \ge 0$; it begins
$0, 0, 1, 1, 2, 4, \dots$ (OEIS A000073).

Source: JIS source statements `jis_16c3a95646fb4f21e9695b73`,
`jis_6d169983fc890fcb1432ab1e`, and `jis_91386fd90045523def73af3f`.

Source: Jiaqiang Pan, *Multiple Binomial Transforms and Families of Integer Sequences*,
Journal of Integer Sequences 13 (2010),
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Pan/pan8.tex>.
-/
def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n

end

end MetaMathlibExt
