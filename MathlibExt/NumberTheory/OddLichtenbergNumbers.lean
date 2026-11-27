/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Odd Lichtenberg numbers

Formalizes the odd Lichtenberg numbers (OEIS A002450).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Odd Lichtenberg numbers.** The odd Lichtenberg numbers form the sequence $(a_n)_{n \ge 0}$
of natural numbers defined by $a_0 = 1$ and $a_{n+1} = 4 a_n + 1$, so the sequence begins
$1, 5, 21, 85, \dots$; these are the positive terms of OEIS A002450.

Equivalently, it is the self-generating sequence with seed $1$ and generating function
$k \mapsto 4k + 1$.

Source: Concept `jis_sem_21a46571c2d8f3f53edb5728` (`odd Lichtenberg numbers`);
required clause from stable statement `jis_e2a7cb75f919d56e388fa0b1` in
`https://cs.uwaterloo.ca/journals/JIS/VOL25/Hinz/hinz5.tex`. -/
def oddLichtenberg : ℕ → ℕ
  | 0 => 1
  | n + 1 => 4 * oddLichtenberg n + 1

end

end MetaMathlibExt
