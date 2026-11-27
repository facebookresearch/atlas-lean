/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Pell–Lucas numbers

This module uses the associated-Pell convention `1, 1, 3, 7, 17, …` for OEIS A001333.

JIS concept: `jis_sem_42455744e467dce308e4961b`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Pell–Lucas sequence.** The Pell–Lucas (associated Pell) numbers $Q_n$, for natural numbers
$n$, are defined by $Q_0 = 1$, $Q_1 = 1$ and $Q_{n+2} = 2Q_{n+1} + Q_n$ for every $n$. They begin
$1, 1, 3, 7, 17, \dots$ (OEIS A001333).

Source: aBa Mbirika, Janee Schrader, and Jürgen Spilker, *Pell and Associated Pell Braid
Sequences as GCDs of Sums of k Consecutive Pell, Balancing, and Related Numbers*,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Mbirika/mbir5.tex>.
-/
def pellLucasSequence : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * pellLucasSequence (n + 1) + pellLucasSequence n

@[simp] theorem pellLucasSequence_zero : pellLucasSequence 0 = 1 := rfl

@[simp] theorem pellLucasSequence_one : pellLucasSequence 1 = 1 := rfl

/-- **Recurrence for the Pell–Lucas numbers.** Write $Q_n$ for the $n$-th Pell–Lucas (associated
Pell) number. For every natural number $n$, $Q_{n+2} = 2Q_{n+1} + Q_n$. -/
theorem pellLucasSequence_succ_succ (n : ℕ) :
    pellLucasSequence (n + 2) =
      2 * pellLucasSequence (n + 1) + pellLucasSequence n := rfl

end

end MetaMathlibExt
