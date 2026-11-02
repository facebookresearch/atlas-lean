/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Shifted Padovan sequence.** The shifted Padovan sequence is the sequence of natural numbers
$(a_n)_{n \ge 0}$ with $a_0 = 1$, $a_1 = 0$, $a_2 = 1$ and $a_{n+3} = a_{n+1} + a_n$ for every
$n \ge 0$.

Source: Daniel Birmajer, Juan B. Gil, and Michael D. Weiner,
*Linear Recurrence Sequences and Their Convolutions via Bell Polynomials*,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Gil/gil3.tex>, where this shifted version is used.
JIS concept: `jis_sem_2d63874aa161ff9e950867e1`.
-/
def shiftedPadovanSequence : Nat → Nat
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | n + 3 => shiftedPadovanSequence (n + 1) + shiftedPadovanSequence n

@[simp] theorem shiftedPadovanSequence_zero : shiftedPadovanSequence 0 = 1 := rfl

@[simp] theorem shiftedPadovanSequence_one : shiftedPadovanSequence 1 = 0 := rfl

@[simp] theorem shiftedPadovanSequence_two : shiftedPadovanSequence 2 = 1 := rfl

/-- **Recurrence of the shifted Padovan sequence.** For every natural number $n$, the shifted
Padovan sequence $(a_n)_{n \ge 0}$ satisfies $a_{n+3} = a_{n+1} + a_n$. -/
theorem shiftedPadovanSequence_add_three (n : Nat) :
    shiftedPadovanSequence (n + 3) =
      shiftedPadovanSequence (n + 1) + shiftedPadovanSequence n := rfl

end

end MetaMathlibExt
