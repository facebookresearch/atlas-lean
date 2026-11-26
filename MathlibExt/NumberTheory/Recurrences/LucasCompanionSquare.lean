/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
import MathlibExt.NumberTheory.Recurrences.SubsequenceSecondOrderRecurrence
import Mathlib.Tactic.LinearCombination

/-!
# Square of the companion Lucas sequence

For positive indices the formula is the discriminant identity for a subsequence of a second-order
recurrence. At index zero it follows from the initial values.
-/

namespace MetaMathlibExt

/-- **Square of the companion Lucas sequence.** Let $x$ and $y \neq 0$ be integers and let
$(U_n)$ and $(V_n)$ be the Lucas sequences with parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$,
$V_0 = 2$, $V_1 = x$ and $W_{n+2} = x W_{n+1} - y W_n$ for $W = U, V$. Then for every natural
number $n$, $V_n^2 = (x^2 - 4y) U_n^2 + 4 y^n$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (vi) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem lucasV_sq_eq (P : LucasSequenceParams) (n : ℕ) :
    lucasV P n ^ 2 = (P.p ^ 2 - 4 * P.q) * lucasU P n ^ 2 + 4 * P.q ^ n := by
  by_cases hn : n = 0
  · subst n
    simp [lucasV, lucasU]
  · have h := (subsequence_secondOrderRecurrence P (lucasU P) (lucasU_add_two P) n 0
      (Nat.pos_of_ne_zero hn)).2
    linear_combination h

end MetaMathlibExt
