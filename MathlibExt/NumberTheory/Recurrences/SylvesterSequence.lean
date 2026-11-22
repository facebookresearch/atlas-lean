/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedSylvester
import Mathlib.Data.Nat.ModEq

/-!
# Sylvester numbers modulo 36

Starting from `S₂ = 7`, the recurrence preserves the residue `7` modulo `36`
because `7² - 7 + 1 = 43`.

## References

* Abderrahim Makki Naciri, *A Note on Sylvester's Sequence*, INTEGERS 24
  (2024), Article A117, Proposition 1, congruence (6).
  <https://math.colgate.edu/~integers/y117/y117.pdf>
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

/-- **Sylvester numbers.** The Sylvester numbers $S_0, S_1, S_2, \dots$ are the natural numbers
given by $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$ for $n \ge 0$, so the sequence begins
$2, 3, 7, 43, 1807, \dots$. It is the generalized Sylvester sequence with parameter $1$. -/
abbrev sylvesterNumber (n : ℕ) : ℕ :=
  Nat.generalizedSylvester 1 n

/-- **Sylvester numbers modulo 36.** Let $(S_n)_{n \ge 0}$ be the Sylvester sequence,
$S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $n \ge 2$, $S_n \equiv 7 \pmod{36}$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, congruence (6). -/
theorem sylvester_modEq_seven_mod_thirty_six
    (n : ℕ) (hn : 2 ≤ n) :
    sylvesterNumber n % 36 = 7 := by
  change sylvesterNumber n ≡ 7 [MOD 36]
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n _ ih =>
    calc
      sylvesterNumber (n + 1) = sylvesterNumber n ^ 2 - sylvesterNumber n + 1 :=
        Nat.generalizedSylvester_succ 1 n
      _ ≡ 7 ^ 2 - 7 + 1 [MOD 36] :=
        (Nat.ModEq.sub (Nat.le_self_pow two_ne_zero _) (by decide)
          (ih.pow 2) ih).add_right 1
      _ ≡ 7 [MOD 36] := by decide

end MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted
