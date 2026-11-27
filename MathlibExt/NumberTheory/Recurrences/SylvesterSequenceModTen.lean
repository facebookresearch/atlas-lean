/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.SylvesterSequence
import Mathlib.Data.Nat.ModEq

/-!
# Sylvester numbers modulo ten

The recurrence sends residue `7` to `3` and then back to `7` modulo ten.

## References

* Abderrahim Makki Naciri, *A Note on Sylvester's Sequence*, *INTEGERS* 24 (2024),
  Article A117, pp. 1–7, Proposition 2, congruence (9) (p. 3).
  <https://math.colgate.edu/~integers/y117/y117.pdf>
* J. J. Sylvester, [On a Point in the Theory of Vulgar Fractions](https://doi.org/10.2307/2369261),
  *American Journal of Mathematics* 3 (4) (1880), pp. 332–335, the original source for the sequence
  credited in Naciri's Section 1.
-/

namespace MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

/-- **Sylvester numbers of even index modulo 10.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $i \ge 1$,
$S_{2i} \equiv 7 \pmod{10}$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 2, congruence (9),
even indices. -/
public theorem sylvester_even_index_mod_ten
    (i : ℕ) (hi : 1 ≤ i) :
    sylvesterNumber (2 * i) % 10 = 7 := by
  have step (n a : ℕ) (ha : sylvesterNumber n ≡ a [MOD 10]) :
      sylvesterNumber (n + 1) ≡ a ^ 2 - a + 1 [MOD 10] := by
    calc
      sylvesterNumber (n + 1) = sylvesterNumber n ^ 2 - sylvesterNumber n + 1 :=
        Nat.generalizedSylvester_succ 1 n
      _ ≡ a ^ 2 - a + 1 [MOD 10] :=
        (Nat.ModEq.sub (Nat.le_self_pow two_ne_zero _) (Nat.le_self_pow two_ne_zero _)
          (ha.pow 2) ha).add_right 1
  change sylvesterNumber (2 * i) ≡ 7 [MOD 10]
  induction i, hi using Nat.le_induction with
  | base => decide
  | succ i _ ih =>
    rw [Nat.mul_succ]
    have hodd : sylvesterNumber (2 * i + 1) ≡ 3 [MOD 10] :=
      (step (2 * i) 7 ih).trans (by decide)
    exact (step (2 * i + 1) 3 hodd).trans (by decide)

end MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted
