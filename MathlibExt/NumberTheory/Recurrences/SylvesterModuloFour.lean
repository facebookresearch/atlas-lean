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
# Sylvester numbers modulo four

The first positive-index term is `3`. For the later terms, reducing the
congruence modulo `36` gives the same residue modulo `4`.

## References

* Abderrahim Makki Naciri, *A Note on Sylvester's Sequence*, INTEGERS 24
  (2024), Article A117, Proposition 1, congruences (5) and (6), pp. 2–3.
  <https://math.colgate.edu/~integers/y117/y117.pdf>
* J. J. Sylvester, *On a Point in the Theory of Vulgar Fractions*, American
  Journal of Mathematics 3 (1880), pp. 332–335, for the original sequence.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

/-- **Sylvester numbers modulo 4.** Let $(S_n)_{n \ge 0}$ be the Sylvester sequence,
$S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $n \ge 1$, $S_n \equiv 3 \pmod 4$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, congruence (5). -/
theorem sylvester_modEq_three_mod_four
    (n : ℕ) (hn : 1 ≤ n) :
    sylvesterNumber n % 4 = 3 := by
  by_cases hn₂ : 2 ≤ n
  · have h36 : sylvesterNumber n ≡ 7 [MOD 36] :=
      sylvester_modEq_seven_mod_thirty_six n hn₂
    exact h36.of_dvd (by decide : 4 ∣ 36)
  · have hn₁ : n = 1 := by omega
    subst n
    decide

end MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted
