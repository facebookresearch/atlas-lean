/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace MetaMathlibExt

/-- **The generalized Markov equation and the generalized second Markov equation.** Let
$k \in \mathbb{N}$ and let $a, b, c$ be rational numbers. Put $x = (3 + 3k)a - k$,
$y = (3 + 3k)b - k$ and $z = (3 + 3k)c - k$. Then
$a^2 + b^2 + c^2 + k(bc + ca + ab) = (3 + 3k)abc$ if and only if
$x^2 + y^2 + z^2 + (k^2 + 2k)(x + y + z) + 2k^3 + 3k^2 = xyz$. The first equation is the
$k$-generalized Markov equation $\mathrm{GME}(k)$ and the second the $k$-generalized second
Markov equation $\mathrm{GSME}(k)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.4. -/
public theorem genMarkov_iff_genSecondMarkov (k : ℕ) (a b c : ℚ) :
    a ^ 2 + b ^ 2 + c ^ 2 + k * (b * c + c * a + a * b) = (3 + 3 * k) * a * b * c ↔
      let x := (3 + 3 * k) * a - k
      let y := (3 + 3 * k) * b - k
      let z := (3 + 3 * k) * c - k
      x ^ 2 + y ^ 2 + z ^ 2 + ((k : ℚ) ^ 2 + 2 * k) * (x + y + z) + 2 * (k : ℚ) ^ 3 +
          3 * (k : ℚ) ^ 2 = x * y * z := by
  dsimp only
  have hscale : (3 + 3 * (k : ℚ)) ^ 2 ≠ 0 := by positivity
  -- After substitution, the difference of the two sides scales by this square.
  rw [← mul_right_inj' hscale]
  constructor <;> intro h <;> linear_combination h

end MetaMathlibExt
