/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ThreeIntegersSymmetricSquares
import Mathlib.Tactic.Ring

/-!
# Choudhry's family (3.31) of square triples with square symmetric functions

The proof verifies explicit integer square roots for the entries, their sum and the sum of their
pairwise products. The product of the entries is then a square by closure under multiplication.

## References

* Ajai Choudhry, *Three Integers Whose Sum, Product, and the Sum of the Products of the Integers,
  Taken Two at a Time, Are Perfect Squares*, INTEGERS 26 (2026), Article A35, pp. 1–15,
  Theorem 2, family (3.31). https://math.colgate.edu/~integers/aa35/aa35.pdf
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

local notation "shiftedQuartic" m:arg n:arg => m ^ 4 - 6 * m ^ 2 * n ^ 2 + n ^ 4

/-- **Choudhry's family (3.31) of square triples with square symmetric functions.** For all
integers $m$ and $n$, let $a = 64 m^4 n^4 (m^2 - n^2)^2$, $b = 16 m^2 n^2 (m^2 - n^2)^4$ and
$c = (m^2 + n^2)^2 (m^4 - 6 m^2 n^2 + n^4)^2$. Then $a + b + c$, $ab + bc + ca$ and $abc$ are
squares of integers, and $a$, $b$ and $c$ are themselves squares of integers.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the
Integers, Taken Two at a Time, Are Perfect Squares", Theorem 2, family (3.31). -/
theorem hasSquareElementarySymmetricFunctions_family331_and_entries_square
    (m n : ℤ) :
    let a := 64 * m ^ 4 * n ^ 4 * (m ^ 2 - n ^ 2) ^ 2
    let b := 16 * m ^ 2 * n ^ 2 * (m ^ 2 - n ^ 2) ^ 4
    let c := (m ^ 2 + n ^ 2) ^ 2 * (shiftedQuartic m n) ^ 2
    HasSquareElementarySymmetricFunctions a b c ∧
      IsSquare a ∧ IsSquare b ∧ IsSquare c := by
  intro a b c
  have ha : IsSquare a := ⟨8 * m ^ 2 * n ^ 2 * (m ^ 2 - n ^ 2), by dsimp only [a]; ring⟩
  have hb : IsSquare b := ⟨4 * m * n * (m ^ 2 - n ^ 2) ^ 2, by dsimp only [b]; ring⟩
  have hc : IsSquare c := ⟨(m ^ 2 + n ^ 2) * shiftedQuartic m n, by dsimp only [c]; ring⟩
  have hsum : IsSquare (a + b + c) := by
    refine ⟨(m ^ 2 + n ^ 2) ^ 3, ?_⟩
    dsimp only [a, b, c]
    ring
  have hpairs : IsSquare (a * b + b * c + c * a) := by
    refine ⟨4 * m * n ^ 11 - 20 * m ^ 3 * n ^ 9 + 104 * m ^ 5 * n ^ 7 - 104 * m ^ 7 * n ^ 5 +
      20 * m ^ 9 * n ^ 3 - 4 * m ^ 11 * n, ?_⟩
    dsimp only [a, b, c]
    ring
  unfold HasSquareElementarySymmetricFunctions
  exact ⟨⟨hsum, hpairs, (ha.mul hb).mul hc⟩, ha, hb, hc⟩

end MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted
