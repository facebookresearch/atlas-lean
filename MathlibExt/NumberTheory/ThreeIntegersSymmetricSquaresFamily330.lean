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
# Choudhry's family (3.30) of square triples with square symmetric functions

The three entries and their three elementary symmetric functions have explicit integer square
roots.

## References

* Ajai Choudhry, *Three Integers Whose Sum, Product, and the Sum of the Products of the Integers,
  Taken Two at a Time, Are Perfect Squares*, INTEGERS 26 (2026), Article A35, pp. 1–15,
  Theorem 2, family (3.30), derived there from Theorem 1, family (3.3).
  https://math.colgate.edu/~integers/aa35/aa35.pdf
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

local notation "shiftedQuartic" m:arg n:arg => m ^ 4 - 6 * m ^ 2 * n ^ 2 + n ^ 4

/-- **Choudhry's family (3.30) of square triples with square symmetric functions.** For all
integers $m$ and $n$, let $Q = m^4 - 6 m^2 n^2 + n^4$ and put $a = (m^4 - n^4)^2 Q^2$,
$b = 4 m^2 n^2 (m^2 + n^2)^2 Q^2$ and $c = 64 m^4 n^4 (m^2 - n^2)^4$. Then each of $a$, $b$,
$c$, $a + b + c$, $ab + bc + ca$ and $abc$ is the square of an integer.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the
Integers, Taken Two at a Time, Are Perfect Squares", Theorem 2, family (3.30). -/
theorem hasSquareElementarySymmetricFunctions_family330_and_entries_square
    (m n : ℤ) :
    let a := (m ^ 4 - n ^ 4) ^ 2 * (shiftedQuartic m n) ^ 2
    let b := 4 * m ^ 2 * n ^ 2 * (m ^ 2 + n ^ 2) ^ 2
      * (shiftedQuartic m n) ^ 2
    let c := 64 * m ^ 4 * n ^ 4 * (m ^ 2 - n ^ 2) ^ 4
    HasSquareElementarySymmetricFunctions a b c ∧
      IsSquare a ∧ IsSquare b ∧ IsSquare c := by
  dsimp only
  unfold HasSquareElementarySymmetricFunctions
  -- The Pythagorean relation `u ^ 2 = v ^ 2 + w ^ 2` gives the symmetric-function roots.
  let u := m ^ 2 + n ^ 2
  let v := m ^ 2 - n ^ 2
  let w := 2 * m * n
  let Q := v ^ 2 - w ^ 2
  let x := u * v * Q
  let y := u * w * Q
  let z := 2 * w ^ 2 * v ^ 2
  refine ⟨⟨⟨v ^ 4 + w ^ 4, ?_⟩, ⟨u ^ 4 * v * w * Q, ?_⟩, ⟨x * y * z, ?_⟩⟩,
    ⟨x, ?_⟩, ⟨y, ?_⟩, ⟨z, ?_⟩⟩ <;> dsimp only [x, y, z, Q, w, v, u] <;> ring

end MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted
