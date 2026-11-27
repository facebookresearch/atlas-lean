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
# Choudhry's family (3.6) of integer triples with square symmetric functions

The sum, sum of pairwise products and product are squares of explicit integer polynomials.

## References

* Ajai Choudhry, *Three Integers Whose Sum, Product, and the Sum of the Products of the Integers,
  Taken Two at a Time, Are Perfect Squares*, INTEGERS 26 (2026), Article A35, pp. 1–15,
  Theorem 1, family (3.6). https://math.colgate.edu/~integers/aa35/aa35.pdf
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

local notation "firstShiftedSextic" s:arg t:arg =>
  s ^ 6 - s ^ 4 * t ^ 2 - 5 * s ^ 2 * t ^ 4 + t ^ 6
local notation "secondShiftedSextic" s:arg t:arg =>
  3 * s ^ 6 + s ^ 4 * t ^ 2 + s ^ 2 * t ^ 4 - t ^ 6

/-- **Choudhry's family (3.6) of integer triples with square symmetric functions.** For all
integers $s$ and $t$, let $f = s^6 - s^4 t^2 - 5 s^2 t^4 + t^6$ and
$g = 3 s^6 + s^4 t^2 + s^2 t^4 - t^6$, and put $a = t^2 (s^2 - t^2)^2 (s^2 + t^2) g^2$,
$b = 4 s^4 t^4 g^2$ and $c = s^2 (s^2 - t^2)^2 (s^2 + t^2) f^2$. Then each of $a + b + c$,
$ab + bc + ca$ and $abc$ is the square of an integer.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the
Integers, Taken Two at a Time, Are Perfect Squares", Theorem 1, family (3.6). -/
theorem hasSquareElementarySymmetricFunctions_family36
    (s t : ℤ) :
    HasSquareElementarySymmetricFunctions
      (t ^ 2 * (s ^ 2 - t ^ 2) ^ 2 * (s ^ 2 + t ^ 2) *
        (secondShiftedSextic s t) ^ 2)
      (4 * s ^ 4 * t ^ 4 * (secondShiftedSextic s t) ^ 2)
      (s ^ 2 * (s ^ 2 - t ^ 2) ^ 2 * (s ^ 2 + t ^ 2) *
        (firstShiftedSextic s t) ^ 2) := by
  unfold HasSquareElementarySymmetricFunctions
  refine ⟨⟨s ^ 10 + 3 * s ^ 8 * t ^ 2 + 8 * s ^ 6 * t ^ 4 - 4 * s ^ 4 * t ^ 6 -
    s ^ 2 * t ^ 8 + t ^ 10, ?_⟩,
    ⟨s * t ^ 19 - 5 * s ^ 3 * t ^ 17 + 12 * s ^ 5 * t ^ 15 - 4 * s ^ 7 * t ^ 13 -
      10 * s ^ 9 * t ^ 11 - 22 * s ^ 11 * t ^ 9 - 4 * s ^ 13 * t ^ 7 +
      28 * s ^ 15 * t ^ 5 + s ^ 17 * t ^ 3 + 3 * s ^ 19 * t, ?_⟩,
    ⟨2 * s ^ 3 * t ^ 3 * (s ^ 2 - t ^ 2) ^ 2 * (s ^ 2 + t ^ 2) *
      (firstShiftedSextic s t) * (secondShiftedSextic s t) ^ 2, ?_⟩⟩ <;> ring

end MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted
