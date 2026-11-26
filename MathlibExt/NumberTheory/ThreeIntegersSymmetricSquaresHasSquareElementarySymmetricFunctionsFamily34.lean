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
# Choudhry's family (3.4) of integer triples with square symmetric functions

For integers `s` and `t`, the triple `a = 4 * s ^ 4 * t ^ 2 * (s ^ 2 + t ^ 2)`,
`b = 4 * s ^ 2 * t ^ 4 * (s ^ 2 + t ^ 2)` and `c = (s ^ 4 - t ^ 4) ^ 2` has square
elementary symmetric functions (`hasSquareElementarySymmetricFunctions_family34`):
`a + b + c`, `a * b + b * c + c * a` and `a * b * c` are each the square of an integer.

Source: Ajai Choudhry, *Three Integers Whose Sum, Product, and the Sum of the
Products of the Integers, Taken Two at a Time, Are Perfect Squares*, INTEGERS,
volume 26, paper A35. The PDF is
https://math.colgate.edu/~integers/aa35/aa35.pdf.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

/-- **Choudhry's family (3.4) of integer triples with square symmetric functions.** For all
integers $s$ and $t$, put $a = 4 s^4 t^2 (s^2 + t^2)$, $b = 4 s^2 t^4 (s^2 + t^2)$ and
$c = (s^4 - t^4)^2$. Then each of $a + b + c$, $ab + bc + ca$ and $abc$ is the square of an
integer.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the
Integers, Taken Two at a Time, Are Perfect Squares", Theorem 1, family (3.4). -/
theorem hasSquareElementarySymmetricFunctions_family34
    (s t : ℤ) :
    HasSquareElementarySymmetricFunctions
      (4 * s ^ 4 * t ^ 2 * (s ^ 2 + t ^ 2))
      (4 * s ^ 2 * t ^ 4 * (s ^ 2 + t ^ 2))
      ((s ^ 4 - t ^ 4) ^ 2) := by
  refine ⟨⟨(s ^ 2 + t ^ 2) ^ 2, ?_⟩,
    ⟨2 * s * t * (s ^ 2 + t ^ 2) * (s ^ 4 + t ^ 4), ?_⟩,
    ⟨4 * s ^ 3 * t ^ 3 * (s ^ 2 + t ^ 2) * (s ^ 4 - t ^ 4), ?_⟩⟩ <;> ring

end MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted
