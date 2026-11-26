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
# Choudhry's family (3.5) of integer triples with square symmetric functions

Choudhry's family (3.5) has square elementary symmetric functions for all integer parameters.
The proof supplies polynomial square roots, so it also applies when an entry vanishes.

Source: Ajai Choudhry, *Three Integers Whose Sum, Product, and the Sum of the
Products of the Integers, Taken Two at a Time, Are Perfect Squares*, INTEGERS 26 (2026),
Article A35, Theorem 1, family (3.5).
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

local notation "firstShiftedSextic" s:arg t:arg =>
  s ^ 6 - s ^ 4 * t ^ 2 - 5 * s ^ 2 * t ^ 4 + t ^ 6

local notation "secondShiftedSextic" s:arg t:arg =>
  3 * s ^ 6 + s ^ 4 * t ^ 2 + s ^ 2 * t ^ 4 - t ^ 6

/-- **Choudhry's family (3.5) of integer triples with square symmetric functions.** For all
integers $s$ and $t$, let $f = s^6 - s^4 t^2 - 5 s^2 t^4 + t^6$ and
$g = 3 s^6 + s^4 t^2 + s^2 t^4 - t^6$, and put $a = 4 s^4 t^2 (s^2 + t^2) f^2$,
$b = (s^4 - t^4)^2 f^2$ and $c = 4 s^2 t^4 (s^2 + t^2) g^2$. Then each of $a + b + c$,
$ab + bc + ca$ and $abc$ is the square of an integer.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the
Integers, Taken Two at a Time, Are Perfect Squares", Theorem 1, family (3.5). -/
theorem hasSquareElementarySymmetricFunctions_family35
    (s t : ℤ) :
    HasSquareElementarySymmetricFunctions
      (4 * s ^ 4 * t ^ 2 * (s ^ 2 + t ^ 2) *
        (firstShiftedSextic s t) ^ 2)
      ((s ^ 4 - t ^ 4) ^ 2 * (firstShiftedSextic s t) ^ 2)
      (4 * s ^ 2 * t ^ 4 * (s ^ 2 + t ^ 2) *
        (secondShiftedSextic s t) ^ 2) := by
  refine ⟨⟨(s ^ 2 + t ^ 2) * (s ^ 8 + 10 * s ^ 4 * t ^ 4 - 4 * s ^ 2 * t ^ 6 + t ^ 8), ?_⟩,
    ⟨2 * s * t * (s ^ 2 + t ^ 2) * firstShiftedSextic s t *
      (s ^ 10 + 3 * s ^ 8 * t ^ 2 + 8 * s ^ 6 * t ^ 4 - 4 * s ^ 4 * t ^ 6 - s ^ 2 * t ^ 8 + t ^ 10),
      ?_⟩,
    ⟨4 * s ^ 3 * t ^ 3 * (s ^ 2 + t ^ 2) * (s ^ 4 - t ^ 4) *
      (firstShiftedSextic s t) ^ 2 * secondShiftedSextic s t, ?_⟩⟩ <;> ring

end MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted
