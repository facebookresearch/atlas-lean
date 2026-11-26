/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LucasLehmerInfiniteSeeds
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- At the minimum exponent, seed 3 detects the prime 7 and both inputs are odd.
example :
    {S : ℤ | 3 ≤ S ∧ IsOddSquarefreePart (S - 2) 1 ∧ IsOddSquarefreePart (S + 2) 5 ∧
      ((mersenne 3).Prime ↔ (mersenne 3 : ℤ) ∣ (fun x : ℤ => x ^ 2 - 2)^[3 - 2] S)}.Infinite := by
  refine infinite_acceptableSeeds_same_parts (n := 3) (by decide) 3 (by decide) 1 5
    ⟨by decide, squarefree_one, 0, 1, by norm_num⟩
    ⟨by decide, Nat.prime_five.squarefree, 0, 1, by norm_num⟩ ?_
  decide

-- Seed 4 correctly rejects the composite 15; both factorizations use a power of two.
example :
    {S : ℤ | 3 ≤ S ∧ IsOddSquarefreePart (S - 2) 1 ∧ IsOddSquarefreePart (S + 2) 3 ∧
      ((mersenne 4).Prime ↔ (mersenne 4 : ℤ) ∣ (fun x : ℤ => x ^ 2 - 2)^[4 - 2] S)}.Infinite := by
  refine infinite_acceptableSeeds_same_parts (n := 4) (by decide) 4 (by decide) 1 3
    ⟨by decide, squarefree_one, 1, 1, by norm_num⟩
    ⟨by decide, Nat.prime_three.squarefree, 1, 1, by norm_num⟩ ?_
  decide
