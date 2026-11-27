/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GoormaghtighPrimes
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NormNum.Prime

/-! # Length-three cases of the Goormaghtigh prime finiteness theorem -/

private def lengthThreePrimes : Set ℕ :=
  {p | p.Prime ∧ ∃ x y m : ℕ, 2 ≤ x ∧ x < y ∧
    p = (x ^ m - 1) / (x - 1) ∧ p = 1 + y + y ^ 2}

example (habc : ∀ ε : ℝ, 0 < ε →
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
      (∏ q ∈ (t.1 * t.2.1 * t.2.2).primeFactors, (q : ℝ)) ^ (1 + ε) ≤ (t.2.2 : ℝ)}.Finite) :
    lengthThreePrimes.Finite := by
  apply (MetaMathlibExt.goormaghtigh_primes_finite_of_abc (habc := habc)).subset
  rintro p ⟨hp, x, y, m, hx, hxy, hpx, hpy⟩
  refine ⟨hp, x, y, m, 3, hx, hxy, le_rfl, hpx.trans (Nat.geomSum_eq hx m).symm, ?_⟩
  simpa [Finset.sum_range_succ] using hpy

-- Both known primes attain the lower bound on the length in the larger base.
example : 31 ∈ lengthThreePrimes :=
  ⟨by norm_num, 2, 5, 5, by decide, by decide, by decide, by decide⟩

example : 8191 ∈ lengthThreePrimes :=
  ⟨by norm_num, 2, 90, 13, by decide, by decide, by decide, by decide⟩
