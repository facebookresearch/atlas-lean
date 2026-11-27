/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for an odd prime quadratic non-residue
-/
module

public import MathlibExt.NumberTheory.LegendreSymbol.OddPrimeNonresidue

@[expose] public section

example (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ legendreSym p q = -1 :=
  legendreSym.exists_odd_prime_eq_neg_one p hp

example [Fact (Nat.Prime 13)] : ∃ q : ℕ, q.Prime ∧ Odd q ∧ legendreSym 13 q = -1 :=
  legendreSym.exists_odd_prime_eq_neg_one 13 (by norm_num)

end
