/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SmoothPrimeGapsInfinitePrimeTuplesSmoothGaps

/-!
# Tests for prime m-tuples with smooth gaps

Applying the theorem at `m = 2`, `k = 50` and at `m = 3`, `k = 100` shows that a prime pair or
triple with smooth gaps exists, assuming the Maynard–Tao hypothesis `hk` at those values. The
examples are conditional: Wu's Table 1 gives `k₂ = 50` but `k₃ = 35265`, so the hypothesis at
`m = 3`, `k = 100` is not known to hold.
-/

namespace MathlibExtTest.NumberTheory.SmoothPrimeGapsInfinitePrimeTuplesSmoothGaps

open MetaMathlibExt

/-- From Maynard–Tao for pairs: a prime pair with 50-smooth gap exists. -/
example (hk : ∀ H : Finset ℤ, IsAdmissibleFinset H → 50 ≤ H.card →
    {n : ℤ | 2 ≤ (H.filter (fun h => (n + h).toNat.Prime)).card}.Infinite) :
    ∃ P : Fin 2 → ℕ, (∀ i, (P i).Prime) ∧
      P 0 < P 1 ∧ P 1 - P 0 ∈ Nat.smoothNumbers 51 := by
  have hinf := infinite_prime_tuples_smooth_gaps 2 50 (by decide) hk
  obtain ⟨P, hprime, hmono⟩ := hinf.nonempty
  have h01 := hmono 1 0 (by decide)
  exact ⟨P, hprime, h01.1, h01.2⟩

/-- Assuming the hypothesis `hk` at `m = 3`, `k = 100`: a prime triple with 100-smooth gaps
exists. -/
example (hk : ∀ H : Finset ℤ, IsAdmissibleFinset H → 100 ≤ H.card →
    {n : ℤ | 3 ≤ (H.filter (fun h => (n + h).toNat.Prime)).card}.Infinite) :
    ∃ P : Fin 3 → ℕ, (∀ i, (P i).Prime) ∧ P 0 < P 1 ∧ P 1 < P 2 ∧
      P 1 - P 0 ∈ Nat.smoothNumbers 101 ∧ P 2 - P 1 ∈ Nat.smoothNumbers 101 ∧
      P 2 - P 0 ∈ Nat.smoothNumbers 101 := by
  have hinf := infinite_prime_tuples_smooth_gaps 3 100 (by decide) hk
  obtain ⟨P, hprime, hmono⟩ := hinf.nonempty
  have h10 := hmono 1 0 (by decide)
  have h21 := hmono 2 1 (by decide)
  have h20 := hmono 2 0 (by decide)
  exact ⟨P, hprime, h10.1, h21.1, h10.2, h21.2, h20.2⟩

end MathlibExtTest.NumberTheory.SmoothPrimeGapsInfinitePrimeTuplesSmoothGaps
