/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedTau
import Mathlib.Data.Nat.Prime.Int

/-!
# Ramanujan's tau function modulo three

For positive `n`, `ramanujanTau_three_mul_modEq_zero` shows that `3` divides `τ(3n)`.
The generalized tau divisibility formula gives `24 ∣ (3n - 1) * τ(3n)`, and `3 ∤ 3n - 1`.
-/

namespace MetaMathlibExt

/-- **Ramanujan's congruence $\tau(3n) \equiv 0 \pmod 3$.** Let $\tau = \tau_{24}$ be Ramanujan's
tau function, where $\tau_k$ is the generalized tau function. For every integer $n \ge 1$,
$\tau(3n) \equiv 0 \pmod 3$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Corollary 1 (`integers-2024-A39-cor-1`). -/
public theorem ramanujanTau_three_mul_modEq_zero (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (3 * n) ≡ 0 [ZMOD 3] := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show 3 * n ≠ 0 by omega)
  have h := mul_generalizedTau_succ_modEq_zero m (by omega) 24 (by decide)
  have h₃ := h.of_dvd (by decide : (3 : ℤ) ∣ |24|)
  rw [hm, Int.modEq_zero_iff_dvd]
  exact (Int.prime_three.dvd_or_dvd (Int.modEq_zero_iff_dvd.mp h₃)).resolve_left (by omega)

end MetaMathlibExt
