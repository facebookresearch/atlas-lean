/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Lucas

/-!
# Prime divisibility of binomial coefficients with unequal prime powers

After removing the common factor `p ^ s` from both arguments by Lucas's theorem,
the upper argument has units digit zero in base `p` and the lower one has positive units digit.
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **$p$ divides $\binom{p^r a}{p^s b}$ when $r > s$.** Let $p$ be a prime, let $r > s$ be
natural numbers, and let $a, b$ be natural numbers not divisible by $p$. Then
$p \mid \binom{p^r a}{p^s b}$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Corollary 14
(`jis-2025-25.2.2-cor-14`). -/
public theorem prime_dvd_choose_pow_mul_pow_mul {p a b r s : ℕ} (hp : p.Prime)
    (hrs : s < r) (hpa : ¬p ∣ a) (hpb : ¬p ∣ b) : p ∣ (p ^ r * a).choose (p ^ s * b) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hrs
  rw [Nat.add_assoc, pow_add, mul_assoc, ← Nat.modEq_zero_iff_dvd]
  refine Choose.choose_pow_mul_pow_mul_modEq_choose_nat.trans ?_
  refine Choose.choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
  have hb : 0 < b % p := Nat.pos_of_ne_zero (mt Nat.dvd_of_mod_eq_zero hpb)
  simp [pow_succ', mul_assoc, Nat.choose_eq_zero_of_lt hb, Nat.ModEq.refl]

end MetaMathlibExt
