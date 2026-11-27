/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Lucas

/-!
# Scaling both binomial arguments by a prime power

Multiplication by `p ^ r` appends `r` zero digits in base `p` to both arguments.
Each new digit contributes `0.choose 0 = 1` to the product in Lucas's theorem.
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Binomial coefficients $\binom{p^r a}{p^r b}$ modulo $p$.** Let $p$ be a prime, let $r \ge 1$,
and let $a, b$ be natural numbers not divisible by $p$. Then
$\binom{p^r a}{p^r b} \equiv \binom{a}{b} \pmod{p}$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Corollary 15
(`jis-2025-25.2.2-cor-15`). -/
public theorem choose_pow_mul_modEq {p a b r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hpa : ¬p ∣ a) (hpb : ¬p ∣ b) : (p ^ r * a).choose (p ^ r * b) ≡ a.choose b [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  exact Choose.choose_pow_mul_pow_mul_modEq_choose_nat

end MetaMathlibExt
