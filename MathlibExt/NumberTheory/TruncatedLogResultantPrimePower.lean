/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TruncatedLogDiscriminant
import all MathlibExt.NumberTheory.TruncatedLogDiscriminant

/-!
# The truncated logarithmic resultant at prime powers

For a prime `p ≡ 1 (mod 4)` and a positive exponent `e`, the resultant product
in degree `p ^ e` is nonzero modulo `p`.
-/

namespace MetaMathlibExt

open not_isSquare_discr_truncatedLog_three_five_seven_mul in
set_option linter.unusedVariables false in
/-- **A prime $p \equiv 1 \pmod 4$ does not divide $\mathcal{P}_{p^e}$.** Let $p$ be a prime with
$p \equiv 1 \pmod 4$, let $e \ge 1$, and let $\mathcal{P}_n$ be the truncated logarithmic
resultant product. Then $p$ does not divide $\mathcal{P}_{p^e}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 4
(`integers-2025-A39-thm-4`). -/
public theorem not_dvd_truncatedLogResultantProduct_of_prime_power {p e : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (he : 1 ≤ e) :
    ¬ (p : ℤ) ∣ truncatedLogResultantProduct (p ^ e) := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hpos : 0 < p ^ e := pow_pos hp.pos e
  exact monomial_resultant_ne_zero (Nat.ne_of_gt he) le_rfl
    (pow_lt_pow_right₀ hp.one_lt (Nat.lt_succ_self e)) (by omega)

end MetaMathlibExt
