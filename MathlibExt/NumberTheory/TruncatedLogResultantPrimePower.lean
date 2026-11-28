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
in degree `p ^ e` is nonzero modulo `p`. For any odd prime `p` and positive `e`,
it is also nonzero modulo `p` in degree `p ^ (2 * e)`. The modular argument does
not require `p ≠ 2`, but the even-power statement retains it as in Theorem 2.

## References

* John Cullinan and Rylan Gajek-Leonard, *On the Discriminants of Truncated Logarithmic
  Polynomials*, INTEGERS 25 (2025), Article A39, pp. 1–12, Theorems 2 and 4.
* Khosro Monsef Shokri, Jafar Shaffaf, and Reza Taleb, *Galois groups of Taylor polynomials
  of some elementary functions*, International Journal of Number Theory 15 (6) (2019),
  pp. 1127–1141, Theorem 3.1 (the prime-degree antecedent cited for Theorem 4).

The even-power proof follows `not_dvd_truncatedLogResultantProduct_of_prime_power` in this
module, reusing `monomial_resultant_ne_zero` from
`MathlibExt.NumberTheory.TruncatedLogDiscriminant`.
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

open not_isSquare_discr_truncatedLog_three_five_seven_mul in
set_option linter.unusedVariables false in
/-- **An odd prime $p$ does not divide $\mathcal{P}_{p^{2e}}$.** Let $p$ be an odd prime, let
$e \ge 1$, and let $\mathcal{P}_n$ be the truncated logarithmic resultant product. Then $p$ does
not divide $\mathcal{P}_{p^{2e}}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 2
(`integers-2025-A39-thm-2`). -/
public theorem not_dvd_truncatedLogResultantProduct_of_even_power {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    ¬ (p : ℤ) ∣ truncatedLogResultantProduct (p ^ (2 * e)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hpos : 0 < p ^ (2 * e) := pow_pos hp.pos _
  exact monomial_resultant_ne_zero (e := 2 * e) (by omega) le_rfl
    (pow_lt_pow_right₀ hp.one_lt (Nat.lt_succ_self _)) (by omega)

end MetaMathlibExt
