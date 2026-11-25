/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.GeneralizedFermatShiftDivisibility

/-!
# Prime factor counts of generalized Fermat numbers

For an odd exponent base, this module proves that the number of prime factors counted with
multiplicity is nondecreasing along the generalized Fermat sequence.
-/

namespace MetaMathlibExt

/-- **Monotonicity of the number of prime factors of generalized Fermat numbers.** For natural
numbers $a$, $b$ and $n$ write $F_n(a, b) = a^{b^n} + 1$, and let $\Omega(N)$ be the number of
prime factors of $N$ counted with multiplicity. If $a, b \ge 2$ and $b$ is odd, then
$\Omega(F_n(a, b)) \le \Omega(F_m(a, b))$ for all natural numbers $n \le m$.

The source writes $\varphi_n(a, b)$ for $\Omega(F_n(a, b))$. Its open question on
$\varphi_n(2, 2)$ and its list of values of $\varphi_n(2, 2)$ are not stated here.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Corollary 1 (`integers-2026-A77-cor-1`). -/
public theorem monotone_cardFactors_pow_pow_add_one {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hbo : Odd b) :
    Monotone fun n : ℕ => ArithmeticFunction.cardFactors (a ^ b ^ n + 1) := by
  refine monotone_nat_of_le_succ fun n => ?_
  have hD : 2 ≤ a ^ b ^ n + 1 := Nat.succ_le_succ (Nat.one_le_pow _ _ (by omega))
  have hdvd : a ^ b ^ n + 1 ∣ a ^ b ^ (n + 1) + 1 :=
    (dvd_pow_pow_add_one_shift ha hb hD dvd_rfl).1 hbo 1 le_rfl
  simp only [ArithmeticFunction.cardFactors_apply]
  exact (Nat.primeFactorsList_sublist_of_dvd hdvd (Nat.succ_ne_zero _)).length_le

end MetaMathlibExt
