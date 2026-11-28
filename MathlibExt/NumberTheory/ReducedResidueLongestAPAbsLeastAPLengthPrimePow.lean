/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ReducedResidueLongestAP
import MathlibExt.NumberTheory.ReducedResidueAverage
import Mathlib.RingTheory.Radical.NatInt

/-!
# Longest progressions of absolute least residues modulo prime powers

For a prime power `p ^ r` with `r ≥ 1` (and `r ≥ 2` when `p` is odd), every reduced residue
window has longest progression length `p ^ (r - 1)`, so the absolute least length is `p ^ (r - 1)`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6.
-/

namespace MetaMathlibExt

private theorem prime_sub_one_le_pow_pred (p r : ℕ) (hp : p.Prime)
    (h : p = 2 ∨ 2 ≤ r) : p - 1 ≤ p ^ (r - 1) := by
  rcases h with rfl | hr2
  · calc 2 - 1 = 1 := by decide
      _ ≤ 2 ^ (r - 1) := Nat.one_le_pow _ _ (by decide)
  · have h1 : 1 ≤ r - 1 := by omega
    have hpow : p ^ 1 ≤ p ^ (r - 1) := Nat.pow_le_pow_right hp.pos h1
    rw [pow_one] at hpow
    omega

/-- **Longest progressions of absolute least residues: prime powers.** Let $p$ be a prime and
$r \ge 1$, with $r \ge 2$ when $p$ is odd. Then the length $g(p^r)$ of the longest arithmetic
progression in the absolute least reduced residue system modulo $p^r$ is $p^{r-1}$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem absLeastAPLength_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (h : p = 2 ∨ 2 ≤ r) : absLeastAPLength (p ^ r) = p ^ (r - 1) := by
  have hn : 1 < p ^ r := Nat.one_lt_pow (by omega) hp.one_lt
  have hfac : (p ^ r).primeFactors = {p} := Nat.primeFactors_prime_pow (by omega) hp
  have hquot : p ^ r / UniqueFactorizationMonoid.radical (p ^ r) = p ^ (r - 1) := by
    rw [Nat.radical_eq_prod_primeFactors, hfac, Finset.prod_singleton]
    exact Nat.div_eq_of_eq_mul_left hp.pos (pow_sub_one_mul (by omega) p).symm
  unfold absLeastAPLength
  rw [longestAPLength_eq_div_radical _ hn (by
    rw [hquot, hfac, Finset.sup_singleton, id_eq]
    exact prime_sub_one_le_pow_pred p r hp h), hquot]

end MetaMathlibExt
