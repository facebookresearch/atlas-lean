/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductClassification

/-!
# Nonvanishing of the sum-plus-product family modulo primes congruent to three modulo four

For a prime $n > 3$ with $n \equiv 3 \pmod 4$ and any $m > 0$, the sum-plus-product family
$F_1$ over $\mathbb{Z}/n$ is not $m$-vanishing. We use the nonvanishing case of the
classification rather than repeating the periodic-word construction of Lemma 7.

## References

* Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem to Some
  Symmetric Functions*, INTEGERS 26 (2026), Article A25, pp. 1–12, Lemma 7 and Theorem 3(a)
  (<https://math.colgate.edu/~integers/aa25/aa25.pdf>).
* `sumAddMulProd_one_classification` in `VanDerWaerdenSumProductClassification` supplies the
  classification. The proof follows `not_isMVanishingFamily_sumAddMulProd_one_prime_one_mod_four`
  in `VanDerWaerdenSumProductPrimeOneModFour`.
-/

namespace MetaMathlibExt

/-- **$F_1$ modulo a prime $n > 3$ with $n \equiv 3 \pmod 4$ is not $m$-vanishing for $m > 0$.**
Let $n > 3$ be a prime with $n \equiv 3 \pmod 4$. Then for every $m > 0$ the sum-plus-product
family $F_1$ over $\mathbb{Z}/n$, $F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$, is
not $m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 7
(`integers-2026-A25-lem-7`). -/
public theorem not_isMVanishingFamily_sumAddMulProd_one_prime_three_mod_four
    {n : ℕ} (hp : n.Prime) (h3 : 3 < n) (h4 : n % 4 = 3) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n)) := by
  have hne : n ∉ ({2, 3, 4, 6, 8} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (sumAddMulProd_one_classification hp.two_le).1 hne m hm

end MetaMathlibExt
