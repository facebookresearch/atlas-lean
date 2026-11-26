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
# Nonvanishing of the sum-plus-product family modulo primes congruent to one modulo four

The proof uses the nonvanishing direction of `sumAddMulProd_one_classification`.

## References

* Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem to Some
  Symmetric Functions*, INTEGERS 26 (2026), Article A25, pp. 1–12, Lemma 5 and Theorem 3.
* Arie Bialostocki and P. Dierker, *Zero sum Ramsey theorems*, Congressus Numerantium 70
  (1990), pp. 119–130, Theorem 3.6, cited by Bialostocki and Oles in Lemma 5.
-/

namespace MetaMathlibExt

/-- **$F_1$ modulo a prime $n \equiv 1 \pmod 4$ is not $m$-vanishing for $m > 0$.** Let $n$ be
a prime with $n \equiv 1 \pmod 4$. Then for every $m > 0$ the sum-plus-product family $F_1$
over $\mathbb{Z}/n$, $F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$, is not
$m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 5
(`integers-2026-A25-lem-5`), quoting Theorem 3.6 of Bialostocki and Dierker. -/
public theorem not_isMVanishingFamily_sumAddMulProd_one_prime_one_mod_four {n : ℕ}
    (hp : n.Prime) (h4 : n % 4 = 1) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n)) := by
  have hn : 1 < n := hp.two_le
  have hne : n ∉ ({2, 3, 4, 6, 8} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (sumAddMulProd_one_classification hn).1 hne m hm

end MetaMathlibExt
