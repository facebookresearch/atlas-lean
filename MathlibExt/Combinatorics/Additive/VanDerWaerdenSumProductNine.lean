/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductClassification

/-!
# Nonvanishing of the sum-plus-product family modulo multiples of nine

The sum-plus-product family is not `m`-vanishing for any positive `m` at any positive multiple
of nine. This specializes the vanishing classification, whose proof for multiples of nine
uses the periodic counterexample with entries `7, 4, 4` modulo nine.

## References

* Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem to Some
  Symmetric Functions*, INTEGERS 26 (2026), Article A25, pp. 1–12, Lemma 9 (pp. 8–9)
  and Theorem 3(a) (p. 4).
-/

namespace MetaMathlibExt

/-- **$F_1$ modulo $9u$ with $u > 0$ is not $m$-vanishing for $m > 0$.** Let $u > 0$ be a natural
number and $n = 9u$. Then for every $m > 0$ the sum-plus-product family $F_1$ over $\mathbb{Z}/n$,
$F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$, is not $m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 9
(`integers-2026-A25-lem-9`). -/
public theorem not_isMVanishingFamily_sumAddMulProd_one_nine_mul {u : ℕ}
    (hu : 0 < u) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod (9 * u))) := by
  have hn : 8 < 9 * u := by omega
  have hne : 9 * u ∉ ({2, 3, 4, 6, 8} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (sumAddMulProd_one_classification (by omega)).1 hne m hm

end MetaMathlibExt
