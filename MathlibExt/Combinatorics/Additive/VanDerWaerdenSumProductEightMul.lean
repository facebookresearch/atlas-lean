/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductClassification

/-!
# Nonvanishing of the sum-plus-product family modulo multiples of eight

For a modulus `8 * u` with `1 < u`, the family `F₁` is not `m`-vanishing for any positive `m`.
This is a consequence of the vanishing classification.

## References

* Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem to Some
  Symmetric Functions*, INTEGERS 26 (2026), Article A25, pp. 1–12, Theorem 3(a) (p. 4) and
  Lemma 8 (p. 8).
-/

namespace MetaMathlibExt

/-- **$F_1$ modulo $8u$ with $u > 1$ is not $m$-vanishing for $m > 0$.** Let $u > 1$ be a natural
number and $n = 8u$. Then for every $m > 0$ the sum-plus-product family $F_1$ over $\mathbb{Z}/n$,
$F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$, is not $m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 8
(`integers-2026-A25-lem-8`). -/
public theorem not_isMVanishingFamily_sumAddMulProd_one_eight_mul {u : ℕ}
    (hu : 1 < u) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod (8 * u))) := by
  have hn : 1 < 8 * u := by omega
  have hne : 8 * u ∉ ({2, 3, 4, 6, 8} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (sumAddMulProd_one_classification hn).1 hne m hm

end MetaMathlibExt
