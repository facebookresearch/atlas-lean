/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductClassification

/-!
# Sum-plus-product vanishing modulo four and eight

The vanishing classification gives consecutive blocks of equal length with zero sum plus product
in every sequence modulo four or eight.
-/

namespace MetaMathlibExt

/-- **The sum-plus-product family is vanishing over $\mathbb{Z}/4\mathbb{Z}$ and
$\mathbb{Z}/8\mathbb{Z}$.** Let $n \in \{4, 8\}$ and let $F_1$ be the family over
$\mathbb{Z}/n\mathbb{Z}$ sending a block $(b_1, \dots, b_l)$ to $\sum_i b_i + \prod_i b_i$. Then
$F_1$ is vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 2
(`integers-2026-A25-lem-2`). -/
public theorem isVanishingFamily_sumAddMulProd_one_four_eight {n : ℕ}
    (hn : n = 4 ∨ n = 8) : IsVanishingFamily (sumAddMulProdFamily (1 : ZMod n)) := by
  apply (sumAddMulProd_one_classification (n := n) (by omega)).2.1
  rcases hn with rfl | rfl <;> decide

end MetaMathlibExt
