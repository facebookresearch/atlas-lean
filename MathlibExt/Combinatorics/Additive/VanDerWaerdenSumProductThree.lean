/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductClassification

/-!
# Vanishing of the sum-plus-product family modulo three

The modulus-three case of the vanishing classification gives full vanishing for `F₁`.
-/

namespace MetaMathlibExt

/-- **The sum-plus-product family is vanishing over $\mathbb{Z}/3\mathbb{Z}$.** Let $F_1$ be the
family over $\mathbb{Z}/3\mathbb{Z}$ sending a block $(b_1, \dots, b_l)$ to
$\sum_i b_i + \prod_i b_i$. Then $F_1$ is vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 1
(`integers-2026-A25-lem-1`). -/
public theorem isVanishingFamily_sumAddMulProd_one_three :
    IsVanishingFamily (sumAddMulProdFamily (1 : ZMod 3)) :=
  (sumAddMulProd_one_classification (n := 3) (by decide)).2.1 (by decide)

end MetaMathlibExt
