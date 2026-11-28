/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CyclotomicProductRamanujanSums
public import MathlibExt.NumberTheory.CyclotomicProductRamanujanSumsTendstoProdCyclotomicHatInvRootOne

/-! # Constancy of an infinite cyclotomic product

Re-exports Bal's theorem that `∏_{n ≥ 1} Φ̂ₙ(z)^{-1/n} ≡ 1` on the open unit
disk, where `Φ̂ₙ(z) = ∏_{ζ primitive n-th root of unity} (1 - z ζ)`, proved in
`MathlibExt.NumberTheory.CyclotomicProductRamanujanSumsTendstoProdCyclotomicHatInvRootOne`,
along with `MathlibExt.NumberTheory.CyclotomicProductRamanujanSums`.
-/
