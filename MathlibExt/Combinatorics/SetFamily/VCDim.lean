/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SetFamily.Shatter

/-!
# The VC dimension of a set family on a finite ground set

Mathlib defines shattering (`Finset.Shatters`), the shatterer and the VC dimension
`Finset.vcDim` of a family `𝒜 : Finset (Finset α)`, and proves the Sauer–Shelah lemma
(`Finset.card_le_card_shatterer`, `Finset.card_shatterer_le_sum_vcDim`). This file adds the
trivial upper bound of the VC dimension by the size of the ground set, which is needed to apply
the counting bound `Real.sum_choose_le_exp_mul_div_pow` (it assumes `vcDim ≤ |α|`).
-/

@[expose] public section

set_option autoImplicit false

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- **The VC dimension is at most the size of the ground set.** For a family `𝒜` of subsets
of a finite type `α`, `𝒜.vcDim ≤ |α|`, because every shattered set is a subset of `α`
(VC dimension as in Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, CUP 2014,
Definition 6.5). -/
theorem vcDim_le_card [Fintype α] (𝒜 : Finset (Finset α)) : 𝒜.vcDim ≤ Fintype.card α := by
  unfold vcDim
  exact Finset.sup_le fun s _ => Finset.card_le_univ s

end Finset
