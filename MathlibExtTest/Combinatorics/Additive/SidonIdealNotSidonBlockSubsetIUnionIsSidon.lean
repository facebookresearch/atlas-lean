/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.SidonIdealNotSidonBlockSubsetIUnionIsSidon

@[expose] public section

namespace MathlibExtTest.Combinatorics.Additive.SidonIdealNotSidonBlockSubsetIUnionIsSidon

-- The block uses powers of `M`: `5 ^ 2 + 1 * 2 ^ 0 = 26` lies in it.
example : 26 ∈ MetaMathlibExt.sidonBlock 2 1 5 2 :=
  ⟨0, by norm_num, 2, by norm_num, le_rfl, by norm_num⟩

-- Multiples of `M` are not in the block: `11 = 2 * 5 + 1` is absent.
example : 11 ∉ MetaMathlibExt.sidonBlock 2 1 5 2 := by
  rintro ⟨k, hk, l, hl1, hl2, h⟩
  obtain rfl | rfl : k = 0 ∨ k = 1 := (by omega)
  all_goals obtain rfl | rfl : l = 1 ∨ l = 2 := (by omega)
  all_goals norm_num at h

-- With `n = 1`, the block is a singleton, not covered by `Fin 0` sets.
example : ¬ ∃ S : Fin (1 - 1) → Set ℕ, (∀ j, (S j).IsSidon) ∧
    MetaMathlibExt.sidonBlock 1 1 (1 * 2 ^ 1 + 1) ((1 - 1) * Nat.choose 1 2 + 1) ⊆
      ⋃ j, S j :=
  MetaMathlibExt.not_sidonBlock_subset_iUnion_isSidon (by decide) (by decide)

-- With `n = 2` and `C = 1`, one Sidon set does not cover the block.
example : ¬ ∃ S : Fin (2 - 1) → Set ℕ, (∀ j, (S j).IsSidon) ∧
    MetaMathlibExt.sidonBlock 2 1 (1 * 2 ^ 2 + 1) ((2 - 1) * Nat.choose 2 2 + 1) ⊆
      ⋃ j, S j :=
  MetaMathlibExt.not_sidonBlock_subset_iUnion_isSidon (by decide) (by decide)

-- With `n = 3` and `C = 2`, two Sidon sets do not cover the block.
example : ¬ ∃ S : Fin (3 - 1) → Set ℕ, (∀ j, (S j).IsSidon) ∧
    MetaMathlibExt.sidonBlock 3 2 (2 * 2 ^ 3 + 1) ((3 - 1) * Nat.choose 3 2 + 1) ⊆
      ⋃ j, S j :=
  MetaMathlibExt.not_sidonBlock_subset_iUnion_isSidon (by decide) (by decide)

end MathlibExtTest.Combinatorics.Additive.SidonIdealNotSidonBlockSubsetIUnionIsSidon
