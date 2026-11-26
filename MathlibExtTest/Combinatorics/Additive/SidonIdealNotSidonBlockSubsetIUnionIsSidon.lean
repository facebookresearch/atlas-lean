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
