/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FixedSubgroupBasisLengthKourovka14Problem23

/-! # Tests for the rank-uniform fixed-subgroup basis bound -/

open MathlibExt.GroupTheory.FixedSubgroupBasisLengthKourovka14Problem23Wanted

example (f : ℕ → ℕ) (hf : Computable f) :
    ∃ (n : ℕ) (α : MulAut (FreeGroup (Fin n))), ¬ HasShortFixedBasis α (f (autNorm α)) := by
  by_contra! h
  exact fixedSubgroupBasisRecursiveBoundUniform_refuted ⟨f, hf, h⟩

example (α : MulAut (FreeGroup (Fin 0))) : autNorm α = 0 := by
  simp [autNorm]

-- The identity fixes the entire group, whose standard basis has length one in positive rank.
example (n : ℕ) : HasShortFixedBasis (MulEquiv.refl (FreeGroup (Fin (n + 1)))) 1 := by
  have htop : fixedSubgroup (MulEquiv.refl (FreeGroup (Fin (n + 1)))) = ⊤ :=
    top_unique fun _ _ => rfl
  unfold HasShortFixedBasis
  rw [htop]
  refine ⟨n + 1, (FreeGroupBasis.ofFreeGroup _).map Subgroup.topEquiv.symm, ?_⟩
  intro i
  exact (FreeGroup.norm_of i).le
