/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PolynormalParanormalSubgroupKourovka14Problem50
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

open MathlibExt.GroupTheory.PolynormalParanormalSubgroupKourovka14Problem50Wanted

variable {G : Type*} [Group G]

-- Conjugating a cyclic subgroup uses the right-conjugation convention on its generator.
example (a x : G) :
    conjSubgroup (Subgroup.zpowers a) x = Subgroup.zpowers (x⁻¹ * a * x) := by
  rw [conjSubgroup, MonoidHom.map_zpowers]
  simp

-- The zero and first powers of x give the two subgroups in the paranormal condition.
example (A : Subgroup G) (hA : IsParanormal A) : IsPolynormal A := by
  intro x
  have h : A ⊔ conjSubgroup A x ≤ ⨆ n : ℤ, conjSubgroup A (x ^ n) := by
    apply sup_le
    · apply le_iSup_of_le (0 : ℤ)
      rw [zpow_zero]
      intro y hy
      exact ⟨y, hy, by simp⟩
    · apply le_iSup_of_le (1 : ℤ)
      simp
  exact (hA x).trans (iSup₂_le fun u hu => le_iSup₂_of_le u (h hu) le_rfl)
