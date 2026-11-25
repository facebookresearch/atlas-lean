/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.OrderOfElement
import MathlibExt.GroupTheory.SurjectionNoninjectiveOnSubgroupsKourovka17Problem50

open MathlibExt.GroupTheory.SurjectionNoninjectiveOnSubgroupsKourovka17Problem50Wanted

-- A lift of a transposition in S₃ has a nonidentity power in the kernel.
example : ∃ (F : Type) (_ : Group F) (_ : Finite F) (f : F →* Equiv.Perm (Fin 3))
    (u : F) (k : ℤ), f u = Equiv.swap 0 1 ∧ u ^ k ≠ 1 ∧ f (u ^ k) = 1 := by
  obtain ⟨F, _, _, f, hf, hH⟩ := surjectionNoninjectiveOnSubgroups_holds (Equiv.Perm (Fin 3))
  obtain ⟨u, hu⟩ := hf (Equiv.swap 0 1)
  have hu' : u ≠ 1 := by
    rintro rfl
    have h := DFunLike.congr_fun (hu.symm.trans (map_one f)) 0
    simp at h
  let H := Subgroup.zpowers u
  have hker : (f.comp H.subtype).ker ≠ ⊥ :=
    (f.comp H.subtype).ker_eq_bot_iff.not.mpr (hH H (Subgroup.zpowers_ne_bot.mpr hu'))
  obtain ⟨v, hv⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp v.val.property
  refine ⟨F, inferInstance, inferInstance, f, u, k, hu, ?_, ?_⟩
  · intro h
    exact hv (Subtype.ext (Subtype.ext (hk.symm.trans h)))
  · rw [hk]
    exact v.property
