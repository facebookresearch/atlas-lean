/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Intrinsic normal two-cores and exact-sequence recognition of their kernels. -/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Subgroup.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The intrinsic normal two-core is the join of all normal two-subgroups of a group. -/
noncomputable def monsterGeometryTwoCore (K : Type*) [Group K] : Subgroup K :=
  sSup {P : Subgroup K | P.Normal ∧ IsPGroup 2 P}

/-- Every actual normal two-subgroup is contained in the intrinsic normal two-core. -/
theorem monsterGeometryNormalTwo_le_core {K : Type*} [Group K]
    (P : Subgroup K) [P.Normal] (hP : IsPGroup 2 P) :
    P ≤ monsterGeometryTwoCore K :=
  le_sSup ⟨inferInstance, hP⟩

/-- An exact projection onto a group with no normal two-subgroup identifies its intrinsic
normal two-core with its kernel, provided the kernel itself is a two-group. -/
theorem monsterGeometryTwoCore_eq_kernel {K L : Type*} [Group K] [Group L]
    (f : K →* L) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    (hL : ∀ P : Subgroup L, P.Normal → IsPGroup 2 P → P = ⊥) :
    monsterGeometryTwoCore K = f.ker := by
  apply le_antisymm
  · apply sSup_le
    intro P hP
    have hn : (P.map f).Normal := hP.1.map f hf
    have he := hL (P.map f) hn (hP.2.map f)
    exact (Subgroup.map_eq_bot_iff P).mp he
  · exact monsterGeometryNormalTwo_le_core f.ker hker

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
