/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FittingClassWithoutInjectorKourovka12Problem96
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.SetLike.Fintype

open MathlibExt.GroupTheory.FittingClassWithoutInjectorKourovka12Problem96Wanted

-- A class-maximal subgroup of the whole group can fail the test on a proper subnormal subgroup.
example : ∃ (X : GroupClass) (G : Type) (_ : Group G) (_ : Finite G) (V N : Subgroup G),
    IsFitting X ∧ ¬ Group.IsSolvable G ∧ IsXMaximalIn X V ⊤ ∧ N.IsSubnormal ∧ N ≠ ⊤ ∧
      ¬ IsXMaximalIn X (V ⊓ N) N := by
  classical
  obtain ⟨X, hX, ⟨H, _, _, hH⟩, G, _, _, hG, hNo⟩ := fittingClassWithoutInjectors_holds
  have hbot : X.mem (⊥ : Subgroup G) :=
    X.iso (⊥ : Subgroup H) _ MulEquiv.ofUnique (hX.1 H ⊥ inferInstance hH)
  obtain ⟨V, _, hmax⟩ := Finite.exists_le_maximal (p := fun V : Subgroup G ↦ X.mem V) hbot
  have hV : IsXMaximalIn X V ⊤ := ⟨le_top, hmax.1, fun W hVW _ hW ↦
    hVW.not_ge (hmax.2 hW hVW.le)⟩
  have hn := hNo V
  unfold IsInjector at hn
  push Not at hn
  obtain ⟨N, hN, hfail⟩ := hn
  refine ⟨X, G, _, inferInstance, V, N, hX, hG, hV, hN, ?_, hfail⟩
  rintro rfl
  exact hfail (by simpa using hV)
