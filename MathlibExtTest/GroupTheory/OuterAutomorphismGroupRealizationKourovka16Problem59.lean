/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.OuterAutomorphismGroupRealizationKourovka16Problem59
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic

namespace MathlibExtTest.GroupTheory.OuterAutomorphismGroupRealizationKourovka16Problem59

open MathlibExt.GroupTheory.OuterAutomorphismGroupRealizationKourovka16Problem59Wanted

-- A realization also exists when the target is the trivial group.
example :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (φ : MulAut G →* PUnit.{1}),
      Function.Surjective φ ∧ φ.ker = (MulAut.conj : G →* MulAut G).range :=
  everyFiniteGroupIsOuterAutomorphismGroup_holds PUnit.{1}

-- Every outer class of the realization has the expected fiber over a permutation.
example :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (φ : MulAut G →* Equiv.Perm (Fin 3)),
      Function.Surjective φ ∧
      ∀ a b : MulAut G, φ a = φ b ↔ ∃ g : G, a * b⁻¹ = MulAut.conj g := by
  obtain ⟨G, _, _, φ, hφ, hk⟩ :=
    everyFiniteGroupIsOuterAutomorphismGroup_holds (Equiv.Perm (Fin 3))
  refine ⟨G, inferInstance, inferInstance, φ, hφ, fun a b => ?_⟩
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
  change a * b⁻¹ ∈ φ.ker ↔ _
  rw [hk]
  exact exists_congr fun g => eq_comm

end MathlibExtTest.GroupTheory.OuterAutomorphismGroupRealizationKourovka16Problem59
