/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FenceTiling
import Mathlib.Data.Fintype.Basic

open MetaMathlibExt

-- Even with no permitted displacements, the permutation of the empty board gives the empty tiling.
example :
    ((fenceTiling_strongPerm_bijection ∅ 0).2 (Equiv.refl _) (fun i => i.elim0)).exists.choose =
      ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  have h := ((fenceTiling_strongPerm_bijection ∅ 0).2 (Equiv.refl _)
    (fun i => i.elim0)).exists.choose_spec
  exact Nat.not_lt_zero _ (h.1.1 f hf).1

-- The fence from slot 0 to 3 and the fence from 1 to 2 give opposite signed displacements.
example : ∃ π : Equiv.Perm (Fin 2), π 0 = 1 ∧ π 1 = 0 := by
  let t : Finset (ℕ × ℕ) := {(0, 1), (1, 0)}
  obtain ⟨π, ⟨_, hπ⟩, _⟩ := (fenceTiling_strongPerm_bijection {-1, 1} 2).1 t (by
    constructor
    · decide
    · intro x hx
      have slots : ∀ x : Fin 4, ∃! f : {f // f ∈ t},
          x.val = f.val.1 ∨ x.val = f.val.1 + 1 + 2 * f.val.2 := by
        unfold ExistsUnique
        decide
      obtain ⟨f, hf, huniq⟩ := slots ⟨x, hx⟩
      exact ⟨f.val, ⟨f.property, hf⟩, fun g hg => congrArg Subtype.val (huniq ⟨g, hg.1⟩ hg.2)⟩)
  have h₀ := (hπ 0 (0, 1) (by decide)).1 rfl
  have h₁ := (hπ 1 (1, 0) (by decide)).2 rfl
  refine ⟨π, Fin.ext ?_, Fin.ext ?_⟩
  · change (π 0).val = 1
    change ((π 0).val : ℤ) = 0 + 1 at h₀
    omega
  · change (π 1).val = 0
    change ((π 1).val : ℤ) = 1 - 0 - 1 at h₁
    omega
