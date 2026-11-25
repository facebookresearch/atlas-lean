/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.MassiveIndependentSetFreeGroupKourovka10Problem13

open MathlibExt.GroupTheory.MassiveIndependentSetFreeGroupKourovka10Problem13Wanted

-- A singleton is normally independent precisely when its word is nontrivial.
example (w : FreeGroup (Fin 2)) : IsNormallyIndependent {w} ↔ w ≠ 1 := by
  simp [IsNormallyIndependent, Subgroup.normalClosure_empty]

-- A generator and a distinct conjugate of it cannot both serve as independent relators.
example : ¬ IsNormallyIndependent
    {FreeGroup.of (0 : Fin 2), FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹} := by
  let a := FreeGroup.of (0 : Fin 2)
  let b := FreeGroup.of (1 : Fin 2)
  let s : Set (FreeGroup (Fin 2)) := {a, b * a * b⁻¹} \ {b * a * b⁻¹}
  intro h
  apply h (b * a * b⁻¹) (by simp [a, b])
  have ha : a ∈ s := ⟨Set.mem_insert _ _, by decide⟩
  exact (Subgroup.normalClosure_normal (s := s)).conj_mem _ (Subgroup.subset_normalClosure ha) b
