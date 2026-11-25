/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FreeGroupCayleyHamiltonKourovka17Problem32
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

open MathlibExt.GroupTheory.FreeGroupCayleyHamiltonKourovka17Problem32Wanted

-- The refutation supplies a witness with the inclusive and strict bounds of the question.
example : ∃ (n : ℕ) (w : FreeGroup (Fin n)) (φ : MulAut (FreeGroup (Fin n))),
    Subgroup.closure {x | ∃ i ≤ n, x = (φ ^ i) w} = ⊤ ∧
    Subgroup.closure {x | ∃ i < n, x = (φ ^ i) w} ≠ ⊤ := by
  by_contra! h
  exact freeGroupCayleyHamilton_refuted h

-- At rank zero the empty orbit segment generates the trivial group.
example (w : FreeGroup (Fin 0)) (φ : MulAut (FreeGroup (Fin 0))) :
    Subgroup.closure {x | ∃ i < 0, x = (φ ^ i) w} = ⊤ :=
  Subsingleton.elim _ _

-- At rank one every automorphism acts by an integer power, so the extra word is redundant.
example (w : FreeGroup (Fin 1)) (φ : MulAut (FreeGroup (Fin 1)))
    (h : Subgroup.closure {x | ∃ i ≤ 1, x = (φ ^ i) w} = ⊤) :
    Subgroup.closure {x | ∃ i < 1, x = (φ ^ i) w} = ⊤ := by
  let H := Subgroup.closure {x | ∃ i < 1, x = (φ ^ i) w}
  have hw : w ∈ H := Subgroup.subset_closure ⟨0, by decide, by simp⟩
  apply top_unique
  rw [← h, Subgroup.closure_le]
  rintro _ ⟨i, _, rfl⟩
  obtain ⟨m, hm⟩ := (φ ^ i).toMonoidHom.map_cyclic
  exact hm w ▸ H.zpow_mem hw m
