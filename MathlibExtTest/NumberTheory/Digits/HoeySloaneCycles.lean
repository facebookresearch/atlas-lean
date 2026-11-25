/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.Perm.Cycle.Concrete
import MathlibExt.NumberTheory.Digits.HoeySloaneCycles

open MetaMathlibExt

-- The loop in Holt's base-four word must close after one edge.
example :
    ∃ (m : ℕ) (v : Fin (m + 1) → ℕ), m = 0 ∧
      ∃ i, (0, 0) = (v i, v (finRotate (m + 1) i)) := by
  let d : Fin 4 → ℕ := ![0, 2, 1, 3]
  let dh : Fin 4 → ℕ := ![0, 3, 2, 1]
  let σ : Equiv.Perm (Fin 4) := c[1, 3, 2]
  have hσ : dh = d ∘ σ := by decide +revert
  have he : (0, 0) ∈ Finset.univ.image (fun j => (d j, dh j)) :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  obtain ⟨m, v, hinj, -, i, hi⟩ :=
    hoeySloaneWord_inputs_union_cycles 2 4 (by decide) (by decide) d dh
      isHoeySloaneWord_two_four_example σ hσ (0, 0) he
  have hfix := hinj ((congrArg Prod.fst hi).symm.trans (congrArg Prod.snd hi))
  have hval := congrArg Fin.val hfix
  rw [coe_finRotate] at hval
  have hm : m = 0 := by
    split at hval
    · rename_i hi
      simpa only [hi, Fin.val_last] using hval
    · omega
  exact ⟨m, v, hm, i, hi⟩

-- Repeating the word gives a six-index orbit with repeated vertices.
-- The edge (2, 3) belongs to a strictly shorter cycle of distinct digits.
example :
    let d : Fin 8 → ℕ := ![0, 2, 1, 3, 0, 2, 1, 3]
    let dh : Fin 8 → ℕ := ![0, 3, 2, 1, 0, 3, 2, 1]
    ∃ (m : ℕ) (v : Fin (m + 1) → ℕ), m + 1 < 6 ∧ Function.Injective v ∧
      (∀ i, (v i, v (finRotate (m + 1) i)) ∈ Finset.univ.image (fun j => (d j, dh j))) ∧
        ∃ i, (2, 3) = (v i, v (finRotate (m + 1) i)) := by
  intro d dh
  let σ : Equiv.Perm (Fin 8) := c[1, 3, 2, 5, 7, 6]
  have hσ : dh = d ∘ σ := by decide +revert
  have hs : IsHoeySloaneWord 2 4 d dh := by
    unfold IsHoeySloaneWord IsMotherGraphEdge
    decide +revert
  have he : (2, 3) ∈ Finset.univ.image (fun j => (d j, dh j)) :=
    Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  obtain ⟨m, v, hinj, hedges, hwitness⟩ :=
    hoeySloaneWord_inputs_union_cycles 2 4 (by decide) (by decide) d dh hs σ hσ (2, 3) he
  have hdigit (i : Fin (m + 1)) : v i < 4 := by
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (hedges i)
    have hfirst : d j = v i := congrArg Prod.fst hj
    rw [← hfirst]
    exact (hs.1 j).1
  let embed (i : Fin (m + 1)) : Fin 4 := ⟨v i, hdigit i⟩
  have hcard := Fintype.card_le_of_injective embed (fun _ _ h => hinj (congrArg Fin.val h))
  simp only [Fintype.card_fin] at hcard
  exact ⟨m, v, by omega, hinj, hedges, hwitness⟩
