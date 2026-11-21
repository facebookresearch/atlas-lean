/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.Natarajan

import Mathlib.Data.Fintype.Pi

/-!
# Tests for the Natarajan lemma

Checks for `NDimLE` and `tracesCard`: a constant class, full binary-class
shattering, singleton binary dimension bounds, and `#print axioms` probes.
-/

namespace CSLibExtTest.MachineLearning.PACLearning

open Cslib.MachineLearning.PACLearning

theorem constClass_ndimLE_zero :
    NDimLE ({fun _ => (0 : Fin 3)} : Finset ((Fin 2) → Fin 3)) 0 := by
  intro s hs hsh
  obtain ⟨f₀, f₁, hne, hwit⟩ := hsh
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hs
  have hy : y ∈ ({y} : Finset (Fin 2)) := Finset.mem_singleton_self y
  obtain ⟨h, mh, h1, -⟩ := hwit {y} (Finset.Subset.refl _)
  obtain ⟨h', mh', -, h0⟩ := hwit ∅ (Finset.empty_subset _)
  have hh : h = fun _ => (0 : Fin 3) := Finset.mem_singleton.mp mh
  have hh' : h' = fun _ => (0 : Fin 3) := Finset.mem_singleton.mp mh'
  have e1 : h y = f₁ y := h1 y (Finset.mem_singleton_self y)
  have e0 : h' y = f₀ y := h0 y hy (Finset.notMem_empty y)
  have hcontra : f₁ y = f₀ y := by rw [← e1, ← e0, hh, hh']
  exact hne y hy hcontra.symm

theorem constClass_tracesCard_one :
    tracesCard ({fun _ => (0 : Fin 3)} : Finset ((Fin 2) → Fin 3))
      Finset.univ = 1 := by
  decide

theorem allFuncs_shatter :
    NShatters (Finset.univ : Finset ((Fin 2) → Fin 2)) Finset.univ := by
  refine ⟨fun _ => (0 : Fin 2), fun _ => (1 : Fin 2), ?_, ?_⟩
  · decide
  · intro t ht
    refine ⟨fun x => if x ∈ t then (1 : Fin 2) else 0, Finset.mem_univ _, ?_, ?_⟩
    · intro x hxt
      simp [hxt]
    · intro x _ hxt
      simp [hxt]

theorem allFuncs_not_ndimLE_one :
    ¬ NDimLE (Finset.univ : Finset ((Fin 2) → Fin 2)) 1 := by
  intro hle
  have hcard : (Finset.univ : Finset (Fin 2)).card = 1 + 1 := by decide
  exact hle Finset.univ hcard allFuncs_shatter

theorem allFuncs_tracesCard_four :
    tracesCard (Finset.univ : Finset ((Fin 2) → Fin 2)) Finset.univ = 4 := by
  decide

theorem twoConsts_ndimLE_one :
    NDimLE ({fun _ : Fin 1 => (0 : Fin 2), fun _ : Fin 1 => (1 : Fin 2)} :
      Finset ((Fin 1) → Fin 2)) 1 := by
  intro s hs _
  have hle : s.card ≤ 1 := by
    have h := Finset.card_le_univ s
    rw [Fintype.card_fin] at h
    exact h
  omega

theorem twoConsts_shatter_univ :
    NShatters ({fun _ : Fin 1 => (0 : Fin 2), fun _ : Fin 1 => (1 : Fin 2)} :
      Finset ((Fin 1) → Fin 2)) Finset.univ := by
  refine ⟨fun _ => (0 : Fin 2), fun _ => (1 : Fin 2), ?_, ?_⟩
  · decide
  · intro t ht
    by_cases hempty : t = ∅
    · refine ⟨fun _ => (0 : Fin 2), Finset.mem_insert_self _ _, ?_, ?_⟩
      · intro x hxt
        rw [hempty] at hxt
        exact absurd hxt (Finset.notMem_empty x)
      · intro x _ _
        rfl
    · have htU : t = Finset.univ := by
        have hcard1 : (Finset.univ : Finset (Fin 1)).card = 1 := by decide
        have hle : t.card ≤ 1 := by
          have h := Finset.card_le_card (Finset.subset_univ t)
          omega
        have hpos : 0 < t.card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hcard : t.card = 1 := by omega
        have hle' : (Finset.univ : Finset (Fin 1)).card ≤ t.card := by omega
        exact Finset.eq_of_subset_of_card_le (Finset.subset_univ t) hle'
      refine ⟨fun _ => (1 : Fin 2),
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_, ?_⟩
      · intro x _
        rfl
      · intro x _ hxt
        rw [htU] at hxt
        exact absurd (Finset.mem_univ x) hxt

theorem twoConsts_not_ndimLE_zero :
    ¬ NDimLE ({fun _ : Fin 1 => (0 : Fin 2), fun _ : Fin 1 => (1 : Fin 2)} :
      Finset ((Fin 1) → Fin 2)) 0 := by
  intro hle
  have hcard : (Finset.univ : Finset (Fin 1)).card = 0 + 1 := by decide
  exact hle Finset.univ hcard twoConsts_shatter_univ

#print axioms Cslib.MachineLearning.PACLearning.nShatters_subset
#print axioms Cslib.MachineLearning.PACLearning.natarajan_lemma
#print axioms Cslib.MachineLearning.PACLearning.nDimLE_zero

end CSLibExtTest.MachineLearning.PACLearning
