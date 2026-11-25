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
shattering, singleton binary dimension bounds, the finite-class bridge, an
infinite-domain universe class, and `#print axioms` probes.
-/

namespace CSLibExtTest.MachineLearning.PACLearning

open Cslib.MachineLearning.PACLearning

theorem constClass_ndimLE_zero :
    NDimLE (↑({fun _ => (0 : Fin 3)} : Finset ((Fin 2) → Fin 3)) :
      ConceptClass (Fin 2) (Fin 3)) 0 := by
  intro s hs hsh
  obtain ⟨f₀, f₁, hne, hwit⟩ := hsh
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hs
  have hy : y ∈ ({y} : Finset (Fin 2)) := Finset.mem_singleton_self y
  obtain ⟨h, mh, h1, -⟩ := hwit {y} (Finset.Subset.refl _)
  obtain ⟨h', mh', -, h0⟩ := hwit ∅ (Finset.empty_subset _)
  have hh : h = fun _ => (0 : Fin 3) :=
    Finset.mem_singleton.mp (Finset.mem_coe.mp mh)
  have hh' : h' = fun _ => (0 : Fin 3) :=
    Finset.mem_singleton.mp (Finset.mem_coe.mp mh')
  have e1 : h y = f₁ y := h1 y (Finset.mem_singleton_self y)
  have e0 : h' y = f₀ y := h0 y hy (Finset.notMem_empty y)
  have hcontra : f₁ y = f₀ y := by rw [← e1, ← e0, hh, hh']
  exact hne y hy hcontra.symm

theorem constClass_tracesCard_one :
    tracesCard (↑({fun _ => (0 : Fin 3)} : Finset ((Fin 2) → Fin 3)) :
      ConceptClass (Fin 2) (Fin 3)) Finset.univ = 1 := by
  rw [tracesCard_coe_finset]
  decide

theorem allFuncs_shatter :
    NShatters (↑(Finset.univ : Finset ((Fin 2) → Fin 2)) :
      ConceptClass (Fin 2) (Fin 2)) Finset.univ := by
  refine ⟨fun _ => (0 : Fin 2), fun _ => (1 : Fin 2), ?_, ?_⟩
  · decide
  · intro t ht
    refine ⟨fun x => if x ∈ t then (1 : Fin 2) else 0, Finset.mem_univ _, ?_, ?_⟩
    · intro x hxt
      simp [hxt]
    · intro x _ hxt
      simp [hxt]

theorem allFuncs_not_ndimLE_one :
    ¬ NDimLE (↑(Finset.univ : Finset ((Fin 2) → Fin 2)) :
      ConceptClass (Fin 2) (Fin 2)) 1 := by
  intro hle
  have hcard : (Finset.univ : Finset (Fin 2)).card = 1 + 1 := by decide
  exact hle Finset.univ hcard allFuncs_shatter

theorem allFuncs_tracesCard_four :
    tracesCard (↑(Finset.univ : Finset ((Fin 2) → Fin 2)) :
      ConceptClass (Fin 2) (Fin 2)) Finset.univ = 4 := by
  rw [tracesCard_coe_finset]
  decide

-- Genuine infinite-class check: the universe class over `ℕ` is presented as
-- a `Set`, not a coerced `Finset`.
theorem univClass_shatter_pair :
    NShatters (Set.univ : ConceptClass ℕ (Fin 2)) {0, 1} := by
  refine ⟨fun _ => (0 : Fin 2), fun _ => (1 : Fin 2), ?_, ?_⟩
  · decide
  · intro t ht
    refine ⟨fun x => if x ∈ t then (1 : Fin 2) else 0, Set.mem_univ _, ?_, ?_⟩
    · intro x hxt
      simp [hxt]
    · intro x _ hxt
      simp [hxt]

theorem twoConsts_ndimLE_one :
    NDimLE (↑({fun _ : Fin 1 => (0 : Fin 2), fun _ : Fin 1 => (1 : Fin 2)} :
      Finset ((Fin 1) → Fin 2)) : ConceptClass (Fin 1) (Fin 2)) 1 := by
  intro s hs _
  have hle : s.card ≤ 1 := by
    have h := Finset.card_le_univ s
    rw [Fintype.card_fin] at h
    exact h
  omega

theorem twoConsts_shatter_univ :
    NShatters (↑({fun _ : Fin 1 => (0 : Fin 2), fun _ : Fin 1 => (1 : Fin 2)} :
      Finset ((Fin 1) → Fin 2)) : ConceptClass (Fin 1) (Fin 2))
      Finset.univ := by
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
    ¬ NDimLE (↑({fun _ : Fin 1 => (0 : Fin 2), fun _ : Fin 1 => (1 : Fin 2)} :
      Finset ((Fin 1) → Fin 2)) : ConceptClass (Fin 1) (Fin 2)) 0 := by
  intro hle
  have hcard : (Finset.univ : Finset (Fin 1)).card = 0 + 1 := by decide
  exact hle Finset.univ hcard twoConsts_shatter_univ

-- Direct lemma use at bound 0; with the exact count, the bound 1 is tight.
theorem constClass_lemma_bound_one :
    tracesCard (↑({fun _ => (0 : Fin 3)} : Finset ((Fin 2) → Fin 3)) :
      ConceptClass (Fin 2) (Fin 3)) Finset.univ ≤ 1 := by
  have hs : (Finset.univ : Finset (Fin 2)).Nonempty := Finset.univ_nonempty
  have h := natarajan_lemma _ 0 constClass_ndimLE_zero Finset.univ hs
  simpa using h

-- Direct lemma use at bound 1; the numeric bound is 1 ^ 1 * 2 ^ (2 * 1).
theorem twoConsts_lemma_bound_four :
    tracesCard (↑({fun _ : Fin 1 => (0 : Fin 2), fun _ : Fin 1 => (1 : Fin 2)} :
      Finset ((Fin 1) → Fin 2)) : ConceptClass (Fin 1) (Fin 2))
      Finset.univ ≤ 4 := by
  have hs : (Finset.univ : Finset (Fin 1)).Nonempty := Finset.univ_nonempty
  have h := natarajan_lemma _ 1 twoConsts_ndimLE_one Finset.univ hs
  have hcard : (Finset.univ : Finset (Fin 1)).card = 1 := by decide
  have hnum : (1 : ℕ) ^ 1 * 2 ^ (2 * 1) = 4 := by decide
  rw [hcard, Fintype.card_fin, hnum] at h
  exact h

theorem twoConsts_tracesCard_two :
    tracesCard (↑({fun _ : Fin 1 => (0 : Fin 2), fun _ : Fin 1 => (1 : Fin 2)} :
      Finset ((Fin 1) → Fin 2)) : ConceptClass (Fin 1) (Fin 2))
      Finset.univ = 2 := by
  rw [tracesCard_coe_finset]
  decide

-- Direct test of the Finset bridge: the set-based count on a coerced class
-- equals the image-of-finite-class count.
theorem twoConsts_bridge_traces :
    tracesCard (↑({fun _ : Fin 1 => (0 : Fin 2), fun _ : Fin 1 => (1 : Fin 2)} :
      Finset ((Fin 1) → Fin 2)) : ConceptClass (Fin 1) (Fin 2))
      Finset.univ =
      (({fun _ : Fin 1 => (0 : Fin 2), fun _ : Fin 1 => (1 : Fin 2)} :
        Finset ((Fin 1) → Fin 2)).image
        fun h (x : ↥(Finset.univ : Finset (Fin 1))) => h x.val).card :=
  tracesCard_coe_finset _ _

-- The finite-class corollary applies directly to a `Finset`.
theorem twoConsts_finset_corollary :
    ((({fun _ : Fin 1 => (0 : Fin 2), fun _ : Fin 1 => (1 : Fin 2)} :
        Finset ((Fin 1) → Fin 2)).image
        fun h (x : ↥(Finset.univ : Finset (Fin 1))) => h x.val).card) ≤
      (Finset.univ : Finset (Fin 1)).card ^ 1 * 2 ^ (2 * 1) := by
  have hs : (Finset.univ : Finset (Fin 1)).Nonempty := Finset.univ_nonempty
  exact natarajan_lemma_finset _ 1 twoConsts_ndimLE_one _ hs

-- Empty-sample boundary for a nonempty singleton class. The lemma needs
-- `s.Nonempty`, so it is not applied here; the value follows from the
-- bridge and `decide`.
theorem constClass_tracesCard_empty :
    tracesCard (↑({fun _ => (0 : Fin 3)} : Finset ((Fin 2) → Fin 3)) :
      ConceptClass (Fin 2) (Fin 3)) ∅ = 1 := by
  rw [tracesCard_coe_finset]
  decide

theorem empty_sample_not_nonempty :
    ¬ (∅ : Finset (Fin 2)).Nonempty := Finset.not_nonempty_empty

-- Bool-label tests: genuine non-`Fin` use of the generalized API.
theorem boolConsts_ndimLE_one :
    NDimLE (↑({fun _ : Fin 1 => false, fun _ : Fin 1 => true} :
      Finset ((Fin 1) → Bool)) : ConceptClass (Fin 1) Bool) 1 := by
  intro s hs _
  have hle : s.card ≤ 1 := by
    have h := Finset.card_le_univ s
    rw [Fintype.card_fin] at h
    exact h
  omega

theorem boolConsts_shatter_univ :
    NShatters (↑({fun _ : Fin 1 => false, fun _ : Fin 1 => true} :
      Finset ((Fin 1) → Bool)) : ConceptClass (Fin 1) Bool)
      Finset.univ := by
  refine ⟨fun _ => false, fun _ => true, ?_, ?_⟩
  · decide
  · intro t ht
    by_cases hempty : t = ∅
    · refine ⟨fun _ => false, Finset.mem_insert_self _ _, ?_, ?_⟩
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
      refine ⟨fun _ => true,
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_, ?_⟩
      · intro x _
        rfl
      · intro x _ hxt
        rw [htU] at hxt
        exact absurd (Finset.mem_univ x) hxt

theorem boolConsts_not_ndimLE_zero :
    ¬ NDimLE (↑({fun _ : Fin 1 => false, fun _ : Fin 1 => true} :
      Finset ((Fin 1) → Bool)) : ConceptClass (Fin 1) Bool) 0 := by
  intro hle
  have hcard : (Finset.univ : Finset (Fin 1)).card = 0 + 1 := by decide
  exact hle Finset.univ hcard boolConsts_shatter_univ

theorem boolConsts_tracesCard_two :
    tracesCard (↑({fun _ : Fin 1 => false, fun _ : Fin 1 => true} :
      Finset ((Fin 1) → Bool)) : ConceptClass (Fin 1) Bool)
      Finset.univ = 2 := by
  rw [tracesCard_coe_finset]
  decide

-- Direct lemma use at bound 1 with `Bool` labels; the numeric bound is
-- `1 ^ 1 * (Fintype.card Bool) ^ (2 * 1) = 4`.
theorem boolConsts_lemma_bound_four :
    tracesCard (↑({fun _ : Fin 1 => false, fun _ : Fin 1 => true} :
      Finset ((Fin 1) → Bool)) : ConceptClass (Fin 1) Bool)
      Finset.univ ≤ 4 := by
  have hs : (Finset.univ : Finset (Fin 1)).Nonempty := Finset.univ_nonempty
  have h := natarajan_lemma _ 1 boolConsts_ndimLE_one Finset.univ hs
  have hcard : (Finset.univ : Finset (Fin 1)).card = 1 := by decide
  have hnum : (1 : ℕ) ^ 1 * 2 ^ (2 * 1) = 4 := by decide
  rw [hcard, Fintype.card_bool, hnum] at h
  exact h

#print axioms Cslib.MachineLearning.PACLearning.nShatters_subset
#print axioms Cslib.MachineLearning.PACLearning.natarajan_lemma
#print axioms Cslib.MachineLearning.PACLearning.nDimLE_zero

end CSLibExtTest.MachineLearning.PACLearning
