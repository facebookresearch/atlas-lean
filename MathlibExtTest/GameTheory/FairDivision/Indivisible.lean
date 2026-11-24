/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.FairDivision.Indivisible
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Basic

/-!
# Tests for EF1 fair division: separating examples and smoke tests.

`T1` recomputes bundle values for the two `C6` examples and checks the
empty-goods boundary. `T2` proves the EF1/EFX/EF verdicts and exhibits a
direct EF1 allocation. `T3` smoke-tests source existence and a 3-cycle.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExtTest.GameTheory.FairDivision.Indivisible

open MathlibExt.GameTheory.FairDivision.Indivisible

/-- `T1`: example (a) bundles. -/
theorem exA_bundle_0 : bundle exA_alloc 0 = {2, 3} := by decide

/-- `T1`: example (a) bundles. -/
theorem exA_bundle_1 : bundle exA_alloc 1 = {0, 1} := by decide

/-- `T1`: agent 0 values its own bundle `{2, 3}` at 2. -/
theorem exA_value_0_own :
    bundleValue exA_val 0 (bundle exA_alloc 0) = 2 := by
  rw [exA_bundle_0]
  show ∑ g ∈ ({2, 3} : Finset (Fin 4)), exA_val 0 g = 2
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [exA_val]

/-- `T1`: agent 0 values the other bundle `{0, 1}` at 2. -/
theorem exA_value_0_other :
    bundleValue exA_val 0 (bundle exA_alloc 1) = 2 := by
  rw [exA_bundle_1]
  show ∑ g ∈ ({0, 1} : Finset (Fin 4)), exA_val 0 g = 2
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [exA_val]

/-- `T1`: agent 1 values the other bundle `{2, 3}` at 4. -/
theorem exA_value_1_other :
    bundleValue exA_val 1 (bundle exA_alloc 0) = 4 := by
  rw [exA_bundle_0]
  show ∑ g ∈ ({2, 3} : Finset (Fin 4)), exA_val 1 g = 4
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [exA_val]

/-- `T1`: agent 1 values its own bundle `{0, 1}` at 2. -/
theorem exA_value_1_own :
    bundleValue exA_val 1 (bundle exA_alloc 1) = 2 := by
  rw [exA_bundle_1]
  show ∑ g ∈ ({0, 1} : Finset (Fin 4)), exA_val 1 g = 2
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [exA_val]

/-- `T1`: example (b) bundles. -/
theorem exB_bundle_0 : bundle exB_alloc 0 = {0} := by decide

/-- `T1`: example (b) bundles. -/
theorem exB_bundle_1 : bundle exB_alloc 1 = {1} := by decide

/-- `T1`: agent 0 values its own bundle `{0}` at 3. -/
theorem exB_value_0_own :
    bundleValue exB_val 0 (bundle exB_alloc 0) = 3 := by
  rw [exB_bundle_0, bundleValue_singleton]
  norm_num [exB_val]

/-- `T1`: agent 0 values the other bundle `{1}` at 2. -/
theorem exB_value_0_other :
    bundleValue exB_val 0 (bundle exB_alloc 1) = 2 := by
  rw [exB_bundle_1, bundleValue_singleton]
  norm_num [exB_val]

/-- `T1`: agent 1 values the other bundle `{0}` at 3. -/
theorem exB_value_1_other :
    bundleValue exB_val 1 (bundle exB_alloc 0) = 3 := by
  rw [exB_bundle_0, bundleValue_singleton]
  norm_num [exB_val]

/-- `T1`: agent 1 values its own bundle `{1}` at 2. -/
theorem exB_value_1_own :
    bundleValue exB_val 1 (bundle exB_alloc 1) = 2 := by
  rw [exB_bundle_1, bundleValue_singleton]
  norm_num [exB_val]

/-- `T1`: the unique allocation with no goods. -/
def emptyAlloc : Fin 0 → Fin 1 := fun g => Fin.elim0 g

/-- `T1`: trivial valuations with no goods. -/
def emptyVal : Fin 1 → Fin 0 → ℝ := fun _ _ => 0

/-- `T1`: all bundles are empty with no goods. -/
theorem empty_bundle (i : Fin 1) : bundle emptyAlloc i = ∅ := by
  ext g
  exact False.elim (Fin.elim0 g)

/-- `T1`: the empty allocation is envy-free. -/
theorem empty_isEF : IsEF emptyVal emptyAlloc := by
  intro i j
  unfold value
  have hj : bundle emptyAlloc j = ∅ := empty_bundle j
  have hi : bundle emptyAlloc i = ∅ := empty_bundle i
  rw [hj, hi, bundleValue_empty]

/-- `T1`: the empty allocation is EFX. -/
theorem empty_isEFX : IsEFX emptyVal emptyAlloc := by
  intro i j g hg
  rw [empty_bundle] at hg
  exact (Finset.notMem_empty g hg).elim

/-- `T1`: the empty allocation is EF1. -/
theorem empty_isEF1 : IsEF1 emptyVal emptyAlloc := by
  intro i j h
  rw [empty_bundle] at h
  obtain ⟨g, hg⟩ := h
  exact (Finset.notMem_empty g hg).elim

theorem exA_erased_0_2 :
    bundleValue exA_val 0 ((({2, 3} : Finset (Fin 4))).erase 2) = 1 := by
  rw [show (({2, 3} : Finset (Fin 4)).erase 2) = {3} from by decide,
    bundleValue_singleton]
  norm_num [exA_val]

theorem exA_erased_0_0 :
    bundleValue exA_val 0 ((({0, 1} : Finset (Fin 4))).erase 0) = 1 := by
  rw [show (({0, 1} : Finset (Fin 4)).erase 0) = {1} from by decide,
    bundleValue_singleton]
  norm_num [exA_val]

theorem exA_erased_1_3 :
    bundleValue exA_val 1 ((({2, 3} : Finset (Fin 4))).erase 3) = 1 := by
  rw [show (({2, 3} : Finset (Fin 4)).erase 3) = {2} from by decide,
    bundleValue_singleton]
  norm_num [exA_val]

theorem exA_erased_1_0 :
    bundleValue exA_val 1 ((({0, 1} : Finset (Fin 4))).erase 0) = 1 := by
  rw [show (({0, 1} : Finset (Fin 4)).erase 0) = {1} from by decide,
    bundleValue_singleton]
  norm_num [exA_val]

theorem exA_isEF1 : IsEF1 exA_val exA_alloc := by
  intro i j _
  fin_cases i <;> fin_cases j
  · simp only [Fin.mk_zero]
    exact ⟨2, by rw [exA_bundle_0]; decide, by
      rw [exA_bundle_0, exA_erased_0_2]
      show (1 : ℝ) ≤ value exA_val exA_alloc 0
      show (1 : ℝ) ≤ bundleValue exA_val 0 (bundle exA_alloc 0)
      rw [exA_value_0_own]
      norm_num⟩
  · simp only [Fin.mk_zero, Fin.mk_one]
    exact ⟨0, by rw [exA_bundle_1]; decide, by
      rw [exA_bundle_1, exA_erased_0_0]
      show (1 : ℝ) ≤ value exA_val exA_alloc 0
      show (1 : ℝ) ≤ bundleValue exA_val 0 (bundle exA_alloc 0)
      rw [exA_value_0_own]
      norm_num⟩
  · simp only [Fin.mk_zero, Fin.mk_one]
    exact ⟨3, by rw [exA_bundle_0]; decide, by
      rw [exA_bundle_0, exA_erased_1_3]
      show (1 : ℝ) ≤ value exA_val exA_alloc 1
      show (1 : ℝ) ≤ bundleValue exA_val 1 (bundle exA_alloc 1)
      rw [exA_value_1_own]
      norm_num⟩
  · simp only [Fin.mk_one]
    exact ⟨0, by rw [exA_bundle_1]; decide, by
      rw [exA_bundle_1, exA_erased_1_0]
      show (1 : ℝ) ≤ value exA_val exA_alloc 1
      show (1 : ℝ) ≤ bundleValue exA_val 1 (bundle exA_alloc 1)
      rw [exA_value_1_own]
      norm_num⟩

theorem exA_not_isEFX : ¬ IsEFX exA_val exA_alloc := by
  intro h
  have h2 := h 1 0 2 (by rw [exA_bundle_0]; decide)
  rw [exA_bundle_0] at h2
  rw [show (({2, 3} : Finset (Fin 4)).erase 2) = {3} from by decide,
    bundleValue_singleton] at h2
  change (3 : ℝ) ≤ value exA_val exA_alloc 1 at h2
  change (3 : ℝ) ≤ bundleValue exA_val 1 (bundle exA_alloc 1) at h2
  rw [exA_value_1_own] at h2
  exact absurd h2 (by simp [show (3 : ℝ) = 2 + 1 from by norm_num])

theorem exB_isEFX : IsEFX exB_val exB_alloc := by
  intro i j g hg
  fin_cases i <;> fin_cases j
  · simp only [Fin.mk_zero] at hg ⊢
    rw [exB_bundle_0] at hg ⊢
    obtain rfl : g = 0 := Finset.mem_singleton.mp hg
    rw [show (({0} : Finset (Fin 2)).erase 0) = ∅ from by decide,
      bundleValue_empty]
    show (0 : ℝ) ≤ value exB_val exB_alloc 0
    show (0 : ℝ) ≤ bundleValue exB_val 0 (bundle exB_alloc 0)
    rw [exB_value_0_own]
    norm_num
  · simp only [Fin.mk_zero, Fin.mk_one] at hg ⊢
    rw [exB_bundle_1] at hg ⊢
    obtain rfl : g = 1 := Finset.mem_singleton.mp hg
    rw [show (({1} : Finset (Fin 2)).erase 1) = ∅ from by decide,
      bundleValue_empty]
    show (0 : ℝ) ≤ value exB_val exB_alloc 0
    show (0 : ℝ) ≤ bundleValue exB_val 0 (bundle exB_alloc 0)
    rw [exB_value_0_own]
    norm_num
  · simp only [Fin.mk_zero, Fin.mk_one] at hg ⊢
    rw [exB_bundle_0] at hg ⊢
    obtain rfl : g = 0 := Finset.mem_singleton.mp hg
    rw [show (({0} : Finset (Fin 2)).erase 0) = ∅ from by decide,
      bundleValue_empty]
    show (0 : ℝ) ≤ value exB_val exB_alloc 1
    show (0 : ℝ) ≤ bundleValue exB_val 1 (bundle exB_alloc 1)
    rw [exB_value_1_own]
    norm_num
  · simp only [Fin.mk_one] at hg ⊢
    rw [exB_bundle_1] at hg ⊢
    obtain rfl : g = 1 := Finset.mem_singleton.mp hg
    rw [show (({1} : Finset (Fin 2)).erase 1) = ∅ from by decide,
      bundleValue_empty]
    show (0 : ℝ) ≤ value exB_val exB_alloc 1
    show (0 : ℝ) ≤ bundleValue exB_val 1 (bundle exB_alloc 1)
    rw [exB_value_1_own]
    norm_num

theorem exB_not_isEF : ¬ IsEF exB_val exB_alloc := by
  intro h
  have h10 := h 1 0
  rw [exB_value_1_other] at h10
  change (3 : ℝ) ≤ value exB_val exB_alloc 1 at h10
  change (3 : ℝ) ≤ bundleValue exB_val 1 (bundle exB_alloc 1) at h10
  rw [exB_value_1_own] at h10
  exact absurd h10 (by simp [show (3 : ℝ) = 2 + 1 from by norm_num])

def exA_witness : Fin 4 → Fin 2 := exA_alloc

theorem exA_witness_isEF1 : IsEF1 exA_val exA_witness := exA_isEF1

def noenvy_val : Fin 2 → Fin 2 → ℝ :=
  fun i g => if i.val = g.val then 1 else 0

def noenvy_alloc : Fin 2 → Fin 2 := fun g => g

theorem noenvy_bundle_0 : bundle noenvy_alloc 0 = {0} := by decide

theorem noenvy_bundle_1 : bundle noenvy_alloc 1 = {1} := by decide

theorem noenvy_all_source : ∀ i, IsSource noenvy_val noenvy_alloc i := by
  intro i j hj
  fin_cases i <;> fin_cases j
  · simp only [Fin.mk_zero] at hj
    simp only [Envy, value] at hj
    rw [noenvy_bundle_0, bundleValue_singleton] at hj
    norm_num [noenvy_val] at hj
  · simp only [Fin.mk_zero, Fin.mk_one] at hj
    simp only [Envy, value] at hj
    rw [noenvy_bundle_0, noenvy_bundle_1, bundleValue_singleton,
      bundleValue_singleton] at hj
    norm_num [noenvy_val] at hj
    exact absurd hj (by norm_num)
  · simp only [Fin.mk_zero, Fin.mk_one] at hj
    simp only [Envy, value] at hj
    rw [noenvy_bundle_1, noenvy_bundle_0, bundleValue_singleton,
      bundleValue_singleton] at hj
    norm_num [noenvy_val] at hj
    exact absurd hj (by norm_num)
  · simp only [Fin.mk_one] at hj
    simp only [Envy, value] at hj
    rw [noenvy_bundle_1, bundleValue_singleton] at hj
    norm_num [noenvy_val] at hj

def cyc_val : Fin 3 → Fin 3 → ℝ :=
  fun i g =>
    if g.val = (i.val + 1) % 3 then 10 else if g.val = i.val then 1 else 0

def cyc_alloc : Fin 3 → Fin 3 := fun g => g

theorem cyc_bundle (k : Fin 3) : bundle cyc_alloc k = {k} := by
  fin_cases k <;> decide

theorem cyc_envy_01 : Envy cyc_val cyc_alloc 0 1 := by
  simp only [Envy, value, cyc_bundle, bundleValue_singleton]
  norm_num [cyc_val]

theorem cyc_envy_12 : Envy cyc_val cyc_alloc 1 2 := by
  simp only [Envy, value, cyc_bundle, bundleValue_singleton]
  norm_num [cyc_val]

theorem cyc_envy_20 : Envy cyc_val cyc_alloc 2 0 := by
  simp only [Envy, value, cyc_bundle, bundleValue_singleton]
  norm_num [cyc_val]

def cyc_idx : ZMod 3 → Fin 3 :=
  fun t => if t = 0 then 0 else if t = 1 then 1 else 2

theorem cyc_idx_inj : Function.Injective cyc_idx := by decide

theorem cyc_isEnvyCycle : IsEnvyCycle cyc_val cyc_alloc 3 cyc_idx := by
  refine ⟨by decide, cyc_idx_inj, fun t => ?_⟩
  have hall : ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  have ht : t = 0 ∨ t = 1 ∨ t = 2 := hall t
  rcases ht with rfl | rfl | rfl
  · rw [show ((0 : ZMod 3) + 1) = 1 from by decide]
    show Envy cyc_val cyc_alloc 0 1
    exact cyc_envy_01
  · rw [show ((1 : ZMod 3) + 1) = 2 from by decide]
    show Envy cyc_val cyc_alloc 1 2
    exact cyc_envy_12
  · rw [show ((2 : ZMod 3) + 1) = 0 from by decide]
    show Envy cyc_val cyc_alloc 2 0
    exact cyc_envy_20

end MathlibExtTest.GameTheory.FairDivision.Indivisible

end
