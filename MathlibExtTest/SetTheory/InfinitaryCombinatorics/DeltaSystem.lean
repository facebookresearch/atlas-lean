/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import MathlibExt.SetTheory.InfinitaryCombinatorics.DeltaSystem
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace MathlibExtTest.SetTheory.InfinitaryCombinatorics.DeltaSystem

open MetaMathlibExt

-- Logic 11: A Delta system

/-- Validity: the root is contained in every member, provided the family has a second member
to intersect against. -/

theorem IsDeltaSystem.root_subset {α : Type*} {A : Set (Set α)} {r s t : Set α}
    (h : IsDeltaSystem A r) (hs : s ∈ A) (ht : t ∈ A) (hst : s ≠ t) : r ⊆ s := by
  rw [← h hs ht hst]
  exact Set.inter_subset_left

/-- Validity: two distinct members pin the root down uniquely, so `r` is not a free parameter
once `A` has at least two elements. -/

theorem IsDeltaSystem.root_unique {α : Type*} {A : Set (Set α)} {r r' s t : Set α}
    (h : IsDeltaSystem A r) (h' : IsDeltaSystem A r') (hs : s ∈ A) (ht : t ∈ A) (hst : s ≠ t) :
    r = r' :=
  (h hs ht hst).symm.trans (h' hs ht hst)

/-- The petals of the standard sunflower: `{0, n+1}`, all sharing exactly `{0}`. -/

def petal (n : ℕ) : Set ℕ := {0, n + 1}

/-- Three sets that pairwise intersect but admit no common root. -/

def triangle : Set (Set ℕ) := {{0, 1}, {1, 2}, {0, 2}}

/-- Sanity check for `IsDeltaSystem`, bracketing the definition from both sides.

1. **Nonvacuous.** `{{0, n+1} | n : ℕ}` is an *infinite* Δ-system with a *nonempty* root `{0}`.
   So the definition is satisfiable by something interesting — not just by degenerate families,
   and not only with the empty root (a pairwise disjoint family).
2. **Not trivially true.** The triangle `{{0,1}, {1,2}, {0,2}}` is a Δ-system for *no* root at
   all, so `IsDeltaSystem` genuinely constrains `A`.
3. **The degenerate case is real.** A one-element family is a Δ-system for *every* `r`, since
   `Set.Pairwise` is vacuous there.  This is why `root_unique` above has to assume two distinct
   members: without that hypothesis the root is not determined, and any theorem producing a
   Δ-system should ask for `2 ≤ A.encard` (or `3 ≤`) to say anything. -/

theorem isDeltaSystem_sanity :
    IsDeltaSystem (Set.range petal) {0} ∧
      (Set.range petal).Infinite ∧
      (∀ r : Set ℕ, ¬ IsDeltaSystem triangle r) ∧
      (∀ r : Set ℕ, IsDeltaSystem {({0} : Set ℕ)} r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Distinct petals meet exactly in `{0}`.
    rintro s ⟨n, rfl⟩ t ⟨m, rfl⟩ hne
    have hnm : n ≠ m := fun hh => hne (by rw [hh])
    ext x
    simp only [petal, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · -- There are infinitely many petals.
    refine Set.infinite_range_of_injective fun n m h => ?_
    have hn : (n + 1 : ℕ) ∈ petal m := by rw [← h]; simp [petal]
    simp only [petal, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    omega
  · -- Two of the three pairs force incompatible roots `{1}` and `{0}`.
    intro r hr
    have m1 : ({0, 1} : Set ℕ) ∈ triangle := by simp [triangle]
    have m2 : ({1, 2} : Set ℕ) ∈ triangle := by simp [triangle]
    have m3 : ({0, 2} : Set ℕ) ∈ triangle := by simp [triangle]
    have d12 : ({0, 1} : Set ℕ) ≠ {1, 2} := by
      intro hh; have h0 := Set.ext_iff.1 hh 0; simp at h0
    have d13 : ({0, 1} : Set ℕ) ≠ {0, 2} := by
      intro hh; have h1 := Set.ext_iff.1 hh 1; simp at h1
    have c1 : ({0, 1} : Set ℕ) ∩ {1, 2} = {1} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    have c2 : ({0, 1} : Set ℕ) ∩ {0, 2} = {0} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    have e1 : ({1} : Set ℕ) = r := by rw [← c1]; exact hr m1 m2 d12
    have e2 : ({0} : Set ℕ) = r := by rw [← c2]; exact hr m1 m3 d13
    have : (1 : ℕ) ∈ ({0} : Set ℕ) := by rw [e2, ← e1]; rfl
    simp at this
  · -- A single-element family is vacuously a Δ-system, whatever `r` is.
    intro r
    exact Set.pairwise_singleton _ _

end MathlibExtTest.SetTheory.InfinitaryCombinatorics.DeltaSystem

end
