/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset

@[expose] public section

/-! # Weighted interval scheduling: exchange identity

Adjoining an interval `i ∉ S`, the optimum weight of a pairwise
compatible family either skips `i` or takes `i` plus the optimum
over the intervals of `S` compatible with `i`. (Without
`i ∉ S` the identity double-counts `i`; that case was refuted
during this work.) This is roadmap package ALG-22a of the Atlas
TCS canon roadmap.

Source: Kleinberg and Tardos, Algorithm Design (2006),
Section 6.1.
-/

open Finset

/-- Weighted interval scheduling. An interval is a triple
`(start, finish, weight)` of natural numbers. A family (finset)
of intervals is compatible if every two distinct intervals are
non-overlapping in one order or the other. -/
noncomputable def wisOpt (S : Finset (ℕ × ℕ × ℕ)) : ℕ :=
  (S.powerset.filter (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b →
    a.2.1 ≤ b.1 ∨ b.2.1 ≤ a.1)).sup (fun F => ∑ a ∈ F, a.2.2)

private theorem compat_empty :
    ∀ a ∈ (∅ : Finset (ℕ × ℕ × ℕ)), ∀ b ∈ (∅ : Finset (ℕ × ℕ × ℕ)), a ≠ b →
      a.2.1 ≤ b.1 ∨ b.2.1 ≤ a.1 := by
  intro a ha
  simp at ha

private theorem powerset_filter_nonempty (S : Finset (ℕ × ℕ × ℕ)) :
    (S.powerset.filter (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b →
      a.2.1 ≤ b.1 ∨ b.2.1 ≤ a.1)).Nonempty := by
  refine ⟨∅, ?_⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset S), compat_empty⟩

/-- The DP exchange identity: adjoining one interval `i`, the
optimum either skips `i`, or takes `i` plus the optimum over the
intervals in `S` compatible with `i`. -/
theorem wisOpt_insert (i : ℕ × ℕ × ℕ) (S : Finset (ℕ × ℕ × ℕ)) (hi : i ∉ S) :
    wisOpt (insert i S) = max (wisOpt S)
      (i.2.2 + wisOpt (S.filter (fun a => a.2.1 ≤ i.1 ∨ i.2.1 ≤ a.1))) := by
  unfold wisOpt
  apply le_antisymm
  · apply Finset.sup_le
    intro F hF
    simp only [Finset.mem_filter, Finset.mem_powerset] at hF
    obtain ⟨hsub, hcompat⟩ := hF
    by_cases hiF : i ∈ F
    · have hGsub : F.erase i ⊆ S.filter (fun a => a.2.1 ≤ i.1 ∨ i.2.1 ≤ a.1) := by
        intro x hx
        have hxF : x ∈ F := Finset.mem_of_mem_erase hx
        have hne : x ≠ i := Finset.ne_of_mem_erase hx
        have hxmem : x ∈ insert i S := hsub hxF
        simp only [Finset.mem_insert] at hxmem
        have hxS : x ∈ S := by
          cases hxmem with
          | inl h => exact absurd h hne
          | inr h => exact h
        refine Finset.mem_filter.mpr ⟨hxS, ?_⟩
        exact hcompat x hxF i hiF hne
      have hGmem : F.erase i ∈ (S.filter (fun a => a.2.1 ≤ i.1 ∨ i.2.1 ≤ a.1)).powerset.filter
          (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → a.2.1 ≤ b.1 ∨ b.2.1 ≤ a.1) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hGsub, ?_⟩
        intro a ha b hb hab
        exact hcompat a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
      calc (∑ a ∈ F, a.2.2) = i.2.2 + ∑ a ∈ F.erase i, a.2.2 :=
            (Finset.add_sum_erase F (fun a => a.2.2) hiF).symm
        _ ≤ i.2.2 + ((S.filter (fun a => a.2.1 ≤ i.1 ∨ i.2.1 ≤ a.1)).powerset.filter
            (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → a.2.1 ≤ b.1 ∨ b.2.1 ≤ a.1)).sup
            (fun F => ∑ a ∈ F, a.2.2) :=
            Nat.add_le_add_left (Finset.le_sup (f := fun F => ∑ a ∈ F, a.2.2) hGmem) _
        _ ≤ max _ _ := le_max_right _ _
    · have hFsub : F ⊆ S := by
        intro x hx
        have hxmem : x ∈ insert i S := hsub hx
        simp only [Finset.mem_insert] at hxmem
        cases hxmem with
        | inl h => subst h; exact absurd hx hiF
        | inr h => exact h
      have hFmem : F ∈ S.powerset.filter
          (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → a.2.1 ≤ b.1 ∨ b.2.1 ≤ a.1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hFsub, hcompat⟩
      exact le_trans (Finset.le_sup (f := fun F => ∑ a ∈ F, a.2.2) hFmem) (le_max_left _ _)
  · apply max_le
    · apply Finset.sup_le
      intro F hF
      simp only [Finset.mem_filter, Finset.mem_powerset] at hF
      obtain ⟨hsub, hcompat⟩ := hF
      have hmem : F ∈ (insert i S).powerset.filter
          (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → a.2.1 ≤ b.1 ∨ b.2.1 ≤ a.1) :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (hsub.trans (Finset.subset_insert i S)), hcompat⟩
      exact Finset.le_sup (f := fun F => ∑ a ∈ F, a.2.2) hmem
    · obtain ⟨F, hFmem, hFeq⟩ := Finset.exists_mem_eq_sup _
        (powerset_filter_nonempty (S.filter (fun a => a.2.1 ≤ i.1 ∨ i.2.1 ≤ a.1)))
        (fun F => ∑ a ∈ F, a.2.2)
      simp only [Finset.mem_filter, Finset.mem_powerset] at hFmem
      obtain ⟨hFsub, hFcompat⟩ := hFmem
      have hFS : F ⊆ S := hFsub.trans (Finset.filter_subset _ S)
      have hiF : i ∉ F := fun h => hi (hFS h)
      have hmem : insert i F ∈ (insert i S).powerset.filter
          (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → a.2.1 ≤ b.1 ∨ b.2.1 ≤ a.1) := by
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.insert_subset_insert i hFS), ?_⟩
        intro a ha b hb hab
        simp only [Finset.mem_insert] at ha hb
        obtain haeq | ha' := ha <;> obtain hbeq | hb' := hb
        · exact absurd (haeq.trans hbeq.symm) hab
        · rw [haeq]
          have hbF : b ∈ S.filter (fun a => a.2.1 ≤ i.1 ∨ i.2.1 ≤ a.1) := hFsub hb'
          simp only [Finset.mem_filter] at hbF
          obtain ⟨-, h⟩ := hbF
          cases h with
          | inl h => exact Or.inr h
          | inr h => exact Or.inl h
        · rw [hbeq]
          have haF : a ∈ S.filter (fun a => a.2.1 ≤ i.1 ∨ i.2.1 ≤ a.1) := hFsub ha'
          simp only [Finset.mem_filter] at haF
          obtain ⟨-, h⟩ := haF
          exact h
        · exact hFcompat a ha' b hb' hab
      calc i.2.2 + ((S.filter (fun a => a.2.1 ≤ i.1 ∨ i.2.1 ≤ a.1)).powerset.filter
            (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → a.2.1 ≤ b.1 ∨ b.2.1 ≤ a.1)).sup
            (fun F => ∑ a ∈ F, a.2.2)
          = i.2.2 + ∑ a ∈ F, a.2.2 := by simp only [hFeq]
        _ = ∑ a ∈ insert i F, a.2.2 := (Finset.sum_insert (f := fun a => a.2.2) hiF).symm
        _ ≤ ((insert i S).powerset.filter
            (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → a.2.1 ≤ b.1 ∨ b.2.1 ≤ a.1)).sup
            (fun F => ∑ a ∈ F, a.2.2) :=
            Finset.le_sup (f := fun F => ∑ a ∈ F, a.2.2) hmem
