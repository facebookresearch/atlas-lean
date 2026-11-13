/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.IntervalScheduling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset

@[expose] public section

/-! # Weighted interval scheduling: exchange identity

Activities indexed by `ι` occupy closed-open intervals `[start a, finish a)` and carry natural
weights. Compatibility is `Cslib.Algorithms.Lean.TimeM.IntervalCompatible`, the relation of the
unweighted interval-scheduling API, so touching endpoints are compatible. `wisOpt` is the largest
total weight of a pairwise compatible subfamily of a finite family `S`.

Adjoining an interval `i ∉ S`, the optimum either skips `i` or takes `i` plus the optimum over
the intervals of `S` compatible with `i`. (Without `i ∉ S` the identity double-counts `i`; that
case was refuted during this work.) This is roadmap package ALG-22a of the Atlas TCS canon
roadmap.

Source: Kleinberg and Tardos, Algorithm Design (2006), Section 6.1.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-- Interval compatibility is decidable for linearly ordered endpoints. -/
instance instDecidableRelIntervalCompatible {ι : Type*} {τ : Type*} [LinearOrder τ]
    (start finish : ι → τ) : DecidableRel (IntervalCompatible start finish) :=
  fun a b => inferInstanceAs (Decidable (finish a ≤ start b ∨ finish b ≤ start a))

end Cslib.Algorithms.Lean.TimeM

namespace Cslib.Algorithms.Lean.WeightedIntervalScheduling

open Finset
open Cslib.Algorithms.Lean.TimeM (IntervalCompatible)

variable {ι : Type*} {τ : Type*} [LinearOrder τ] [DecidableEq ι]

/-- Weighted interval scheduling: the largest total `weight` of a subfamily of `S` whose distinct
members are pairwise `IntervalCompatible start finish`. -/
def wisOpt (start finish : ι → τ) (weight : ι → ℕ) (S : Finset ι) : ℕ :=
  (S.powerset.filter (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b →
    IntervalCompatible start finish a b)).sup (fun F => ∑ a ∈ F, weight a)

private theorem powerset_filter_nonempty (start finish : ι → τ) (S : Finset ι) :
    (S.powerset.filter (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b →
      IntervalCompatible start finish a b)).Nonempty := by
  refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset S), ?_⟩⟩
  intro a ha
  simp at ha

/-- The DP exchange identity: adjoining one interval `i`, the
optimum either skips `i`, or takes `i` plus the optimum over the
intervals in `S` compatible with `i`. -/
theorem wisOpt_insert (start finish : ι → τ) (weight : ι → ℕ) (i : ι) (S : Finset ι)
    (hi : i ∉ S) :
    wisOpt start finish weight (insert i S) = max (wisOpt start finish weight S)
      (weight i + wisOpt start finish weight (S.filter (IntervalCompatible start finish i))) := by
  unfold wisOpt
  apply le_antisymm
  · apply Finset.sup_le
    intro F hF
    simp only [Finset.mem_filter, Finset.mem_powerset] at hF
    obtain ⟨hsub, hcompat⟩ := hF
    by_cases hiF : i ∈ F
    · have hGsub : F.erase i ⊆ S.filter (IntervalCompatible start finish i) := by
        intro x hx
        have hxF : x ∈ F := Finset.mem_of_mem_erase hx
        have hne : x ≠ i := Finset.ne_of_mem_erase hx
        have hxmem : x ∈ insert i S := hsub hxF
        simp only [Finset.mem_insert] at hxmem
        have hxS : x ∈ S := by
          cases hxmem with
          | inl h => exact absurd h hne
          | inr h => exact h
        exact Finset.mem_filter.mpr ⟨hxS, (hcompat x hxF i hiF hne).symm⟩
      have hGmem : F.erase i ∈ (S.filter (IntervalCompatible start finish i)).powerset.filter
          (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → IntervalCompatible start finish a b) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hGsub, ?_⟩
        intro a ha b hb hab
        exact hcompat a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
      calc (∑ a ∈ F, weight a) = weight i + ∑ a ∈ F.erase i, weight a :=
            (Finset.add_sum_erase F weight hiF).symm
        _ ≤ weight i + ((S.filter (IntervalCompatible start finish i)).powerset.filter
            (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → IntervalCompatible start finish a b)).sup
            (fun F => ∑ a ∈ F, weight a) :=
            Nat.add_le_add_left (Finset.le_sup (f := fun F => ∑ a ∈ F, weight a) hGmem) _
        _ ≤ max _ _ := le_max_right _ _
    · have hFsub : F ⊆ S := by
        intro x hx
        have hxmem : x ∈ insert i S := hsub hx
        simp only [Finset.mem_insert] at hxmem
        cases hxmem with
        | inl h => subst h; exact absurd hx hiF
        | inr h => exact h
      have hFmem : F ∈ S.powerset.filter
          (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → IntervalCompatible start finish a b) :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hFsub, hcompat⟩
      exact le_trans (Finset.le_sup (f := fun F => ∑ a ∈ F, weight a) hFmem) (le_max_left _ _)
  · apply max_le
    · apply Finset.sup_le
      intro F hF
      simp only [Finset.mem_filter, Finset.mem_powerset] at hF
      obtain ⟨hsub, hcompat⟩ := hF
      have hmem : F ∈ (insert i S).powerset.filter
          (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → IntervalCompatible start finish a b) :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (hsub.trans (Finset.subset_insert i S)), hcompat⟩
      exact Finset.le_sup (f := fun F => ∑ a ∈ F, weight a) hmem
    · obtain ⟨F, hFmem, hFeq⟩ := Finset.exists_mem_eq_sup _
        (powerset_filter_nonempty start finish (S.filter (IntervalCompatible start finish i)))
        (fun F => ∑ a ∈ F, weight a)
      simp only [Finset.mem_filter, Finset.mem_powerset] at hFmem
      obtain ⟨hFsub, hFcompat⟩ := hFmem
      have hFS : F ⊆ S := hFsub.trans (Finset.filter_subset _ S)
      have hiF : i ∉ F := fun h => hi (hFS h)
      have hmem : insert i F ∈ (insert i S).powerset.filter
          (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → IntervalCompatible start finish a b) := by
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.insert_subset_insert i hFS), ?_⟩
        intro a ha b hb hab
        simp only [Finset.mem_insert] at ha hb
        obtain haeq | ha' := ha <;> obtain hbeq | hb' := hb
        · exact absurd (haeq.trans hbeq.symm) hab
        · rw [haeq]
          exact (Finset.mem_filter.mp (hFsub hb')).2
        · rw [hbeq]
          exact (Finset.mem_filter.mp (hFsub ha')).2.symm
        · exact hFcompat a ha' b hb' hab
      calc weight i + ((S.filter (IntervalCompatible start finish i)).powerset.filter
            (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → IntervalCompatible start finish a b)).sup
            (fun F => ∑ a ∈ F, weight a)
          = weight i + ∑ a ∈ F, weight a := by simp only [hFeq]
        _ = ∑ a ∈ insert i F, weight a := (Finset.sum_insert (f := weight) hiF).symm
        _ ≤ ((insert i S).powerset.filter
            (fun F => ∀ a ∈ F, ∀ b ∈ F, a ≠ b → IntervalCompatible start finish a b)).sup
            (fun F => ∑ a ∈ F, weight a) :=
            Finset.le_sup (f := fun F => ∑ a ∈ F, weight a) hmem

end Cslib.Algorithms.Lean.WeightedIntervalScheduling
