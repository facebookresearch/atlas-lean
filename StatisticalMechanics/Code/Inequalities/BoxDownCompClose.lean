/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Code.Inequalities.ReimerIterationClose

open Finset MeasureTheory
open scoped NNReal FinsetFamily

namespace StatMech

open ConfigSpace







def bdc2_A : Finset (Finset (Fin 2)) := {∅, {0}, {1}}


def bdc2_B : Finset (Finset (Fin 2)) := {∅, {0}, {0,1}}


noncomputable def bdc2_w : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2


def bdc2_FF : ConfigSpace (Fin 2) := ![false, false]


def bdc2_TF : ConfigSpace (Fin 2) := ![true, false]


def bdc2_TT : ConfigSpace (Fin 2) := ![true, true]

lemma bdc2_w_nonneg : ∀ x b, 0 ≤ bdc2_w x b := fun _ _ => by norm_num [bdc2_w]

lemma bdc2_w_prob : ∀ x, bdc2_w x false + bdc2_w x true = 1 := fun _ => by norm_num [bdc2_w]

lemma bdc2_w_symm : ∀ x, bdc2_w x false = bdc2_w x true := fun _ => rfl







lemma bdc2_downComp_A : Down.compression 0 bdc2_A = bdc2_A := by decide


lemma bdc2_downComp_B : Down.compression 0 bdc2_B = bdc2_A := by decide




lemma bdc2_support_FF : cfgSupport bdc2_FF = (∅ : Finset (Fin 2)) := by decide


lemma bdc2_support_TF : cfgSupport bdc2_TF = ({0} : Finset (Fin 2)) := by decide


lemma bdc2_support_TT : cfgSupport bdc2_TT = ({0, 1} : Finset (Fin 2)) := by decide


lemma bdc2_TF_ne_FF : bdc2_TF ≠ bdc2_FF := by decide


lemma bdc2_config_of_support_in_AB {ω : ConfigSpace (Fin 2)}
    (h : cfgSupport ω = ∅ ∨ cfgSupport ω = {0}) : ω = bdc2_FF ∨ ω = bdc2_TF := by
  rcases h with h | h
  · left; have := supportCfg_cfgSupport ω; rw [h] at this; rw [← this]; decide
  · right; have := supportCfg_cfgSupport ω; rw [h] at this; rw [← this]; decide








lemma bdc2_support_mem_A_of_zero_false {ω : ConfigSpace (Fin 2)} (h0 : ω 0 = false) :
    cfgSupport ω ∈ bdc2_A := by
  have hsub : cfgSupport ω ⊆ ({1} : Finset (Fin 2)) := by
    intro i hi
    rw [mem_cfgSupport] at hi
    rw [Finset.mem_singleton]
    fin_cases i
    · exact absurd (h0 ▸ hi) (by decide)
    · rfl
  rcases Finset.subset_singleton_iff.mp hsub with h | h <;> rw [h] <;> decide


lemma bdc2_support_mem_A_of_one_false {ω : ConfigSpace (Fin 2)} (h1 : ω 1 = false) :
    cfgSupport ω ∈ bdc2_A := by
  have hmem : cfgSupport ω ⊆ ({0} : Finset (Fin 2)) := by
    intro i hi
    rw [mem_cfgSupport] at hi
    rw [Finset.mem_singleton]
    fin_cases i
    · rfl
    · exact absurd (h1 ▸ hi) (by decide)
  rcases Finset.subset_singleton_iff.mp hmem with h | h <;> rw [h] <;> decide


lemma bdc2_support_mem_B_of_one_false {ω : ConfigSpace (Fin 2)} (h1 : ω 1 = false) :
    cfgSupport ω ∈ bdc2_B := by
  have hmem : cfgSupport ω ⊆ ({0} : Finset (Fin 2)) := by
    intro i hi
    rw [mem_cfgSupport] at hi
    rw [Finset.mem_singleton]
    fin_cases i
    · rfl
    · exact absurd (h1 ▸ hi) (by decide)
  rcases Finset.subset_singleton_iff.mp hmem with h | h <;> rw [h] <;> decide


lemma bdc2_support_mem_B_of_zero_true {ω : ConfigSpace (Fin 2)} (h0 : ω 0 = true) :
    cfgSupport ω ∈ bdc2_B := by
  have hmem : (0 : Fin 2) ∈ cfgSupport ω := by rw [mem_cfgSupport]; exact h0
  have hsub : cfgSupport ω ⊆ ({0, 1} : Finset (Fin 2)) := fun i _ => by fin_cases i <;> decide
  have hgen : ∀ s : Finset (Fin 2),
      s ∈ ({0, 1} : Finset (Fin 2)).powerset → (0 : Fin 2) ∈ s → s ∈ bdc2_B := by decide
  exact hgen _ (Finset.mem_powerset.mpr hsub) hmem





lemma bdc2_FF_mem_box_AB :
    bdc2_FF ∈ disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_B) := by
  refine ⟨({0} : Set (Fin 2)), ({1} : Set (Fin 2)), ?_, ?_, ?_⟩
  · rw [Set.disjoint_singleton]; decide
  · intro ω' hag
    rw [mem_familyEvent]
    exact bdc2_support_mem_A_of_zero_false (hag 0 (by simp))
  · intro ω' hag
    rw [mem_familyEvent]
    exact bdc2_support_mem_B_of_one_false (hag 1 (by simp))



lemma bdc2_TF_mem_box_AB :
    bdc2_TF ∈ disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_B) := by
  refine ⟨({1} : Set (Fin 2)), ({0} : Set (Fin 2)), ?_, ?_, ?_⟩
  · rw [Set.disjoint_singleton]; decide
  · intro ω' hag
    rw [mem_familyEvent]
    have : ω' 1 = bdc2_TF 1 := hag 1 (by simp)
    exact bdc2_support_mem_A_of_one_false (by rw [this]; decide)
  · intro ω' hag
    rw [mem_familyEvent]
    have : ω' 0 = bdc2_TF 0 := hag 0 (by simp)
    exact bdc2_support_mem_B_of_zero_true (by rw [this]; decide)



lemma bdc2_FF_mem_box_compressed :
    bdc2_FF ∈ disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_A) := by
  refine ⟨({0} : Set (Fin 2)), ({1} : Set (Fin 2)), ?_, ?_, ?_⟩
  · rw [Set.disjoint_singleton]; decide
  · intro ω' hag
    rw [mem_familyEvent]
    exact bdc2_support_mem_A_of_zero_false (hag 0 (by simp))
  · intro ω' hag
    rw [mem_familyEvent]
    
    have h1 : ω' 1 = false := hag 1 (by simp)
    have hsub : cfgSupport ω' ⊆ ({0} : Finset (Fin 2)) := by
      intro i hi
      rw [mem_cfgSupport] at hi
      rw [Finset.mem_singleton]
      fin_cases i
      · rfl
      · exact absurd (h1 ▸ hi) (by decide)
    rcases Finset.subset_singleton_iff.mp hsub with h | h <;> rw [h] <;> decide









lemma bdc2_TT_notMem_familyEvent_A : bdc2_TT ∉ familyEvent bdc2_A := by
  rw [mem_familyEvent, bdc2_support_TT]; decide





lemma bdc2_occursOn_forces_one {K : Set (Fin 2)}
    (h : OccursOn (familyEvent bdc2_A) K bdc2_TF) : (1 : Fin 2) ∈ K := by
  by_contra h1
  have hag : agreeOn K bdc2_TF bdc2_TT := by
    intro e he
    fin_cases e
    · rfl
    · exact absurd he h1
  exact bdc2_TT_notMem_familyEvent_A (h bdc2_TT hag)



lemma bdc2_TF_notMem_box_compressed :
    bdc2_TF ∉ disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_A) := by
  rintro ⟨K, L, hKL, hK, hL⟩
  have h1K : (1 : Fin 2) ∈ K := bdc2_occursOn_forces_one hK
  have h1L : (1 : Fin 2) ∈ L := bdc2_occursOn_forces_one hL
  exact (Set.disjoint_left.mp hKL h1K) h1L








theorem bdc2_box_AB :
    disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_B)
      = ({bdc2_FF, bdc2_TF} : Set (ConfigSpace (Fin 2))) := by
  apply Set.Subset.antisymm
  · intro ω hω
    obtain ⟨hA, hB⟩ := disjointOccurrence_subset_inter _ _ hω
    rw [mem_familyEvent] at hA hB
    have hint : cfgSupport ω = ∅ ∨ cfgSupport ω = {0} :=
      (by decide : ∀ s : Finset (Fin 2), s ∈ bdc2_A → s ∈ bdc2_B → s = ∅ ∨ s = {0})
        _ hA hB
    rcases bdc2_config_of_support_in_AB hint with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro ω hω
    rcases hω with h | h
    · rw [h]; exact bdc2_FF_mem_box_AB
    · rw [Set.mem_singleton_iff] at h; rw [h]; exact bdc2_TF_mem_box_AB


theorem bdc2_box_compressed :
    disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_A)
      = ({bdc2_FF} : Set (ConfigSpace (Fin 2))) := by
  apply Set.Subset.antisymm
  · intro ω hω
    obtain ⟨hA, _⟩ := disjointOccurrence_subset_inter _ _ hω
    rw [mem_familyEvent] at hA
    have hcases : cfgSupport ω = ∅ ∨ cfgSupport ω = {0} ∨ cfgSupport ω = {1} :=
      (by decide : ∀ s : Finset (Fin 2), s ∈ bdc2_A → s = ∅ ∨ s = {0} ∨ s = {1}) _ hA
    rw [Set.mem_singleton_iff]
    rcases hcases with h | h | h
    · have := supportCfg_cfgSupport ω; rw [h] at this; rw [← this]; decide
    · 
      exfalso
      have hωeq : ω = bdc2_TF := by
        have := supportCfg_cfgSupport ω; rw [h] at this; rw [← this]; decide
      rw [hωeq] at hω
      exact bdc2_TF_notMem_box_compressed hω
    · 
      exfalso
      have hωeq : ω = ![false, true] := by
        have := supportCfg_cfgSupport ω; rw [h] at this; rw [← this]; decide
      rw [hωeq] at hω
      obtain ⟨K, L, hKL, hK, hL⟩ := hω
      
      have force : ∀ M : Set (Fin 2),
          OccursOn (familyEvent bdc2_A) M (![false, true] : ConfigSpace (Fin 2)) →
            (0 : Fin 2) ∈ M := by
        intro M hM
        by_contra h0
        have hag : agreeOn M (![false, true] : ConfigSpace (Fin 2)) bdc2_TT := by
          intro e he
          fin_cases e
          · exact absurd he h0
          · rfl
        exact bdc2_TT_notMem_familyEvent_A (hM bdc2_TT hag)
      exact (Set.disjoint_left.mp hKL (force K hK)) (force L hL)
  · intro ω hω
    rw [Set.mem_singleton_iff] at hω; rw [hω]; exact bdc2_FF_mem_box_compressed




lemma bdc2_pweight_TF_pos : 0 < pweight bdc2_w bdc2_TF := by
  simp only [pweight, bdc2_w]; positivity



lemma bdc2_wprob_strict_mono {E : Type*} [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ}
    (hφ : ∀ x b, 0 ≤ φ x b) {S T : Set (ConfigSpace E)} (hST : S ⊆ T)
    {x : ConfigSpace E} (hxT : x ∈ T) (hxS : x ∉ S) (hpx : 0 < pweight φ x) :
    wprob φ S < wprob φ T := by
  unfold wprob
  apply Finset.sum_lt_sum
  · intro ω _
    apply mul_le_mul_of_nonneg_right _ (pweight_nonneg hφ ω)
    by_cases hS : ω ∈ S
    · rw [Set.indicator_of_mem hS, Set.indicator_of_mem (hST hS)]
    · rw [Set.indicator_of_notMem hS]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    rw [Set.indicator_of_notMem hxS, Set.indicator_of_mem hxT, zero_mul, one_mul]
    exact hpx





theorem bdc2_wprob_compressed_lt_AB :
    wprob bdc2_w (disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_A))
      < wprob bdc2_w (disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_B)) := by
  rw [bdc2_box_AB, bdc2_box_compressed]
  apply bdc2_wprob_strict_mono bdc2_w_nonneg
  · intro x hx; exact Or.inl hx
  · exact Or.inr rfl
  · rw [Set.mem_singleton_iff]; exact bdc2_TF_ne_FF
  · exact bdc2_pweight_TF_pos














theorem bdc2_boxDownCompMono_fin2_false : ¬ rit_BoxDownCompMono (Fin 2) := by
  intro h
  have hle := h bdc2_w bdc2_w_nonneg bdc2_w_symm 0 bdc2_A bdc2_B
  rw [bdc2_downComp_A, bdc2_downComp_B] at hle
  exact absurd hle (not_le.mpr bdc2_wprob_compressed_lt_AB)























end StatMech
