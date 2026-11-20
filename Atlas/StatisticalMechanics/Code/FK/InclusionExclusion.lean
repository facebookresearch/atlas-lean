/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































import Mathlib
import Code.Inequalities.IncreasingEvent

open StatMech ConfigSpace
open scoped BigOperators Pointwise

namespace StatMech

namespace FK

variable {E : Type*}






def incrIndicators (E : Type*) : Set (ConfigSpace E → ℝ) :=
  {f | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧ f = A.indicator 1}



lemma one_mem_incrIndicators : (1 : ConfigSpace E → ℝ) ∈ incrIndicators E :=
  ⟨Set.univ, isUpperSet_univ, by simp⟩



lemma openEvent_increasing (e : E) : IsIncreasing {ω : ConfigSpace E | ω e = true} := by
  intro x y hxy hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  exact Bool.le_iff_imp.mp (hxy e) hx


lemma openIndicator_mem (e : E) :
    ({ω : ConfigSpace E | ω e = true}).indicator (1 : ConfigSpace E → ℝ) ∈ incrIndicators E :=
  ⟨_, openEvent_increasing e, rfl⟩







def SignedIncreasingCombo (f : ConfigSpace E → ℝ) : Prop :=
  f ∈ Submodule.span ℝ (incrIndicators E)





theorem signedIncreasingCombo_iff (f : ConfigSpace E → ℝ) :
    SignedIncreasingCombo f ↔
      ∃ (ι : Type) (s : Finset ι) (c : ι → ℝ) (A : ι → Set (ConfigSpace E)),
        (∀ i ∈ s, IsIncreasing (A i)) ∧
          f = ∑ i ∈ s, c i • (A i).indicator (1 : ConfigSpace E → ℝ) := by
  constructor
  · intro hf
    
    rw [SignedIncreasingCombo, Submodule.mem_span_set'] at hf
    obtain ⟨n, c, g, hsum⟩ := hf
    
    classical
    refine ⟨Fin n, Finset.univ, c,
      fun i => ((g i).2).choose, fun i _ => ((g i).2).choose_spec.1, ?_⟩
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ((g i).2).choose_spec.2]
  · rintro ⟨ι, s, c, A, hA, rfl⟩
    refine Submodule.sum_mem _ fun i hi => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨A i, hA i hi, rfl⟩)








lemma span_mul_mem {f g : ConfigSpace E → ℝ}
    (hf : f ∈ Submodule.span ℝ (incrIndicators E))
    (hg : g ∈ Submodule.span ℝ (incrIndicators E)) :
    f * g ∈ Submodule.span ℝ (incrIndicators E) := by
  have hmul : incrIndicators E * incrIndicators E ⊆ incrIndicators E := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨A, hA, rfl⟩ := ha
    obtain ⟨B, hB, rfl⟩ := hb
    exact ⟨A ∩ B, IsUpperSet.inter hA hB, Set.inter_indicator_one.symm⟩
  have h : f * g ∈ Submodule.span ℝ (incrIndicators E) * Submodule.span ℝ (incrIndicators E) :=
    Submodule.mul_mem_mul hf hg
  rw [Submodule.span_mul_span] at h
  exact Submodule.span_mono hmul h



lemma prod_mem_span {ι : Type*} (s : Finset ι) (f : ι → ConfigSpace E → ℝ)
    (hf : ∀ i ∈ s, f i ∈ Submodule.span ℝ (incrIndicators E)) :
    (∏ i ∈ s, f i) ∈ Submodule.span ℝ (incrIndicators E) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact Submodule.subset_span one_mem_incrIndicators
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact span_mul_mem (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))





lemma matcher_mem (e : E) (b : Bool) :
    (fun ω : ConfigSpace E => if ω e = b then (1 : ℝ) else 0)
      ∈ Submodule.span ℝ (incrIndicators E) := by
  cases b with
  | true =>
    have h : (fun ω : ConfigSpace E => if ω e = true then (1 : ℝ) else 0)
        = ({ω : ConfigSpace E | ω e = true}).indicator 1 := by
      ext ω; rw [Set.indicator_apply]; simp [Set.mem_setOf_eq]
    rw [h]; exact Submodule.subset_span (openIndicator_mem e)
  | false =>
    have h : (fun ω : ConfigSpace E => if ω e = false then (1 : ℝ) else 0)
        = (1 : ConfigSpace E → ℝ) - ({ω : ConfigSpace E | ω e = true}).indicator 1 := by
      ext ω
      simp only [Pi.sub_apply, Pi.one_apply, Set.indicator_apply, Set.mem_setOf_eq]
      cases hb : ω e <;> simp
    rw [h]
    exact sub_mem (Submodule.subset_span one_mem_incrIndicators)
      (Submodule.subset_span (openIndicator_mem e))






def cyl (S : Finset E) (ψ : ConfigSpace E) : Set (ConfigSpace E) :=
  {ω | ∀ e ∈ S, ω e = ψ e}



lemma cyl_indicator_eq_prod (S : Finset E) (ψ : ConfigSpace E) :
    (cyl S ψ).indicator (1 : ConfigSpace E → ℝ)
      = ∏ e ∈ S, (fun ω : ConfigSpace E => if ω e = ψ e then (1 : ℝ) else 0) := by
  classical
  ext ω
  rw [Finset.prod_apply, Set.indicator_apply]
  simp only [cyl, Set.mem_setOf_eq, Pi.one_apply]
  split_ifs with h
  · symm; exact Finset.prod_eq_one fun e he => if_pos (h e he)
  · symm
    obtain ⟨e, he, hne⟩ : ∃ e ∈ S, ω e ≠ ψ e := by
      by_contra hcon
      exact h fun e he => not_ne_iff.mp fun hne => hcon ⟨e, he, hne⟩
    exact Finset.prod_eq_zero he (if_neg hne)





theorem cyl_indicator_signedIncreasingCombo (S : Finset E) (ψ : ConfigSpace E) :
    SignedIncreasingCombo ((cyl S ψ).indicator (1 : ConfigSpace E → ℝ)) := by
  rw [SignedIncreasingCombo, cyl_indicator_eq_prod]
  exact prod_mem_span S _ fun e _ => matcher_mem e (ψ e)

section Representatives

variable [DecidableEq E]




noncomputable def repOf (S : Finset E) (φ : ↥S → Bool) : ConfigSpace E :=
  fun e => if h : e ∈ S then φ ⟨e, h⟩ else false


lemma repOf_agree (S : Finset E) (φ : ↥S → Bool) {e : E} (he : e ∈ S) :
    repOf S φ e = φ ⟨e, he⟩ := by
  simp only [repOf, dif_pos he]






theorem indicator_eq_sum_cyl (C : Set (ConfigSpace E)) (S : Finset E)
    (hC : DependsOn (C.indicator (1 : ConfigSpace E → ℝ)) (S : Set E)) :
    C.indicator (1 : ConfigSpace E → ℝ)
      = ∑ φ : ↥S → Bool,
          (C.indicator (1 : ConfigSpace E → ℝ) (repOf S φ)) •
            (cyl S (repOf S φ)).indicator 1 := by
  ext ω
  rw [Finset.sum_apply,
    Finset.sum_eq_single_of_mem (fun i : ↥S => ω i.1) (Finset.mem_univ _)]
  · have hmem : ω ∈ cyl S (repOf S (fun i : ↥S => ω i.1)) := by
      intro e he; rw [repOf_agree S _ he]
    rw [Pi.smul_apply, Set.indicator_of_mem hmem, Pi.one_apply, smul_eq_mul, mul_one]
    refine hC ?_
    intro e he
    rw [repOf_agree S _ he]
  · intro φ _ hne
    have hnmem : ω ∉ cyl S (repOf S φ) := by
      intro hmem
      apply hne
      funext i
      have hh := hmem i.1 i.2
      rw [repOf_agree S φ i.2] at hh
      rw [hh]
    rw [Pi.smul_apply, Set.indicator_of_notMem hnmem, smul_zero]











theorem indicator_signedIncreasingCombo_of_dependsOn
    (C : Set (ConfigSpace E)) (S : Finset E)
    (hC : DependsOn (C.indicator (1 : ConfigSpace E → ℝ)) (S : Set E)) :
    SignedIncreasingCombo (C.indicator (1 : ConfigSpace E → ℝ)) := by
  rw [SignedIncreasingCombo, indicator_eq_sum_cyl C S hC]
  refine Submodule.sum_mem _ fun φ _ => Submodule.smul_mem _ _ ?_
  exact cyl_indicator_signedIncreasingCombo S (repOf S φ)

end Representatives

end FK

end StatMech
