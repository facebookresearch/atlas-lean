/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































































import Code.Inequalities.ReimerCompressionClose
import Code.Inequalities.ReimerIterationClose

open Finset MeasureTheory
open scoped NNReal FinsetFamily

namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]








def bglue (K : α → Bool) (ω τ : ConfigSpace α) : ConfigSpace α :=
  fun a => if K a then ω a else τ a

omit [Fintype α] [DecidableEq α] in

lemma bglue_agreeOn_true (K : α → Bool) (ω τ : ConfigSpace α) :
    agreeOn {a | K a = true} ω (bglue K ω τ) := by
  intro e he; simp only [Set.mem_setOf_eq] at he; simp only [bglue, he, if_true]

omit [Fintype α] [DecidableEq α] in


lemma bglue_agreeOn_false (K : α → Bool) (ω τ : ConfigSpace α) :
    agreeOn {a | K a = false} ω (bglue K τ ω) := by
  intro e he; simp only [Set.mem_setOf_eq] at he
  simp only [bglue, he]; rfl

omit [DecidableEq α] in







lemma bglue_weight (φ : α → Bool → ℝ) (K : α → Bool) (ω τ : ConfigSpace α) :
    pweight φ (bglue K ω τ) * pweight φ (bglue K τ ω) = pweight φ ω * pweight φ τ := by
  simp only [pweight, bglue]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun a _ => by by_cases h : K a <;> simp [h, mul_comm])

omit [Fintype α] [DecidableEq α] in



lemma bglue_bglue_left (K : α → Bool) (ω τ : ConfigSpace α) :
    bglue K (bglue K ω τ) (bglue K τ ω) = ω := by
  funext a; simp only [bglue]; by_cases h : K a <;> simp [h]

omit [Fintype α] [DecidableEq α] in

lemma bglue_bglue_right (K : α → Bool) (ω τ : ConfigSpace α) :
    bglue K (bglue K τ ω) (bglue K ω τ) = τ := by
  funext a; simp only [bglue]; by_cases h : K a <;> simp [h]











def bfly (wit : ConfigSpace α → (α → Bool)) (p : ConfigSpace α × ConfigSpace α) :
    ConfigSpace α × ConfigSpace α :=
  (bglue (wit p.1) p.1 p.2, bglue (wit p.1) p.2 p.1)

omit [Fintype α] [DecidableEq α] in
@[simp] lemma bfly_fst (wit : ConfigSpace α → (α → Bool)) (p : ConfigSpace α × ConfigSpace α) :
    (bfly wit p).1 = bglue (wit p.1) p.1 p.2 := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] lemma bfly_snd (wit : ConfigSpace α → (α → Bool)) (p : ConfigSpace α × ConfigSpace α) :
    (bfly wit p).2 = bglue (wit p.1) p.2 p.1 := rfl













def rdc_DoubleCover (A B : Set (ConfigSpace α)) : Prop :=
  ∃ wit : ConfigSpace α → (α → Bool),
    (∀ ω ∈ disjointOccurrence A B, OccursOn A {a | wit ω a = true} ω) ∧
    (∀ ω ∈ disjointOccurrence A B, OccursOn B {a | wit ω a = false} ω) ∧
    Set.InjOn (bfly wit) {p : ConfigSpace α × ConfigSpace α | p.1 ∈ disjointOccurrence A B}

















theorem rdc_reimer_wprob_of_doubleCover (φ : α → Bool → ℝ) (hφ0 : ∀ x b, 0 ≤ φ x b)
    (hφ1 : ∀ x, φ x false + φ x true = 1) {A B : Set (ConfigSpace α)}
    (hDC : rdc_DoubleCover A B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  classical
  obtain ⟨wit, hwitA, hwitB, hinj⟩ := hDC
  set box := disjointOccurrence A B with hbox
  have hsum1 : (∑ τ : ConfigSpace α, pweight φ τ) = 1 := sum_pweight_eq_one hφ1
  
  set g : ConfigSpace α × ConfigSpace α → ℝ :=
    fun p => (A.indicator (fun _ => (1 : ℝ)) p.1 * pweight φ p.1) *
             (B.indicator (fun _ => (1 : ℝ)) p.2 * pweight φ p.2) with hg
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p; apply mul_nonneg <;> apply mul_nonneg
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · exact pweight_nonneg hφ0 _
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · exact pweight_nonneg hφ0 _
  
  have hlhs : wprob φ box = ∑ p : ConfigSpace α × ConfigSpace α,
      box.indicator (fun _ => (1 : ℝ)) p.1 * (pweight φ p.1 * pweight φ p.2) := by
    rw [Fintype.sum_prod_type]
    simp only [wprob]
    apply Finset.sum_congr rfl; intro ω _
    have : (∑ τ : ConfigSpace α, box.indicator (fun _ => (1 : ℝ)) ω * (pweight φ ω * pweight φ τ))
        = box.indicator (fun _ => (1 : ℝ)) ω * pweight φ ω * ∑ τ : ConfigSpace α, pweight φ τ := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro τ _; ring
    rw [this, hsum1, mul_one]
  
  have hrhs : wprob φ A * wprob φ B = ∑ p : ConfigSpace α × ConfigSpace α, g p := by
    simp only [wprob, Finset.sum_mul_sum, hg, Fintype.sum_prod_type]
  rw [hlhs, hrhs]
  
  set boxPairs := Finset.univ.filter
    (fun p : ConfigSpace α × ConfigSpace α => p.1 ∈ box) with hbp
  have hlhs2 : (∑ p : ConfigSpace α × ConfigSpace α,
        box.indicator (fun _ => (1 : ℝ)) p.1 * (pweight φ p.1 * pweight φ p.2))
      = ∑ p ∈ boxPairs, pweight φ p.1 * pweight φ p.2 := by
    rw [hbp, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun p : ConfigSpace α × ConfigSpace α => p.1 ∈ box)]
    have hz : (∑ p ∈ Finset.univ.filter
          (fun p : ConfigSpace α × ConfigSpace α => ¬ p.1 ∈ box),
          box.indicator (fun _ => (1 : ℝ)) p.1 * (pweight φ p.1 * pweight φ p.2)) = 0 := by
      apply Finset.sum_eq_zero; intro p hp; rw [Finset.mem_filter] at hp
      rw [Set.indicator_of_notMem hp.2, zero_mul]
    rw [hz, add_zero]
    apply Finset.sum_congr rfl; intro p hp; rw [Finset.mem_filter] at hp
    rw [Set.indicator_of_mem hp.2, one_mul]
  rw [hlhs2]
  
  have hwp : (∑ p ∈ boxPairs, pweight φ p.1 * pweight φ p.2)
      = ∑ p ∈ boxPairs, g (bfly wit p) := by
    apply Finset.sum_congr rfl; intro p hp; rw [hbp, Finset.mem_filter] at hp
    have hpbox : p.1 ∈ box := hp.2
    have hmemA : bglue (wit p.1) p.1 p.2 ∈ A :=
      hwitA p.1 hpbox _ (bglue_agreeOn_true (wit p.1) p.1 p.2)
    have hmemB : bglue (wit p.1) p.2 p.1 ∈ B :=
      hwitB p.1 hpbox _ (bglue_agreeOn_false (wit p.1) p.1 p.2)
    simp only [hg, bfly]
    rw [Set.indicator_of_mem hmemA, Set.indicator_of_mem hmemB, one_mul, one_mul, bglue_weight]
  rw [hwp]
  
  rw [← Finset.sum_image (g := bfly wit) (f := g)
        (by intro x hx y hy h; rw [hbp, Finset.mem_coe, Finset.mem_filter] at hx hy
            exact hinj hx.2 hy.2 h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hg0 p)








omit [Fintype α] [DecidableEq α] in



theorem rdc_bfly_const_injective (K₀ : α → Bool) :
    Function.Injective (bfly (fun _ => K₀) : ConfigSpace α × ConfigSpace α → _) := by
  intro p q h
  simp only [bfly] at h
  have h1 : bglue K₀ p.1 p.2 = bglue K₀ q.1 q.2 := congrArg Prod.fst h
  have h2 : bglue K₀ p.2 p.1 = bglue K₀ q.2 q.1 := congrArg Prod.snd h
  have hp1 := (bglue_bglue_left K₀ p.1 p.2).symm
  have hq1 := bglue_bglue_left K₀ q.1 q.2
  have hp2 := (bglue_bglue_right K₀ p.1 p.2).symm
  have hq2 := bglue_bglue_right K₀ q.1 q.2
  ext a
  · rw [show p.1 = bglue K₀ (bglue K₀ p.1 p.2) (bglue K₀ p.2 p.1) from hp1, h1, h2, hq1]
  · rw [show p.2 = bglue K₀ (bglue K₀ p.2 p.1) (bglue K₀ p.1 p.2) from hp2, h1, h2, hq2]

















theorem rdc_doubleCover_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    rdc_DoubleCover A B := by
  classical
  refine ⟨fun _ => fun a => decide (a ∈ S), ?_, ?_,
    (rdc_bfly_const_injective (fun a => decide (a ∈ S))).injOn⟩
  · 
    intro ω hω
    have hset : {a | (fun b => decide (b ∈ S)) a = true} = (↑S : Set α) := by
      ext a; simp only [Set.mem_setOf_eq, decide_eq_true_eq, Finset.mem_coe]
    rw [hset]
    exact (hA.occursOn_iff ω).mpr (disjointOccurrence_subset_inter A B hω).1
  · 
    intro ω hω
    have hset : {a | (fun b => decide (b ∈ S)) a = false} = (↑Sᶜ : Set α) := by
      ext a
      simp only [Set.mem_setOf_eq, decide_eq_false_iff_not, Finset.coe_compl,
        Set.mem_compl_iff, Finset.mem_coe]
    rw [hset]
    have hTsub : (↑T : Set α) ⊆ (↑Sᶜ : Set α) := by
      intro a ha
      simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe]
      exact fun haS => (Finset.disjoint_left.mp hST) haS (Finset.mem_coe.mp ha)
    exact ((hB.mono hTsub).occursOn_iff ω).mpr (disjointOccurrence_subset_inter A B hω).2






omit [Fintype α] [DecidableEq α] in



theorem rdc_doubleCover_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : rdc_DoubleCover A B := by
  refine ⟨fun _ => fun _ => false, ?_, ?_, ?_⟩
  · intro ω hω; rw [hbox] at hω; exact absurd hω (Set.notMem_empty ω)
  · intro ω hω; rw [hbox] at hω; exact absurd hω (Set.notMem_empty ω)
  · intro p hp; rw [Set.mem_setOf_eq, hbox] at hp; exact absurd hp (Set.notMem_empty p.1)

omit [Fintype α] [DecidableEq α] in


theorem rdc_doubleCover_empty_left (B : Set (ConfigSpace α)) :
    rdc_DoubleCover (∅ : Set (ConfigSpace α)) B := by
  apply rdc_doubleCover_of_box_empty
  rw [Set.eq_empty_iff_forall_notMem]
  intro ω hω
  exact (disjointOccurrence_subset_inter _ _ hω).1









def rdc_DoubleCoverAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rdc_DoubleCover A B




theorem rdc_reimer_wprob_core_of_doubleCover (h : rdc_DoubleCoverAll) : ReimerWprobCore := by
  intro n φ hφ0 hφ1 A B
  exact rdc_reimer_wprob_of_doubleCover φ hφ0 hφ1 (h n A B)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in





theorem rdc_reimer_inequality_of_doubleCover (h : rdc_DoubleCoverAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (rdc_reimer_wprob_core_of_doubleCover h) hp A B








































end StatMech
