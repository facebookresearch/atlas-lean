/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Code.Inequalities.ReimerButterflyInjClose

open Finset MeasureTheory
open scoped NNReal FinsetFamily

namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]









def bfly2 (wit : ConfigSpace α × ConfigSpace α → (α → Bool))
    (p : ConfigSpace α × ConfigSpace α) : ConfigSpace α × ConfigSpace α :=
  (bglue (wit p) p.1 p.2, bglue (wit p) p.2 p.1)

omit [Fintype α] [DecidableEq α] in
@[simp] lemma bfly2_fst (wit : ConfigSpace α × ConfigSpace α → (α → Bool))
    (p : ConfigSpace α × ConfigSpace α) : (bfly2 wit p).1 = bglue (wit p) p.1 p.2 := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] lemma bfly2_snd (wit : ConfigSpace α × ConfigSpace α → (α → Bool))
    (p : ConfigSpace α × ConfigSpace α) : (bfly2 wit p).2 = bglue (wit p) p.2 p.1 := rfl






def rpw_PairDoubleCover (A B : Set (ConfigSpace α)) : Prop :=
  ∃ wit : ConfigSpace α × ConfigSpace α → (α → Bool),
    (∀ p : ConfigSpace α × ConfigSpace α, p.1 ∈ disjointOccurrence A B →
        OccursOn A {a | wit p a = true} p.1) ∧
    (∀ p : ConfigSpace α × ConfigSpace α, p.1 ∈ disjointOccurrence A B →
        OccursOn B {a | wit p a = false} p.1) ∧
    Set.InjOn (bfly2 wit) {p : ConfigSpace α × ConfigSpace α | p.1 ∈ disjointOccurrence A B}








def rpw_p1 : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
  (rbi_cfg false false, rbi_cfg false true)


def rpw_p2 : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
  (rbi_cfg false true, rbi_cfg false false)


lemma rpw_p1_mem :
    rpw_p1 ∈ {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) |
      p.1 ∈ disjointOccurrence rbi_A rbi_B} := rbi_FF_in_box

lemma rpw_p2_mem :
    rpw_p2 ∈ {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) |
      p.1 ∈ disjointOccurrence rbi_A rbi_B} := rbi_FT_in_box


lemma rpw_p1_ne_p2 : rpw_p1 ≠ rpw_p2 := rbi_pairs_ne











theorem rpw_pairDoubleCover_false : ¬ rpw_PairDoubleCover rbi_A rbi_B := by
  rintro ⟨wit, hwitA, hwitB, hinj⟩
  
  obtain ⟨a0, a1⟩ := rbi_force_FF (wit rpw_p1)
    (hwitA rpw_p1 rbi_FF_in_box) (hwitB rpw_p1 rbi_FF_in_box)
  obtain ⟨b0, b1⟩ := rbi_force_FT (wit rpw_p2)
    (hwitA rpw_p2 rbi_FT_in_box) (hwitB rpw_p2 rbi_FT_in_box)
  
  have himg : bfly2 wit rpw_p1 = bfly2 wit rpw_p2 := by
    apply Prod.ext
    · simp only [bfly2_fst, rpw_p1, rpw_p2]
      exact rbi_collision_fst _ _ a0 a1 b0 b1
    · simp only [bfly2_snd, rpw_p1, rpw_p2]
      exact rbi_collision_snd _ _ a0 a1 b0 b1
  exact rpw_p1_ne_p2 (hinj rpw_p1_mem rpw_p2_mem himg)



theorem rpw_pairDoubleCoverAll_false :
    ¬ (∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rpw_PairDoubleCover A B) := by
  intro h
  exact rpw_pairDoubleCover_false (h 2 rbi_A rbi_B)


























def rpw_WeightInjection (A B : Set (ConfigSpace α)) : Prop :=
  ∃ Φ : ConfigSpace α × ConfigSpace α → ConfigSpace α × ConfigSpace α,
    (∀ p : ConfigSpace α × ConfigSpace α, p.1 ∈ disjointOccurrence A B →
        (Φ p).1 ∈ A ∧ (Φ p).2 ∈ B) ∧
    (∀ (φ : α → Bool → ℝ) (p : ConfigSpace α × ConfigSpace α), p.1 ∈ disjointOccurrence A B →
        pweight φ (Φ p).1 * pweight φ (Φ p).2 = pweight φ p.1 * pweight φ p.2) ∧
    Set.InjOn Φ {p : ConfigSpace α × ConfigSpace α | p.1 ∈ disjointOccurrence A B}








theorem rpw_reimer_wprob_of_weightInjection (φ : α → Bool → ℝ) (hφ0 : ∀ x b, 0 ≤ φ x b)
    (hφ1 : ∀ x, φ x false + φ x true = 1) {A B : Set (ConfigSpace α)}
    (hWI : rpw_WeightInjection A B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  classical
  obtain ⟨Φ, hmem, hwt, hinj⟩ := hWI
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
      = ∑ p ∈ boxPairs, g (Φ p) := by
    apply Finset.sum_congr rfl; intro p hp; rw [hbp, Finset.mem_filter] at hp
    have hpbox : p.1 ∈ box := hp.2
    obtain ⟨hmemA, hmemB⟩ := hmem p hpbox
    simp only [hg]
    rw [Set.indicator_of_mem hmemA, Set.indicator_of_mem hmemB, one_mul, one_mul,
      hwt φ p hpbox]
  rw [hwp]
  
  rw [← Finset.sum_image (g := Φ) (f := g)
        (by intro x hx y hy h; rw [hbp, Finset.mem_coe, Finset.mem_filter] at hx hy
            exact hinj hx.2 hy.2 h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hg0 p)










omit [DecidableEq α] in





theorem rpw_weightInjection_of_doubleCover {A B : Set (ConfigSpace α)}
    (hDC : rdc_DoubleCover A B) : rpw_WeightInjection A B := by
  obtain ⟨wit, hwitA, hwitB, hinj⟩ := hDC
  refine ⟨bfly wit, ?_, ?_, hinj⟩
  · intro p hp
    refine ⟨hwitA p.1 hp _ (bglue_agreeOn_true (wit p.1) p.1 p.2),
      hwitB p.1 hp _ (bglue_agreeOn_false (wit p.1) p.1 p.2)⟩
  · intro φ p _
    simp only [bfly_fst, bfly_snd]
    exact bglue_weight φ (wit p.1) p.1 p.2









theorem rpw_weightInjection_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    rpw_WeightInjection A B :=
  rpw_weightInjection_of_doubleCover (rdc_doubleCover_of_disjoint_support hA hB hST)

omit [DecidableEq α] in

theorem rpw_weightInjection_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : rpw_WeightInjection A B :=
  rpw_weightInjection_of_doubleCover (rdc_doubleCover_of_box_empty hbox)








def rpw_WeightInjectionAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rpw_WeightInjection A B




theorem rpw_reimer_wprob_core_of_weightInjection (h : rpw_WeightInjectionAll) :
    ReimerWprobCore := by
  intro n φ hφ0 hφ1 A B
  exact rpw_reimer_wprob_of_weightInjection φ hφ0 hφ1 (h n A B)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in





theorem rpw_reimer_inequality_of_weightInjection (h : rpw_WeightInjectionAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (rpw_reimer_wprob_core_of_weightInjection h) hp A B







































end StatMech
