/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Code.OSSS.Monotonic
import Code.Inequalities.OSSS

open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false

namespace StatMech
namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]









noncomputable def condProbBit (μ : ConfigSpace E → ℝ) (F : Finset E)
    (η : ConfigSpace E) (e : E) (b : Bool) : ℝ :=
  (∑ ω, if (Agree F η ω ∧ ω e = b) then μ ω else 0) / condNorm μ F η



noncomputable def condProbClosed (μ : ConfigSpace E → ℝ) (F : Finset E)
    (η : ConfigSpace E) (e : E) : ℝ :=
  condProbBit μ F η e false



lemma condProbBit_true_add_false (μ : ConfigSpace E → ℝ) (F : Finset E)
    (η : ConfigSpace E) (e : E) (hF : condNorm μ F η ≠ 0) :
    condProbBit μ F η e true + condProbBit μ F η e false = 1 := by
  unfold condProbBit
  rw [← add_div, div_eq_one_iff_eq hF, ← Finset.sum_add_distrib]
  unfold condNorm
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hag : Agree F η ω
  · cases ω e <;> simp [hag]
  · simp [hag]


lemma condProbBit_nonneg {μ : ConfigSpace E → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (F : Finset E)
    (η : ConfigSpace E) (e : E) (b : Bool) (hF : 0 < condNorm μ F η) :
    0 ≤ condProbBit μ F η e b := by
  unfold condProbBit
  refine div_nonneg (Finset.sum_nonneg fun ω _ => ?_) hF.le
  split
  · exact hμ ω
  · rfl


lemma condProbBit_le_one {μ : ConfigSpace E → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (F : Finset E)
    (η : ConfigSpace E) (e : E) (b : Bool) (hF : 0 < condNorm μ F η) :
    condProbBit μ F η e b ≤ 1 := by
  cases b with
  | true =>
    have h1 := condProbBit_true_add_false μ F η e hF.ne'
    have h2 := condProbBit_nonneg hμ F η e false hF
    linarith
  | false =>
    have h1 := condProbBit_true_add_false μ F η e hF.ne'
    have h2 := condProbBit_nonneg hμ F η e true hF
    linarith






omit [Fintype E] [DecidableEq E] in
lemma agree_congr_of_eq_on (F : Finset E) (η η' ω : ConfigSpace E)
    (h : ∀ f ∈ F, η f = η' f) : Agree F η ω ↔ Agree F η' ω := by
  unfold Agree
  constructor <;> intro hyp f hf
  · rw [hyp f hf, h f hf]
  · rw [hyp f hf, ← h f hf]

lemma condNorm_congr (μ : ConfigSpace E → ℝ) (F : Finset E) (η η' : ConfigSpace E)
    (h : ∀ f ∈ F, η f = η' f) : condNorm μ F η = condNorm μ F η' := by
  unfold condNorm
  apply Finset.sum_congr rfl
  intro ω _
  exact if_congr (agree_congr_of_eq_on F η η' ω h) rfl rfl

lemma condProbBit_congr (μ : ConfigSpace E → ℝ) (F : Finset E) (η η' : ConfigSpace E)
    (e : E) (b : Bool) (h : ∀ f ∈ F, η f = η' f) :
    condProbBit μ F η e b = condProbBit μ F η' e b := by
  unfold condProbBit
  rw [condNorm_congr μ F η η' h]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  exact if_congr (and_congr_left (fun _ => agree_congr_of_eq_on F η η' ω h)) rfl rfl

lemma condProbClosed_congr (μ : ConfigSpace E → ℝ) (F : Finset E) (η η' : ConfigSpace E)
    (e : E) (h : ∀ f ∈ F, η f = η' f) :
    condProbClosed μ F η e = condProbClosed μ F η' e :=
  condProbBit_congr μ F η η' e false h








def prefixIdx (n : ℕ) (t : ℕ) : Finset (Fin n) := Finset.univ.filter (fun s => (s : ℕ) < t)


def prefixSet {n : ℕ} (σ : Fin n → E) (t : ℕ) : Finset E := (prefixIdx n t).image σ

omit [Fintype E] in
lemma prefixIdx_zero (n : ℕ) : prefixIdx n 0 = ∅ := by
  unfold prefixIdx; apply Finset.filter_false_of_mem; intro s _; omega

omit [Fintype E] in
lemma prefixIdx_succ_lt (n t : ℕ) (ht : t < n) :
    prefixIdx n (t+1) = insert (⟨t, ht⟩ : Fin n) (prefixIdx n t) := by
  unfold prefixIdx; ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hs; rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
    · exact Or.inr h
    · left; exact Fin.ext h
  · rintro (rfl | h)
    · exact Nat.lt_succ_self t
    · exact Nat.lt_succ_of_lt h

omit [Fintype E] in
lemma prefixIdx_ge (n t : ℕ) (ht : n ≤ t) : prefixIdx n t = Finset.univ := by
  unfold prefixIdx; apply Finset.filter_true_of_mem; intro s _; exact lt_of_lt_of_le s.2 ht

omit [Fintype E] in
lemma prefixIdx_self (n : ℕ) : prefixIdx n n = Finset.univ := prefixIdx_ge n n le_rfl

omit [Fintype E] in
lemma prefixIdx_succ_ge (n t : ℕ) (ht : n ≤ t) : prefixIdx n (t+1) = prefixIdx n t := by
  rw [prefixIdx_ge n t ht, prefixIdx_ge n (t+1) (by omega)]

omit [Fintype E] in
lemma mem_prefixIdx_lt (n t : ℕ) (ht : t < n) : (⟨t, ht⟩ : Fin n) ∉ prefixIdx n t := by
  unfold prefixIdx; simp

omit [Fintype E] in
lemma mem_prefixSet_iff {n : ℕ} (σ : Fin n → E) (k : ℕ) (e : E) :
    e ∈ prefixSet σ k ↔ ∃ s : Fin n, (s : ℕ) < k ∧ σ s = e := by
  unfold prefixSet prefixIdx
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype E] in
lemma prefixSet_zero {n : ℕ} (σ : Fin n → E) : prefixSet σ 0 = ∅ := by
  unfold prefixSet; rw [prefixIdx_zero, Finset.image_empty]

omit [Fintype E] in
lemma prefixSet_succ_lt {n : ℕ} (σ : Fin n → E) (t : ℕ) (ht : t < n) :
    prefixSet σ (t+1) = insert (σ ⟨t, ht⟩) (prefixSet σ t) := by
  unfold prefixSet; rw [prefixIdx_succ_lt n t ht, Finset.image_insert]

omit [Fintype E] in
lemma prefixSet_succ_ge {n : ℕ} (σ : Fin n → E) (t : ℕ) (ht : n ≤ t) :
    prefixSet σ (t+1) = prefixSet σ t := by
  unfold prefixSet; rw [prefixIdx_succ_ge n t ht]



lemma prefixSet_card {n : ℕ} (σ : Fin n ≃ E) :
    prefixSet (σ : Fin n → E) n = Finset.univ := by
  unfold prefixSet prefixIdx
  apply Finset.eq_univ_of_forall
  intro e
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨σ.symm e, (σ.symm e).2, by simp⟩









lemma condNorm_insert (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E) (e : E) :
    condNorm μ (insert e F) η = ∑ ω, if (Agree F η ω ∧ ω e = η e) then μ ω else 0 := by
  unfold condNorm
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨fun f hf => h f (Finset.mem_insert_of_mem hf), h e (Finset.mem_insert_self e F)⟩
  · rintro ⟨hF, he⟩ f hf
    rcases Finset.mem_insert.mp hf with rfl | hf'
    · exact he
    · exact hF f hf'



lemma condProbBit_eq_ratio (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E) (e : E) :
    condProbBit μ F η e (η e) = condNorm μ (insert e F) η / condNorm μ F η := by
  unfold condProbBit; rw [condNorm_insert]



lemma telescope_step (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E) (e : E)
    (hF : condNorm μ F η ≠ 0) :
    condNorm μ (insert e F) η = condProbBit μ F η e (η e) * condNorm μ F η := by
  rw [condProbBit_eq_ratio]; field_simp




lemma condNorm_prefix_telescope (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    {n : ℕ} (σ : Fin n → E) (η : ConfigSpace E) (t : ℕ) :
    condNorm μ (prefixSet σ t) η
      = (∏ s ∈ prefixIdx n t, condProbBit μ (prefixSet σ (s : ℕ)) η (σ s) (η (σ s)))
        * condNorm μ (∅ : Finset E) η := by
  induction t with
  | zero =>
    rw [prefixIdx_zero, Finset.prod_empty, one_mul, prefixSet_zero]
  | succ t ih =>
    by_cases ht : t < n
    · rw [prefixIdx_succ_lt n t ht, Finset.prod_insert (mem_prefixIdx_lt n t ht),
          prefixSet_succ_lt σ t ht,
          telescope_step μ (prefixSet σ t) η (σ ⟨t, ht⟩)
            (OSSS.Monotonic.condNorm_pos hpos _ _).ne', ih]
      ring
    · have ht' : n ≤ t := not_lt.mp ht
      rw [prefixIdx_succ_ge n t ht', prefixSet_succ_ge σ t ht', ih]



lemma condNorm_empty (μ : ConfigSpace E → ℝ) (η : ConfigSpace E) :
    condNorm μ (∅ : Finset E) η = ∑ ω, μ ω := by
  unfold condNorm Agree
  apply Finset.sum_congr rfl
  intro ω _
  rw [if_pos]
  intro f hf
  exact absurd hf (Finset.notMem_empty f)



lemma condNorm_univ (μ : ConfigSpace E → ℝ) (η : ConfigSpace E) :
    condNorm μ (Finset.univ : Finset E) η = μ η := by
  unfold condNorm
  rw [Finset.sum_eq_single η]
  · rw [if_pos (agree_self _ _)]
  · intro ω _ hne
    rw [if_neg]
    intro hag
    exact hne (funext fun e => hag e (Finset.mem_univ e))
  · intro h; exact absurd (Finset.mem_univ η) h








noncomputable def codePrefix (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u : Fin n → ℝ) : ℕ → ConfigSpace E
  | 0 => fun _ => false
  | (k+1) =>
      let prev := codePrefix μ σ u k
      if hk : k < n then
        Function.update prev (σ ⟨k, hk⟩)
          (decide (u ⟨k, hk⟩ ≥ condProbClosed μ (prefixSet σ k) prev (σ ⟨k, hk⟩)))
      else prev





noncomputable def codeMap (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u : Fin n → ℝ) : ConfigSpace E :=
  codePrefix μ σ u n



lemma codePrefix_succ_self (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u : Fin n → ℝ) (t : ℕ) (ht : t < n) :
    codePrefix μ σ u (t+1) (σ ⟨t, ht⟩)
      = decide (u ⟨t, ht⟩ ≥ condProbClosed μ (prefixSet σ t) (codePrefix μ σ u t) (σ ⟨t, ht⟩)) := by
  conv_lhs => unfold codePrefix
  simp only [ht, dif_pos, Function.update_self]




lemma codePrefix_stable (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (hσ : Function.Injective σ) (u : Fin n → ℝ) (k m : ℕ) (hkm : k ≤ m) (e : E)
    (he : e ∈ prefixSet σ k) :
    codePrefix μ σ u m e = codePrefix μ σ u k e := by
  obtain ⟨s, hs, rfl⟩ := (mem_prefixSet_iff σ k _).mp he
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hkm) with hlt | heq
    · have hkm' : k ≤ m := by omega
      conv_lhs => unfold codePrefix
      by_cases hmn : m < n
      · simp only [hmn, dif_pos]
        have hne : σ s ≠ σ ⟨m, hmn⟩ := by
          intro h; have := hσ h; rw [this] at hs; simp at hs; omega
        rw [Function.update_of_ne hne]; exact ih hkm'
      · simp only [hmn, dif_neg, not_false_iff]; exact ih hkm'
    · rw [heq]



lemma codePrefix_agree_codeMap (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (hσ : Function.Injective σ) (u : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∀ e ∈ prefixSet σ m, codePrefix μ σ u m e = codeMap μ σ u e := by
  intro e he
  unfold codeMap
  exact (codePrefix_stable μ σ hσ u m n hm e he).symm










noncomputable def thr (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E) (x : ConfigSpace E)
    (t : Fin n) : ℝ :=
  condProbClosed μ (prefixSet σ (t : ℕ)) x (σ t)



noncomputable def codeInterval (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (x : ConfigSpace E) (t : Fin n) : Set ℝ :=
  if x (σ t) then Set.Ico (thr μ σ x t) 1 else Set.Ico (0 : ℝ) (thr μ σ x t)




lemma recon (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E) (hσ : Function.Injective σ)
    (x : ConfigSpace E) (u : Fin n → ℝ) (m : ℕ) (hm : m ≤ n)
    (H : ∀ (t : ℕ) (ht : t < m),
        x (σ ⟨t, by omega⟩) = decide (u ⟨t, by omega⟩ ≥ thr μ σ x ⟨t, by omega⟩)) :
    Agree (prefixSet σ m) x (codePrefix μ σ u m) := by
  induction m with
  | zero => intro f hf; simp [prefixSet, prefixIdx] at hf
  | succ m ih =>
    have hmn : m < n := by omega
    have ihA : Agree (prefixSet σ m) x (codePrefix μ σ u m) := by
      apply ih (by omega)
      intro t ht; exact H t (by omega)
    intro f hf
    rw [prefixSet_succ_lt σ m hmn] at hf
    show codePrefix μ σ u (m+1) f = x f
    conv_lhs => unfold codePrefix
    simp only [hmn, dif_pos]
    rcases Finset.mem_insert.mp hf with rfl | hfm
    · rw [Function.update_self]
      have hcong : condProbClosed μ (prefixSet σ m) (codePrefix μ σ u m) (σ ⟨m, hmn⟩)
          = thr μ σ x ⟨m, hmn⟩ := by
        unfold thr
        symm
        exact condProbClosed_congr μ (prefixSet σ m) x (codePrefix μ σ u m) (σ ⟨m, hmn⟩)
          (fun g hg => (ihA g hg).symm)
      rw [hcong]
      have hH := H m (Nat.lt_succ_self m)
      simp only at hH ⊢
      rw [hH]
    · have hne : f ≠ σ ⟨m, hmn⟩ := by
        intro h; rw [h] at hfm
        obtain ⟨s, hs, hseq⟩ := (mem_prefixSet_iff σ m _).mp hfm
        have hsm := hσ hseq
        rw [hsm] at hs; exact (lt_irrefl m) hs
      rw [Function.update_of_ne hne]
      exact ihA f hfm



lemma codeMap_eq_imp (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (hσ : Function.Injective σ) (x : ConfigSpace E) (u : Fin n → ℝ)
    (hx : codeMap μ σ u = x) (t : Fin n) :
    x (σ t) = decide (u t ≥ thr μ σ x t) := by
  obtain ⟨t, ht⟩ := t
  have hstep := codePrefix_succ_self μ σ u t ht
  have hval : codeMap μ σ u (σ ⟨t, ht⟩) = codePrefix μ σ u (t+1) (σ ⟨t, ht⟩) := by
    unfold codeMap
    exact codePrefix_stable μ σ hσ u (t+1) n ht (σ ⟨t, ht⟩)
      (by rw [mem_prefixSet_iff]; exact ⟨⟨t, ht⟩, Nat.lt_succ_self t, rfl⟩)
  have hagree : ∀ g ∈ prefixSet σ t, codePrefix μ σ u t g = x g := by
    intro g hg
    rw [codePrefix_agree_codeMap μ σ hσ u t (by omega) g hg, hx]
  have hcong : condProbClosed μ (prefixSet σ t) (codePrefix μ σ u t) (σ ⟨t, ht⟩)
      = thr μ σ x ⟨t, ht⟩ := by
    unfold thr
    exact condProbClosed_congr μ (prefixSet σ t) (codePrefix μ σ u t) x (σ ⟨t, ht⟩) hagree
  calc x (σ ⟨t, ht⟩)
      = codeMap μ σ u (σ ⟨t, ht⟩) := by rw [hx]
    _ = codePrefix μ σ u (t+1) (σ ⟨t, ht⟩) := hval
    _ = decide (u ⟨t, ht⟩ ≥ condProbClosed μ (prefixSet σ t) (codePrefix μ σ u t) (σ ⟨t, ht⟩)) :=
          hstep
    _ = decide (u ⟨t, ht⟩ ≥ thr μ σ x ⟨t, ht⟩) := by rw [hcong]



lemma codeMap_eq_iff (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (x : ConfigSpace E) (u : Fin n → ℝ) :
    codeMap μ (σ : Fin n → E) u = x
      ↔ ∀ t : Fin n, x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t) := by
  have hσ : Function.Injective (σ : Fin n → E) := σ.injective
  constructor
  · intro hx t; exact codeMap_eq_imp μ (σ : Fin n → E) hσ x u hx t
  · intro H
    have hag : Agree (prefixSet (σ : Fin n → E) n) x (codeMap μ (σ : Fin n → E) u) := by
      unfold codeMap
      exact recon μ (σ : Fin n → E) hσ x u n le_rfl (fun t ht => H ⟨t, ht⟩)
    rw [prefixSet_card σ] at hag
    funext e
    exact hag e (Finset.mem_univ e)


lemma thr_mem_Icc (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) {n : ℕ} (σ : Fin n → E)
    (x : ConfigSpace E) (t : Fin n) : 0 ≤ thr μ σ x t ∧ thr μ σ x t ≤ 1 := by
  have hZ : 0 < condNorm μ (prefixSet σ (t : ℕ)) x := OSSS.Monotonic.condNorm_pos hpos _ _
  unfold thr
  exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) _ x _ false hZ,
         condProbBit_le_one (fun ω => (hpos ω).le) _ x _ false hZ⟩


noncomputable def codeFibre (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (x : ConfigSpace E) : Set (Fin n → ℝ) :=
  {u | (∀ t, u t ∈ Set.Ico (0 : ℝ) 1) ∧ codeMap μ (σ : Fin n → E) u = x}


lemma codeFibre_eq_box (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    codeFibre μ σ x = Set.univ.pi (codeInterval μ (σ : Fin n → E) x) := by
  ext u
  simp only [codeFibre, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨hcube, hx⟩ t
    have hb := (codeMap_eq_iff μ σ x u).mp hx t
    have h0 : 0 ≤ u t := (hcube t).1
    have h1 : u t < 1 := (hcube t).2
    unfold codeInterval
    by_cases hbit : x ((σ : Fin n → E) t)
    · simp only [hbit, if_true]
      rw [hbit] at hb
      have hd : decide (u t ≥ thr μ (σ : Fin n → E) x t) = true := hb.symm
      rw [decide_eq_true_eq] at hd
      exact ⟨hd, h1⟩
    · simp only [hbit, Bool.false_eq_true, if_false]
      rw [Bool.not_eq_true] at hbit
      rw [hbit] at hb
      have hd : decide (u t ≥ thr μ (σ : Fin n → E) x t) = false := hb.symm
      rw [decide_eq_false_iff_not, not_le] at hd
      exact ⟨h0, hd⟩
  · intro hmem
    have hthr := fun t => thr_mem_Icc μ hpos (σ : Fin n → E) x t
    refine ⟨fun t => ?_, ?_⟩
    · have hm := hmem t
      unfold codeInterval at hm
      obtain ⟨h0, h1⟩ := hthr t
      by_cases hbit : x ((σ : Fin n → E) t)
      · simp only [hbit, if_true] at hm
        exact ⟨le_trans h0 hm.1, hm.2⟩
      · simp only [hbit, Bool.false_eq_true, if_false] at hm
        exact ⟨hm.1, lt_of_lt_of_le hm.2 h1⟩
    · rw [codeMap_eq_iff μ σ x u]
      intro t
      have hm := hmem t
      unfold codeInterval at hm
      by_cases hbit : x ((σ : Fin n → E) t)
      · simp only [hbit, if_true] at hm
        rw [hbit]; symm; rw [decide_eq_true_eq]; exact hm.1
      · simp only [hbit, Bool.false_eq_true, if_false] at hm
        rw [Bool.not_eq_true] at hbit
        rw [hbit]; symm; rw [decide_eq_false_iff_not, not_le]; exact hm.2



lemma volume_codeInterval (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    {n : ℕ} (σ : Fin n → E) (x : ConfigSpace E) (t : Fin n) :
    (volume (codeInterval μ σ x t)).toReal
      = condProbBit μ (prefixSet σ (t : ℕ)) x (σ t) (x (σ t)) := by
  have hZ : 0 < condNorm μ (prefixSet σ (t : ℕ)) x := OSSS.Monotonic.condNorm_pos hpos _ _
  have hsum := condProbBit_true_add_false μ (prefixSet σ (t : ℕ)) x (σ t) hZ.ne'
  obtain ⟨h0, h1⟩ := thr_mem_Icc μ hpos σ x t
  have hthr_eq : thr μ σ x t = condProbBit μ (prefixSet σ (t : ℕ)) x (σ t) false := rfl
  unfold codeInterval
  by_cases hbit : x (σ t)
  · simp only [hbit, if_true, Real.volume_Ico]
    rw [ENNReal.toReal_ofReal (by linarith)]
    rw [hthr_eq] at *
    linarith
  · simp only [hbit, Bool.false_eq_true, if_false, Real.volume_Ico, sub_zero]
    rw [ENNReal.toReal_ofReal h0, hthr_eq]





theorem codeProb_eq_mass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    (∏ t : Fin n, condProbBit μ (prefixSet (σ : Fin n → E) (t : ℕ)) x
        ((σ : Fin n → E) t) (x ((σ : Fin n → E) t)))
      = μ x := by
  have htel := condNorm_prefix_telescope μ hpos (σ : Fin n → E) x n
  rw [prefixSet_card σ, condNorm_univ, prefixIdx_self, condNorm_empty, hμ1, mul_one] at htel
  rw [← htel]






theorem volume_codeFibre (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    (volume (codeFibre μ σ x)).toReal = μ x := by
  rw [codeFibre_eq_box μ hpos σ x, volume_pi_pi, ENNReal.toReal_prod]
  rw [← codeProb_eq_mass μ hpos hμ1 σ x]
  apply Finset.prod_congr rfl
  intro t _
  exact volume_codeInterval μ hpos (σ : Fin n → E) x t









open OSSS.DecisionTree

omit [Fintype E] in




lemma eval_eq_of_agree_on_queried (T : DecisionTree E) (ω ω' : ConfigSpace E)
    (h : ∀ e ∈ T.queried ω, ω' e = ω e) : T.eval ω' = T.eval ω := by
  induction T with
  | leaf b => rfl
  | node e t f IHt IHf =>
    have hmem : e ∈ (DecisionTree.node e t f).queried ω := by
      unfold DecisionTree.queried; exact Finset.mem_insert_self e _
    have he : ω' e = ω e := h e hmem
    unfold DecisionTree.eval
    rw [he]
    by_cases hb : ω e
    · simp only [hb, if_true]
      refine IHt ?_
      intro i hi
      apply h i
      unfold DecisionTree.queried
      rw [hb]
      exact Finset.mem_insert_of_mem (by simp only [if_true]; exact hi)
    · simp only [hb, Bool.false_eq_true, if_false]
      refine IHf ?_
      intro i hi
      apply h i
      unfold DecisionTree.queried
      simp only [hb, Bool.false_eq_true, if_false]
      exact Finset.mem_insert_of_mem hi




noncomputable def stoppingTime (T : DecisionTree E) (ω : ConfigSpace E) : ℕ :=
  (T.queried ω).card

omit [Fintype E] in


lemma stoppingTime_eq_card (T : DecisionTree E) (ω : ConfigSpace E) :
    stoppingTime T ω = (T.queried ω).card := rfl

omit [Fintype E] in


lemma eval_determined_by_queried (T : DecisionTree E) (ω ω' : ConfigSpace E)
    (h : ∀ e ∈ T.queried ω, ω' e = ω e) : T.eval ω' = T.eval ω :=
  eval_eq_of_agree_on_queried T ω ω' h

end OSSS.Coding
end StatMech
