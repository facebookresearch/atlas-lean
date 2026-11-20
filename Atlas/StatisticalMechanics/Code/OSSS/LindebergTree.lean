/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Code.OSSS.Lindeberg

open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace LindebergTree

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg

open OSSS.DecisionTree

section Path

variable {E : Type*} [DecidableEq E]


















def pathPrefix : DecisionTree E → ConfigSpace E → ℕ → Finset E
  | leaf _,       _, _       => ∅
  | node _ _ _,   _, 0       => ∅
  | node e t f,   ω, (k + 1) => insert e (pathPrefix (if ω e then t else f) ω k)

@[simp] lemma pathPrefix_leaf (b : Bool) (ω : ConfigSpace E) (t : ℕ) :
    pathPrefix (leaf b) ω t = ∅ := by cases t <;> rfl

@[simp] lemma pathPrefix_zero (T : DecisionTree E) (ω : ConfigSpace E) :
    pathPrefix T ω 0 = ∅ := by cases T <;> rfl

lemma pathPrefix_node_succ (e : E) (t f : DecisionTree E) (ω : ConfigSpace E) (k : ℕ) :
    pathPrefix (node e t f) ω (k + 1)
      = insert e (pathPrefix (if ω e then t else f) ω k) := rfl



def treeDepth : DecisionTree E → ℕ
  | leaf _ => 0
  | node _ t f => max (treeDepth t) (treeDepth f) + 1

lemma queried_leaf (b : Bool) (ω : ConfigSpace E) :
    (DecisionTree.queried (leaf b) ω) = (∅ : Finset E) := rfl

lemma queried_node (e : E) (l r : DecisionTree E) (ω : ConfigSpace E) :
    DecisionTree.queried (node e l r) ω
      = insert e (if ω e then l.queried ω else r.queried ω) := rfl


lemma pathPrefix_subset_queried (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) :
    pathPrefix T ω t ⊆ T.queried ω := by
  induction T generalizing t with
  | leaf b => rw [pathPrefix_leaf, queried_leaf]
  | node e l r IHl IHr =>
    cases t with
    | zero => rw [pathPrefix_zero]; exact Finset.empty_subset _
    | succ k =>
      rw [pathPrefix_node_succ, queried_node]
      apply Finset.insert_subset_insert
      by_cases he : ω e
      · simp only [he, if_true]; exact IHl k
      · simp only [he, Bool.false_eq_true, if_false]; exact IHr k


lemma pathPrefix_mono (T : DecisionTree E) (ω : ConfigSpace E) {s t : ℕ} (hst : s ≤ t) :
    pathPrefix T ω s ⊆ pathPrefix T ω t := by
  induction T generalizing s t with
  | leaf b => rw [pathPrefix_leaf, pathPrefix_leaf]
  | node e l r IHl IHr =>
    cases s with
    | zero => rw [pathPrefix_zero]; exact Finset.empty_subset _
    | succ k =>
      cases t with
      | zero => omega
      | succ m =>
        rw [pathPrefix_node_succ, pathPrefix_node_succ]
        apply Finset.insert_subset_insert
        by_cases he : ω e
        · simp only [he, if_true]; exact IHl (by omega)
        · simp only [he, Bool.false_eq_true, if_false]; exact IHr (by omega)



lemma pathPrefix_ge_depth (T : DecisionTree E) (ω : ConfigSpace E) {s : ℕ}
    (hs : treeDepth T ≤ s) :
    pathPrefix T ω s = T.queried ω := by
  induction T generalizing ω s with
  | leaf b => rw [pathPrefix_leaf, queried_leaf]
  | node e l r IHl IHr =>
    rw [treeDepth] at hs
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    rw [pathPrefix_node_succ, queried_node]
    congr 1
    by_cases he : ω e
    · simp only [he, if_true]
      exact IHl ω (by omega)
    · simp only [he, Bool.false_eq_true, if_false]
      exact IHr ω (by omega)


lemma pathPrefix_depth_eq_queried (T : DecisionTree E) (ω : ConfigSpace E) :
    pathPrefix T ω (treeDepth T) = T.queried ω :=
  pathPrefix_ge_depth T ω le_rfl

end Path


















section Analytic

variable {E : Type*} [Fintype E] [DecidableEq E]



noncomputable def adaptM (μ : ConfigSpace E → ℝ) (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (ω : ConfigSpace E) : ℝ :=
  cExp μ (pathPrefix T ω t) f ω


lemma adaptM_zero {μ : ConfigSpace E → ℝ} (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    adaptM μ T f 0 ω = mean μ f := by
  unfold adaptM
  rw [pathPrefix_zero]
  exact cExp_empty hμ1 f ω





lemma cExp_queried_evalR {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (ω : ConfigSpace E) :
    cExp μ (T.queried ω) (T.evalR) ω = T.evalR ω := by
  unfold cExp condMass
  have hZ : 0 < condNorm μ (T.queried ω) ω := condNorm_pos hpos _ _
  
  have hval : ∀ ω', Agree (T.queried ω) ω ω' →
      T.evalR ω' = T.evalR ω := by
    intro ω' hag
    unfold DecisionTree.evalR
    rw [Coding.eval_eq_of_agree_on_queried T ω ω' (fun e he => hag e he)]
  calc ∑ ω', T.evalR ω' * ((if Agree (T.queried ω) ω ω' then μ ω' else 0) / condNorm μ (T.queried ω) ω)
      = ∑ ω', T.evalR ω * ((if Agree (T.queried ω) ω ω' then μ ω' else 0) / condNorm μ (T.queried ω) ω) := by
        apply Finset.sum_congr rfl
        intro ω' _
        by_cases hag : Agree (T.queried ω) ω ω'
        · rw [if_pos hag, hval ω' hag]
        · rw [if_neg hag]; simp
    _ = T.evalR ω * ∑ ω', ((if Agree (T.queried ω) ω ω' then μ ω' else 0) / condNorm μ (T.queried ω) ω) := by
        rw [Finset.mul_sum]
    _ = T.evalR ω := by
        rw [← Finset.sum_div]
        have : (∑ ω', if Agree (T.queried ω) ω ω' then μ ω' else 0) = condNorm μ (T.queried ω) ω := rfl
        rw [this, div_self hZ.ne', mul_one]



lemma adaptM_depth {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (T : DecisionTree E)
    (ω : ConfigSpace E) :
    adaptM μ T (T.evalR) (treeDepth T) ω = T.evalR ω := by
  unfold adaptM
  rw [pathPrefix_depth_eq_queried]
  exact cExp_queried_evalR hpos T ω




lemma evalR_sub_mean_eq_sum {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E) (ω : ConfigSpace E) :
    T.evalR ω - mean μ (T.evalR)
      = ∑ t ∈ Finset.range (treeDepth T),
          (adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω) := by
  rw [Finset.sum_range_sub (fun t => adaptM μ T (T.evalR) t ω) (treeDepth T)]
  rw [adaptM_depth hpos T ω, adaptM_zero hμ1 T (T.evalR) ω]


noncomputable def meanAbs (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, |g ω| * μ ω


lemma meanAbs_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (g : ConfigSpace E → ℝ) :
    0 ≤ meanAbs μ g :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (abs_nonneg _) (hpos ω).le)



lemma var_le_meanAbs {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {f : ConfigSpace E → ℝ} (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f ≤ meanAbs μ (fun ω => f ω - mean μ f) := by
  have hmean0 : 0 ≤ mean μ f := by
    apply Finset.sum_nonneg; intro ω _; exact mul_nonneg (hf0 ω) (hpos ω).le
  have hmean1 : mean μ f ≤ 1 := by
    calc mean μ f = ∑ ω, f ω * μ ω := rfl
      _ ≤ ∑ ω, 1 * μ ω := by
          apply Finset.sum_le_sum; intro ω _
          exact mul_le_mul_of_nonneg_right (hf1 ω) (hpos ω).le
      _ = 1 := by simp_rw [one_mul]; exact hμ1
  
  set m := mean μ f with hm
  have hvareq : Lindeberg.var μ f = ∑ ω, (f ω - m) ^ 2 * μ ω := by
    have hexpand : ∑ ω, (f ω - m) ^ 2 * μ ω
        = (∑ ω, (f ω * f ω) * μ ω) - 2 * m * (∑ ω, f ω * μ ω) + m ^ 2 * (∑ ω, μ ω) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro ω _; ring
    rw [hexpand, hμ1]
    have hms : (∑ ω, f ω * μ ω) = m := rfl
    unfold Lindeberg.var Lindeberg.cov Lindeberg.mean
    rw [show (∑ x, (fun ω => f ω * f ω) x * μ x) = ∑ ω, (f ω * f ω) * μ ω from rfl]
    rw [hms]
    ring
  rw [hvareq]
  unfold meanAbs
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_right _ (hpos ω).le
  
  have hf0ω : (0 : ℝ) ≤ f ω := hf0 ω
  have hf1ω : f ω ≤ 1 := hf1 ω
  have hbound : |f ω - m| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc (f ω - m) ^ 2 = |f ω - m| ^ 2 := by rw [sq_abs]
    _ = |f ω - m| * |f ω - m| := by ring
    _ ≤ |f ω - m| * 1 := mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = |f ω - m| := by ring


lemma meanAbs_sum_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (s : Finset ℕ)
    (g : ℕ → ConfigSpace E → ℝ) :
    meanAbs μ (fun ω => ∑ t ∈ s, g t ω) ≤ ∑ t ∈ s, meanAbs μ (g t) := by
  unfold meanAbs
  have hswap : (∑ t ∈ s, ∑ ω, |g t ω| * μ ω)
      = ∑ ω, ∑ t ∈ s, |g t ω| * μ ω := Finset.sum_comm
  rw [hswap]
  apply Finset.sum_le_sum
  intro ω _
  simp only []
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (hpos ω).le
  exact Finset.abs_sum_le_sum_abs (fun t => g t ω) s




lemma var_le_sum_step {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (T : DecisionTree E) :
    Lindeberg.var μ (T.evalR)
      ≤ ∑ t ∈ Finset.range (treeDepth T),
          meanAbs μ (fun ω => adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω) := by
  have hstep1 := var_le_meanAbs (μ := μ) hpos hμ1
    (f := T.evalR) (fun ω => T.evalR_nonneg ω) (fun ω => T.evalR_le_one ω)
  refine hstep1.trans ?_
  
  have hrw : meanAbs μ (fun ω => T.evalR ω - mean μ (T.evalR))
      = meanAbs μ (fun ω => ∑ t ∈ Finset.range (treeDepth T),
            (adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω)) := by
    unfold meanAbs
    apply Finset.sum_congr rfl
    intro ω _
    simp only []
    rw [evalR_sub_mean_eq_sum hpos hμ1 T ω]
  rw [hrw]
  exact meanAbs_sum_le hpos (Finset.range (treeDepth T))
    (fun t ω => adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω)










noncomputable def freshAt (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) (e : E) : ℝ :=
  if e ∈ pathPrefix T ω (t + 1) ∧ e ∉ pathPrefix T ω t then (1 : ℝ) else 0



noncomputable def revealmentMu (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (e : E) : ℝ :=
  mean μ (fun ω => if e ∈ T.queried ω then (1 : ℝ) else 0)




lemma freshAt_eq_diff (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) (e : E) :
    freshAt T ω t e
      = (if e ∈ pathPrefix T ω (t + 1) then (1 : ℝ) else 0)
        - (if e ∈ pathPrefix T ω t then (1 : ℝ) else 0) := by
  unfold freshAt
  by_cases h1 : e ∈ pathPrefix T ω (t + 1)
  · by_cases h0 : e ∈ pathPrefix T ω t
    · rw [if_neg (by tauto), if_pos h1, if_pos h0]; ring
    · rw [if_pos ⟨h1, h0⟩, if_pos h1, if_neg h0]; ring
  · have h0 : e ∉ pathPrefix T ω t := fun hmem =>
      h1 (pathPrefix_mono T ω (Nat.le_succ t) hmem)
    rw [if_neg (by tauto), if_neg h1, if_neg h0]; ring




lemma sum_freshAt_eq_queried (T : DecisionTree E) (ω : ConfigSpace E) (e : E) :
    ∑ t ∈ Finset.range (treeDepth T), freshAt T ω t e
      = if e ∈ T.queried ω then (1 : ℝ) else 0 := by
  simp_rw [freshAt_eq_diff T ω]
  rw [Finset.sum_range_sub (fun t => if e ∈ pathPrefix T ω t then (1 : ℝ) else 0) (treeDepth T)]
  rw [pathPrefix_depth_eq_queried, pathPrefix_zero]
  simp



lemma pathPrefix_succ_eq_or_insert (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) :
    pathPrefix T ω (t + 1) = pathPrefix T ω t ∨
      ∃ a, a ∉ pathPrefix T ω t ∧ pathPrefix T ω (t + 1) = insert a (pathPrefix T ω t) := by
  induction T generalizing t ω with
  | leaf b => left; rw [pathPrefix_leaf, pathPrefix_leaf]
  | node eN l r IHl IHr =>
    cases t with
    | zero =>
      rw [pathPrefix_node_succ, pathPrefix_zero]
      by_cases heN : eN ∈ pathPrefix (if ω eN then l else r) ω 0
      · rw [pathPrefix_zero] at heN; exact absurd heN (Finset.notMem_empty eN)
      · right; refine ⟨eN, Finset.notMem_empty eN, ?_⟩
        rw [pathPrefix_zero]
    | succ k =>
      rw [pathPrefix_node_succ, pathPrefix_node_succ]
      set br := (if ω eN then l else r) with hbr
      have IH : pathPrefix br ω (k + 1) = pathPrefix br ω k ∨
          ∃ a, a ∉ pathPrefix br ω k ∧ pathPrefix br ω (k + 1) = insert a (pathPrefix br ω k) := by
        by_cases he : ω eN
        · simp only [hbr, he, if_true]; exact IHl ω k
        · simp only [hbr, he, Bool.false_eq_true, if_false]; exact IHr ω k
      rcases IH with heq | ⟨a, hanew, ha⟩
      · left; rw [heq]
      · rw [ha]
        by_cases haeN : a = eN
        · subst haeN; left; rw [Finset.insert_comm, Finset.insert_idem]
        · by_cases heNmem : eN ∈ pathPrefix br ω k
          · 
            right; refine ⟨a, ?_, ?_⟩
            · rw [Finset.mem_insert]; rintro (rfl | hmem)
              · exact haeN rfl
              · exact hanew hmem
            · rw [Finset.insert_comm]
          · 
            
            right; refine ⟨a, ?_, ?_⟩
            · rw [Finset.mem_insert]; rintro (rfl | hmem)
              · exact haeN rfl
              · exact hanew hmem
            · rw [Finset.insert_comm]



lemma adaptM_step_eq_of_prefix_eq {μ : ConfigSpace E → ℝ} (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (ω : ConfigSpace E)
    (h : pathPrefix T ω (t + 1) = pathPrefix T ω t) :
    adaptM μ T f (t + 1) ω = adaptM μ T f t ω := by
  unfold adaptM; rw [h]





lemma abs_step_eq_sum_freshAt {μ : ConfigSpace E → ℝ} (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (ω : ConfigSpace E) :
    |adaptM μ T f (t + 1) ω - adaptM μ T f t ω|
      = ∑ e, |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e := by
  by_cases hgrow : pathPrefix T ω (t + 1) = pathPrefix T ω t
  · 
    rw [adaptM_step_eq_of_prefix_eq T f t ω hgrow]
    simp only [sub_self, abs_zero, zero_mul, Finset.sum_const_zero]
  · 
    have hsub : pathPrefix T ω t ⊆ pathPrefix T ω (t + 1) :=
      pathPrefix_mono T ω (Nat.le_succ t)
    
    have hsumfresh : (∑ e, freshAt T ω t e)
        = ((pathPrefix T ω (t + 1) \ pathPrefix T ω t).card : ℝ) := by
      unfold freshAt
      rw [Finset.sum_boole]
      congr 1
      apply Finset.card_bij (fun e _ => e)
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        exact Finset.mem_sdiff.mpr ⟨he.1, he.2⟩
      · intro a _ b _ hab; exact hab
      · intro e he
        rw [Finset.mem_sdiff] at he
        exact ⟨e, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨he.1, he.2⟩, rfl⟩
    
    have hcard1 : (pathPrefix T ω (t + 1) \ pathPrefix T ω t).card = 1 := by
      rcases pathPrefix_succ_eq_or_insert T ω t with heq | ⟨a, hanew, ha⟩
      · exact absurd heq hgrow
      · rw [ha, Finset.insert_sdiff_cancel hanew]; simp
    rw [hcard1] at hsumfresh
    rw [← Finset.mul_sum, hsumfresh]
    simp































def StepCovBound (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (f : ConfigSpace E → ℝ) : Prop :=
  ∀ (t : ℕ) (e : E),
    mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e)
      ≤ Lindeberg.cov μ f (coord e) * mean μ (fun ω => freshAt T ω t e)



lemma sum_step_eq_sum_edge {μ : ConfigSpace E → ℝ} (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) :
    ∑ t ∈ Finset.range (treeDepth T),
        meanAbs μ (fun ω => adaptM μ T f (t + 1) ω - adaptM μ T f t ω)
      = ∑ e, ∑ t ∈ Finset.range (treeDepth T),
          mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  
  unfold meanAbs mean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [abs_step_eq_sum_freshAt T f t ω, Finset.sum_mul]



lemma revealmentMu_eq_sum {μ : ConfigSpace E → ℝ} (T : DecisionTree E) (e : E) :
    revealmentMu μ T e
      = ∑ t ∈ Finset.range (treeDepth T), mean μ (fun ω => freshAt T ω t e) := by
  unfold revealmentMu mean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.sum_mul, sum_freshAt_eq_queried T ω e]


lemma mean_freshAt_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (t : ℕ) (e : E) :
    0 ≤ mean μ (fun ω => freshAt T ω t e) := by
  unfold mean
  apply Finset.sum_nonneg; intro ω _
  refine mul_nonneg ?_ (hpos ω).le
  show 0 ≤ freshAt T ω t e
  unfold freshAt; split <;> norm_num



lemma cov_coord_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) {f : ConfigSpace E → ℝ} (hf : Monotone f) (e : E) :
    0 ≤ Lindeberg.cov μ f (coord e) := by
  have hfkg := mean_mul_ge hpos hμ1 hFKG hf (coord_mono e)
  unfold Lindeberg.cov
  linarith [hfkg]




















theorem tree_osss {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (T : DecisionTree E) (hStep : StepCovBound μ T (T.evalR)) :
    Lindeberg.var μ (T.evalR)
      ≤ ∑ e, revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (coord e) := by
  
  have h1 := var_le_sum_step hpos hμ1 T
  rw [sum_step_eq_sum_edge T (T.evalR)] at h1
  refine h1.trans ?_
  
  apply Finset.sum_le_sum
  intro e _
  
  calc ∑ t ∈ Finset.range (treeDepth T),
        mean μ (fun ω => |adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω| * freshAt T ω t e)
      ≤ ∑ t ∈ Finset.range (treeDepth T),
          Lindeberg.cov μ (T.evalR) (coord e) * mean μ (fun ω => freshAt T ω t e) :=
        Finset.sum_le_sum (fun t _ => hStep t e)
    _ = Lindeberg.cov μ (T.evalR) (coord e) * ∑ t ∈ Finset.range (treeDepth T),
          mean μ (fun ω => freshAt T ω t e) := by rw [← Finset.mul_sum]
    _ = revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (coord e) := by
        rw [revealmentMu_eq_sum]; ring









theorem tree_osss_revealment_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (T : DecisionTree E)
    (hfmono : Monotone (T.evalR)) (hStep : StepCovBound μ T (T.evalR))
    (D : ℝ) (hD : ∀ e, revealmentMu μ T e ≤ D) :
    Lindeberg.var μ (T.evalR) ≤ D * ∑ e, Lindeberg.cov μ (T.evalR) (coord e) := by
  refine (tree_osss hpos hμ1 T hStep).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hcov : 0 ≤ Lindeberg.cov μ (T.evalR) (coord e) :=
    cov_coord_nonneg hpos hμ1 hFKG hfmono e
  exact mul_le_mul_of_nonneg_right (hD e) hcov










theorem monotonicOSSSBound_tree {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (T : DecisionTree E)
    (hfmono : Monotone (T.evalR)) (hStep : StepCovBound μ T (T.evalR))
    (D : ℝ) (hD : ∀ e, revealmentMu μ T e ≤ D) :
    OSSS.MonotonicMeasure.MonotonicOSSSBound μ Finset.univ (T.evalR) 1 1 D := by
  unfold OSSS.MonotonicMeasure.MonotonicOSSSBound
  rw [← Lindeberg.var_eq_genVar, Nat.cast_one, one_mul, one_mul]
  have hmain := tree_osss_revealment_le hpos hμ1 hFKG T hfmono hStep D hD
  refine hmain.trans (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  
  rw [← Lindeberg.cov_eq_genCov, ← Lindeberg.coord_eq_genCoord]
  unfold Lindeberg.cov Lindeberg.mean
  rw [show (fun ω => T.evalR ω * coord e ω) = (fun ω => coord e ω * T.evalR ω) from by
        funext ω; ring]
  ring

end Analytic










section FK

open MonotonicFK OSSS.MonotonicMeasure





theorem fk_tree_osss {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (T : DecisionTree (Sym2 V))
    (hStep : StepCovBound (fkMass G p q) T (T.evalR)) :
    Lindeberg.var (fkMass G p q) (T.evalR)
      ≤ ∑ e, revealmentMu (fkMass G p q) T e
          * Lindeberg.cov (fkMass G p q) (T.evalR) (coord e) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact tree_osss (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0) T hStep








theorem fk_monotonicOSSSBound_tree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (T : DecisionTree (Sym2 V))
    (hfmono : Monotone (T.evalR)) (hStep : StepCovBound (fkMass G p q) T (T.evalR))
    (D : ℝ) (hD : ∀ e, revealmentMu (fkMass G p q) T e ≤ D) :
    OSSS.MonotonicMeasure.MonotonicOSSSBound (fkMass G p q) Finset.univ (T.evalR) 1 1 D := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact monotonicOSSSBound_tree (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0)
    (FK.fkProb_FKGLatticeCondition G hp hp1 hq) T hfmono hStep D hD

end FK

end LindebergTree

end OSSS

end StatMech
