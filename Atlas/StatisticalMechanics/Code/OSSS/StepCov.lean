/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































































import Code.OSSS.LindebergTree

open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace StepCov

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg OSSS.LindebergTree
open OSSS.DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]














lemma abs_coord_sub_eq (e : E) (ω : ConfigSpace E) {N : ℝ} (hN0 : 0 ≤ N) (hN1 : N ≤ 1) :
    |coord e ω - N| = coord e ω + N - 2 * coord e ω * N := by
  unfold coord
  by_cases hb : ω e
  · simp only [hb, if_true]
    rw [abs_of_nonneg (by linarith)]; ring
  · simp only [hb, Bool.false_eq_true, if_false]
    rw [abs_of_nonpos (by linarith)]; ring





lemma mean_Fmeas_mul_abs_coord_sub {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (e : E) {g : ConfigSpace E → ℝ} (hg : Fmeas F g) :
    mean μ (fun ω => g ω * |coord e ω - cExp μ F (coord e) ω|)
      = 2 * mean μ (fun ω => g ω * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω))) := by
  set N := cExp μ F (coord e) with hNdef
  
  have hN0 : ∀ ω, 0 ≤ N ω := fun ω => cExp_nonneg hpos F (coord_nonneg e) ω
  have hN1 : ∀ ω, N ω ≤ 1 := fun ω =>
    cExp_le_one hpos F (fun ω => by unfold coord; split <;> norm_num) ω
  
  have hexp : mean μ (fun ω => g ω * |coord e ω - N ω|)
      = mean μ (fun ω => g ω * coord e ω) + mean μ (fun ω => g ω * N ω)
        - 2 * mean μ (fun ω => g ω * coord e ω * N ω) := by
    unfold mean
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    simp only []
    rw [abs_coord_sub_eq e ω (hN0 ω) (hN1 ω)]; ring
  rw [hexp]
  
  have hpull1 : mean μ (fun ω => g ω * coord e ω) = mean μ (fun ω => g ω * N ω) := by
    have hp := cExp_pullout hpos F (coord e) g hg
    unfold mean
    rw [show (fun ω => g ω * coord e ω) = (fun ω => coord e ω * g ω) from by funext ω; ring]
    rw [show (∑ ω, (fun ω => coord e ω * g ω) ω * μ ω) = ∑ ω, (coord e ω * g ω) * μ ω from rfl, ← hp]
    rw [hNdef]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  
  have hgN_Fmeas : Fmeas F (fun ω => g ω * N ω) := by
    intro η η' h
    have h1 := hg η η' h
    have h2 : N η = N η' := (cExp_Fmeas μ F (coord e)) η η' h
    show g η * N η = g η' * N η'; rw [h1, h2]
  have hpull2 : mean μ (fun ω => g ω * coord e ω * N ω) = mean μ (fun ω => g ω * N ω * N ω) := by
    have hp := cExp_pullout hpos F (coord e) (fun ω => g ω * N ω) hgN_Fmeas
    unfold mean
    rw [show (fun ω => g ω * coord e ω * N ω) = (fun ω => coord e ω * (g ω * N ω)) from by
          funext ω; ring]
    rw [show (∑ ω, (fun ω => coord e ω * (g ω * N ω)) ω * μ ω)
          = ∑ ω, (coord e ω * (g ω * N ω)) * μ ω from rfl, ← hp]
    rw [hNdef]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [hpull1, hpull2]
  
  unfold mean
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  ring

















lemma abs_step_eq_delta_mul {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hFKG : FKGLatticeCondition μ) (F : Finset E) (e : E) (he : e ∉ F)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (ω : ConfigSpace E) :
    |cExp μ (insert e F) f ω - cExp μ F f ω|
      = delta μ F e f ω * |coord e ω - cExp μ F (coord e) ω| := by
  rw [step_factor hpos F e he f ω, abs_mul,
      abs_of_nonneg (delta_nonneg hpos hFKG F e hf hf0 ω)]









lemma stepAbs_eq_two_mul {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hFKG : FKGLatticeCondition μ) (F : Finset E) (e : E) (he : e ∉ F)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    {g : ConfigSpace E → ℝ} (hg : Fmeas F g) :
    mean μ (fun ω => g ω * |cExp μ (insert e F) f ω - cExp μ F f ω|)
      = 2 * mean μ (fun ω => (g ω * delta μ F e f ω)
            * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω))) := by
  
  have hrw : (fun ω => g ω * |cExp μ (insert e F) f ω - cExp μ F f ω|)
      = (fun ω => (fun ω => g ω * delta μ F e f ω) ω * |coord e ω - cExp μ F (coord e) ω|) := by
    funext ω
    rw [abs_step_eq_delta_mul hpos hFKG F e he hf hf0 ω]; ring
  rw [hrw]
  
  have hgδ : Fmeas F (fun ω => g ω * delta μ F e f ω) := by
    intro η η' h
    have h1 := hg η η' h
    have h2 := (delta_Fmeas μ F e he f) η η' h
    show g η * delta μ F e f η = g η' * delta μ F e f η'; rw [h1, h2]
  exact mean_Fmeas_mul_abs_coord_sub hpos F e hgδ











lemma pathPrefix_eq_of_agree (T : DecisionTree E) (ω ω' : ConfigSpace E) (t : ℕ)
    (h : Agree (pathPrefix T ω t) ω ω') :
    pathPrefix T ω' t = pathPrefix T ω t := by
  induction T generalizing t ω' with
  | leaf b => rw [pathPrefix_leaf, pathPrefix_leaf]
  | node eN l r IHl IHr =>
    cases t with
    | zero => rw [pathPrefix_zero, pathPrefix_zero]
    | succ k =>
      rw [pathPrefix_node_succ] at h ⊢
      have heN : ω' eN = ω eN := h eN (Finset.mem_insert_self eN _)
      rw [heN]
      have hbr : Agree (pathPrefix (if ω eN then l else r) ω k) ω ω' := by
        intro x hx; exact h x (Finset.mem_insert_of_mem hx)
      congr 1
      by_cases hb : ω eN
      · simp only [hb, if_true] at hbr ⊢; exact IHl ω' k hbr
      · simp only [hb, Bool.false_eq_true, if_false] at hbr ⊢; exact IHr ω' k hbr







lemma pathPrefix_succ_eq_of_agree (T : DecisionTree E) (ω ω' : ConfigSpace E) (t : ℕ)
    (h : Agree (pathPrefix T ω t) ω ω') :
    pathPrefix T ω' (t + 1) = pathPrefix T ω (t + 1) := by
  induction T generalizing t ω' with
  | leaf b => rw [pathPrefix_leaf, pathPrefix_leaf]
  | node eN l r IHl IHr =>
    cases t with
    | zero =>
      rw [pathPrefix_node_succ, pathPrefix_node_succ, pathPrefix_zero, pathPrefix_zero]
    | succ k =>
      rw [pathPrefix_node_succ] at h
      have heN : ω' eN = ω eN := h eN (Finset.mem_insert_self eN _)
      rw [pathPrefix_node_succ, pathPrefix_node_succ, heN]
      have hbr : Agree (pathPrefix (if ω eN then l else r) ω k) ω ω' := by
        intro x hx; exact h x (Finset.mem_insert_of_mem hx)
      congr 1
      by_cases hb : ω eN
      · simp only [hb, if_true] at hbr ⊢; exact IHl ω' k hbr
      · simp only [hb, Bool.false_eq_true, if_false] at hbr ⊢; exact IHr ω' k hbr



lemma pathPrefix_eq_Fmeas (T : DecisionTree E) (F : Finset E) (t : ℕ) :
    Fmeas F (fun ω => if pathPrefix T ω t = F then (1 : ℝ) else 0) := by
  intro η η' h
  show (if pathPrefix T η t = F then (1 : ℝ) else 0)
      = (if pathPrefix T η' t = F then (1 : ℝ) else 0)
  by_cases hη : pathPrefix T η t = F
  · 
    have hag : Agree (pathPrefix T η t) η η' := by
      intro x hx; rw [hη] at hx; exact (h x hx).symm
    have heq : pathPrefix T η' t = pathPrefix T η t := pathPrefix_eq_of_agree T η η' t hag
    rw [if_pos hη, if_pos (by rw [heq, hη])]
  · 
    have hη' : pathPrefix T η' t ≠ F := by
      intro hcontra
      apply hη
      have hag : Agree (pathPrefix T η' t) η' η := by
        intro x hx; rw [hcontra] at hx; exact h x hx
      rw [pathPrefix_eq_of_agree T η' η t hag, hcontra]
    rw [if_neg hη, if_neg hη']




lemma freshPref_Fmeas (T : DecisionTree E) (F : Finset E) (e : E) (t : ℕ) :
    Fmeas F (fun ω =>
      if pathPrefix T ω t = F ∧ pathPrefix T ω (t + 1) = insert e F then (1 : ℝ) else 0) := by
  
  
  have key : ∀ (a b : ConfigSpace E),
      (∀ x ∈ F, a x = b x) →
      pathPrefix T a t = F → pathPrefix T a (t + 1) = insert e F →
      pathPrefix T b t = F ∧ pathPrefix T b (t + 1) = insert e F := by
    intro a b hab hat hat1
    have hag : Agree (pathPrefix T a t) a b := by
      intro x hx; rw [hat] at hx; exact (hab x hx).symm
    refine ⟨?_, ?_⟩
    · rw [pathPrefix_eq_of_agree T a b t hag, hat]
    · rw [pathPrefix_succ_eq_of_agree T a b t hag, hat1]
  intro η η' h
  show (if pathPrefix T η t = F ∧ pathPrefix T η (t + 1) = insert e F then (1 : ℝ) else 0)
      = (if pathPrefix T η' t = F ∧ pathPrefix T η' (t + 1) = insert e F then (1 : ℝ) else 0)
  by_cases hη : pathPrefix T η t = F ∧ pathPrefix T η (t + 1) = insert e F
  · obtain ⟨hηt, hηt1⟩ := hη
    rw [if_pos ⟨hηt, hηt1⟩, if_pos (key η η' h hηt hηt1)]
  · have hη' : ¬ (pathPrefix T η' t = F ∧ pathPrefix T η' (t + 1) = insert e F) := by
      rintro ⟨hη't, hη't1⟩
      exact hη (key η' η (fun x hx => (h x hx).symm) hη't hη't1)
    rw [if_neg hη, if_neg hη']


















noncomputable def freshPI (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) (e : E)
    (F : Finset E) : ℝ :=
  if pathPrefix T ω t = F ∧ pathPrefix T ω (t + 1) = insert e F then (1 : ℝ) else 0


noncomputable def prefSet (e : E) : Finset (Finset E) :=
  Finset.univ.filter (fun F => e ∉ F)





lemma abs_step_freshAt_eq_sum_prefix {μ : ConfigSpace E → ℝ} (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (e : E) (ω : ConfigSpace E) :
    |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e
      = ∑ F ∈ prefSet e,
          |cExp μ (insert e F) f ω - cExp μ F f ω| * freshPI T ω t e F := by
  set P := pathPrefix T ω t with hP
  by_cases hPe : e ∈ P
  · 
    have hfresh0 : freshAt T ω t e = 0 := by
      unfold freshAt; rw [if_neg (by rintro ⟨_, h2⟩; rw [← hP] at h2; exact h2 hPe)]
    rw [hfresh0, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro F hF
    rw [prefSet, Finset.mem_filter] at hF
    
    unfold freshPI
    rw [if_neg (by rintro ⟨h1, _⟩; rw [hP, h1] at hPe; exact hF.2 hPe)]
    simp
  · 
    have hPmem : P ∈ prefSet e := by rw [prefSet, Finset.mem_filter]; exact ⟨Finset.mem_univ P, hPe⟩
    rw [Finset.sum_eq_single_of_mem P hPmem]
    · unfold freshAt freshPI adaptM
      rw [← hP]
      by_cases hgrow : pathPrefix T ω (t + 1) = insert e P
      · have he_in : e ∈ pathPrefix T ω (t + 1) := by rw [hgrow]; exact Finset.mem_insert_self e P
        rw [if_pos ⟨he_in, hPe⟩, if_pos ⟨rfl, hgrow⟩, hgrow]
      · have hfresh0 : ¬ (e ∈ pathPrefix T ω (t + 1) ∧ e ∉ P) := by
          rintro ⟨hin, hnin⟩
          rcases pathPrefix_succ_eq_or_insert T ω t with heq | ⟨a, hanew, ha⟩
          · rw [← hP] at heq; rw [heq] at hin; exact hnin hin
          · rw [← hP] at ha hanew
            rw [ha] at hin
            rcases Finset.mem_insert.mp hin with rfl | hmem
            · exact hgrow (by rw [ha])
            · exact hnin hmem
        rw [if_neg hfresh0, if_neg (by rintro ⟨_, h2⟩; exact hgrow h2)]
        simp
    · 
      intro F _ hFne
      unfold freshPI
      rw [if_neg (by rintro ⟨h1, _⟩; exact hFne (by rw [← h1, ← hP]))]
      simp



lemma freshPI_Fmeas (T : DecisionTree E) (t : ℕ) (e : E) (F : Finset E) :
    Fmeas F (fun ω => freshPI T ω t e F) := freshPref_Fmeas T F e t


lemma freshPI_nonneg (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) (e : E) (F : Finset E) :
    0 ≤ freshPI T ω t e F := by unfold freshPI; split <;> norm_num




lemma mean_step_eq_sum_prefix {μ : ConfigSpace E → ℝ} (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (e : E) :
    mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e)
      = ∑ F ∈ prefSet e,
          mean μ (fun ω =>
            |cExp μ (insert e F) f ω - cExp μ F f ω| * freshPI T ω t e F) := by
  unfold mean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  rw [abs_step_freshAt_eq_sum_prefix T f t e ω, Finset.sum_mul]













theorem mean_step_freshAt_eq {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hFKG : FKGLatticeCondition μ) (T : DecisionTree E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (t : ℕ) (e : E) :
    mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e)
      = 2 * ∑ F ∈ prefSet e,
          mean μ (fun ω => (freshPI T ω t e F * delta μ F e f ω)
            * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω))) := by
  rw [mean_step_eq_sum_prefix T f t e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [prefSet, Finset.mem_filter] at hF
  have hcomm : mean μ (fun ω => |cExp μ (insert e F) f ω - cExp μ F f ω| * freshPI T ω t e F)
      = mean μ (fun ω => freshPI T ω t e F * |cExp μ (insert e F) f ω - cExp μ F f ω|) := by
    unfold mean; exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [hcomm]
  exact stepAbs_eq_two_mul hpos hFKG F e hF.2 hf hf0 (freshPI_Fmeas T t e F)



lemma freshAt_eq_sum_prefix (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) (e : E) :
    freshAt T ω t e = ∑ F ∈ prefSet e, freshPI T ω t e F := by
  
  
  set P := pathPrefix T ω t with hP
  by_cases hPe : e ∈ P
  · have hfresh0 : freshAt T ω t e = 0 := by
      unfold freshAt; rw [if_neg (by rintro ⟨_, h2⟩; rw [← hP] at h2; exact h2 hPe)]
    rw [hfresh0]
    symm
    apply Finset.sum_eq_zero
    intro F hF
    rw [prefSet, Finset.mem_filter] at hF
    unfold freshPI
    rw [if_neg (by rintro ⟨h1, _⟩; rw [hP, h1] at hPe; exact hF.2 hPe)]
  · have hPmem : P ∈ prefSet e := by rw [prefSet, Finset.mem_filter]; exact ⟨Finset.mem_univ P, hPe⟩
    rw [Finset.sum_eq_single_of_mem P hPmem]
    · unfold freshAt freshPI
      rw [← hP]
      by_cases hgrow : pathPrefix T ω (t + 1) = insert e P
      · have he_in : e ∈ pathPrefix T ω (t + 1) := by rw [hgrow]; exact Finset.mem_insert_self e P
        rw [if_pos ⟨he_in, hPe⟩, if_pos ⟨rfl, hgrow⟩]
      · have hfresh0 : ¬ (e ∈ pathPrefix T ω (t + 1) ∧ e ∉ P) := by
          rintro ⟨hin, hnin⟩
          rcases pathPrefix_succ_eq_or_insert T ω t with heq | ⟨a, hanew, ha⟩
          · rw [← hP] at heq; rw [heq] at hin; exact hnin hin
          · rw [← hP] at ha hanew
            rw [ha] at hin
            rcases Finset.mem_insert.mp hin with rfl | hmem
            · exact hgrow (by rw [ha])
            · exact hnin hmem
        rw [if_neg hfresh0, if_neg (by rintro ⟨_, h2⟩; exact hgrow h2)]
    · intro F _ hFne
      unfold freshPI
      rw [if_neg (by rintro ⟨h1, _⟩; exact hFne (by rw [← h1, ← hP]))]



lemma mean_freshAt_eq_sum_prefix {μ : ConfigSpace E → ℝ} (T : DecisionTree E) (t : ℕ) (e : E) :
    mean μ (fun ω => freshAt T ω t e) = ∑ F ∈ prefSet e, mean μ (fun ω => freshPI T ω t e F) := by
  unfold mean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  rw [freshAt_eq_sum_prefix T ω t e, Finset.sum_mul]




























def StepCovResidue (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (f : ConfigSpace E → ℝ)
    (t : ℕ) (e : E) : Prop :=
  ∀ F ∈ prefSet e,
    mean μ (fun ω => (freshPI T ω t e F * delta μ F e f ω)
        * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω)))
      ≤ Lindeberg.cov μ f (coord e) * mean μ (fun ω => freshPI T ω t e F)








def StepCovBoundTwo (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (f : ConfigSpace E → ℝ) : Prop :=
  ∀ (t : ℕ) (e : E),
    mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e)
      ≤ 2 * (Lindeberg.cov μ f (coord e) * mean μ (fun ω => freshAt T ω t e))





theorem stepCovBoundTwo_of_cplFKG {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hFKG : FKGLatticeCondition μ) (T : DecisionTree E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (hres : ∀ t e, StepCovResidue μ T f t e) :
    StepCovBoundTwo μ T f := by
  intro t e
  rw [mean_step_freshAt_eq hpos hFKG T hf hf0 t e, mean_freshAt_eq_sum_prefix T t e]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  calc ∑ F ∈ prefSet e,
        mean μ (fun ω => (freshPI T ω t e F * delta μ F e f ω)
            * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω)))
      ≤ ∑ F ∈ prefSet e, Lindeberg.cov μ f (coord e) * mean μ (fun ω => freshPI T ω t e F) :=
        Finset.sum_le_sum (fun F hF => hres t e F hF)
    _ = Lindeberg.cov μ f (coord e) * ∑ F ∈ prefSet e, mean μ (fun ω => freshPI T ω t e F) := by
        rw [Finset.mul_sum]














theorem var_le_half_meanAbs {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {f : ConfigSpace E → ℝ} (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f ≤ (1 / 2) * meanAbs μ (fun ω => f ω - mean μ f) := by
  have hmean0 : 0 ≤ mean μ f :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (hf0 ω) (hpos ω).le)
  have hmean1 : mean μ f ≤ 1 := by
    calc mean μ f = ∑ ω, f ω * μ ω := rfl
      _ ≤ ∑ ω, 1 * μ ω := Finset.sum_le_sum (fun ω _ =>
            mul_le_mul_of_nonneg_right (hf1 ω) (hpos ω).le)
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
    rw [show (∑ x, (fun ω => f ω * f ω) x * μ x) = ∑ ω, (f ω * f ω) * μ ω from rfl, hms]; ring
  rw [hvareq]
  
  have hbal : ∑ ω, (f ω - m) * μ ω = 0 := by
    rw [show (fun ω => (f ω - m) * μ ω) = (fun ω => f ω * μ ω - m * μ ω) from by funext ω; ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hμ1, mul_one]
    have : (∑ ω, f ω * μ ω) = m := rfl
    rw [this]; ring
  
  
  
  have hkey : ∀ ω, (f ω - m) ^ 2 * μ ω
      ≤ (1 / 2) * (|f ω - m| * μ ω) + (1 / 2) * ((f ω - m) * (1 - 2 * m) * μ ω) := by
    intro ω
    have hμω := (hpos ω).le
    have hf0ω : (0:ℝ) ≤ f ω := hf0 ω
    have hf1ω : f ω ≤ 1 := hf1 ω
    
    have hpt : (f ω - m) ^ 2 ≤ (1 / 2) * |f ω - m| + (1 / 2) * ((f ω - m) * (1 - 2 * m)) := by
      by_cases hsign : m ≤ f ω
      · rw [abs_of_nonneg (by linarith)]
        nlinarith [sq_nonneg (f ω - m), mul_nonneg (sub_nonneg.mpr hsign) (sub_nonneg.mpr hf1ω)]
      · replace hsign : f ω < m := lt_of_not_ge hsign
        rw [abs_of_neg (by linarith)]
        nlinarith [sq_nonneg (f ω - m), mul_nonneg (le_of_lt (sub_pos.mpr hsign)) hmean0]
    calc (f ω - m) ^ 2 * μ ω
        ≤ ((1 / 2) * |f ω - m| + (1 / 2) * ((f ω - m) * (1 - 2 * m))) * μ ω :=
          mul_le_mul_of_nonneg_right hpt hμω
      _ = (1 / 2) * (|f ω - m| * μ ω) + (1 / 2) * ((f ω - m) * (1 - 2 * m) * μ ω) := by ring
  calc ∑ ω, (f ω - m) ^ 2 * μ ω
      ≤ ∑ ω, ((1 / 2) * (|f ω - m| * μ ω) + (1 / 2) * ((f ω - m) * (1 - 2 * m) * μ ω)) :=
        Finset.sum_le_sum (fun ω _ => hkey ω)
    _ = (1 / 2) * (∑ ω, |f ω - m| * μ ω)
          + (1 / 2) * (1 - 2 * m) * (∑ ω, (f ω - m) * μ ω) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rw [show (∑ ω, (f ω - m) * (1 - 2 * m) * μ ω)
              = (1 - 2 * m) * ∑ ω, (f ω - m) * μ ω from by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)]
        ring
    _ = (1 / 2) * meanAbs μ (fun ω => f ω - m) := by
        rw [hbal, mul_zero, add_zero]; unfold meanAbs; rfl














lemma var_le_half_sum_step {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (T : DecisionTree E) :
    Lindeberg.var μ (T.evalR)
      ≤ (1 / 2) * ∑ t ∈ Finset.range (treeDepth T),
          meanAbs μ (fun ω => adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω) := by
  have hstep1 := var_le_half_meanAbs (μ := μ) hpos hμ1
    (f := T.evalR) (fun ω => T.evalR_nonneg ω) (fun ω => T.evalR_le_one ω)
  refine hstep1.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1 / 2)
  
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













theorem tree_osss_sharp {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) (T : DecisionTree E) (hfmono : Monotone (T.evalR))
    (hres : ∀ t e, StepCovResidue μ T (T.evalR) t e) :
    Lindeberg.var μ (T.evalR)
      ≤ ∑ e, revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (coord e) := by
  have hStep : StepCovBoundTwo μ T (T.evalR) :=
    stepCovBoundTwo_of_cplFKG hpos hFKG T hfmono (fun ω => T.evalR_nonneg ω) hres
  
  have h1 := var_le_half_sum_step hpos hμ1 T
  rw [sum_step_eq_sum_edge T (T.evalR)] at h1
  refine h1.trans ?_
  
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  
  calc (1 / 2) * ∑ t ∈ Finset.range (treeDepth T),
        mean μ (fun ω => |adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω| * freshAt T ω t e)
      ≤ (1 / 2) * ∑ t ∈ Finset.range (treeDepth T),
          2 * (Lindeberg.cov μ (T.evalR) (coord e) * mean μ (fun ω => freshAt T ω t e)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1 / 2)
        exact Finset.sum_le_sum (fun t _ => hStep t e)
    _ = Lindeberg.cov μ (T.evalR) (coord e) * ∑ t ∈ Finset.range (treeDepth T),
          mean μ (fun ω => freshAt T ω t e) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
    _ = revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (coord e) := by
        rw [revealmentMu_eq_sum]; ring


















namespace Counterexample


lemma sum_boolfun (g : (Bool → Bool) → ℝ) :
    (∑ ω : (Bool → Bool), g ω) =
      g (fun _ => false) + g (fun b => bif b then true else false)
        + g (fun b => bif b then false else true) + g (fun _ => true) := by
  rw [show (Finset.univ : Finset (Bool → Bool))
        = {(fun _ => false), (fun b => bif b then true else false),
            (fun b => bif b then false else true), (fun _ => true)} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring


noncomputable def muU : ConfigSpace Bool → ℝ := fun _ => 1 / 4


def Tw : DecisionTree Bool := DecisionTree.node false (DecisionTree.leaf true) (DecisionTree.leaf false)


noncomputable def fAvg : ConfigSpace Bool → ℝ := fun ω =>
  (if ω false then (1:ℝ) else 0) * (1 / 2) + (if ω true then (1:ℝ) else 0) * (1 / 2)

lemma muU_pos : ∀ ω, 0 < muU ω := fun _ => by unfold muU; norm_num

lemma muU_sum_one : ∑ ω : ConfigSpace Bool, muU ω = 1 := by
  unfold muU; rw [sum_boolfun]; norm_num

lemma mean_fAvg : mean muU fAvg = 1 / 2 := by
  unfold mean muU fAvg; rw [sum_boolfun]; norm_num

lemma cov_fAvg : Lindeberg.cov muU fAvg (coord false) = 1 / 8 := by
  unfold Lindeberg.cov Lindeberg.mean muU fAvg coord
  rw [sum_boolfun, sum_boolfun, sum_boolfun]; norm_num

lemma condNorm_false : condNorm muU {false} (fun _ => false) = 1 / 2 := by
  unfold condNorm muU Agree; rw [sum_boolfun]; norm_num [Finset.mem_singleton]

lemma condNorm_true : condNorm muU {false} (fun _ => true) = 1 / 2 := by
  unfold condNorm muU Agree; rw [sum_boolfun]; norm_num [Finset.mem_singleton]

lemma cExp_false : cExp muU {false} fAvg (fun _ => false) = 1 / 4 := by
  rw [cExp_eq_cSum_div, condNorm_false]
  unfold cSum muU fAvg Agree; rw [sum_boolfun]; norm_num [Finset.mem_singleton]

lemma cExp_true : cExp muU {false} fAvg (fun _ => true) = 3 / 4 := by
  rw [cExp_eq_cSum_div, condNorm_true]
  unfold cSum muU fAvg Agree; rw [sum_boolfun]; norm_num [Finset.mem_singleton]


lemma pathPrefix_Tw_one (ω : ConfigSpace Bool) : pathPrefix Tw ω 1 = {false} := by
  unfold Tw; rw [pathPrefix_node_succ, pathPrefix_zero]; simp


lemma freshAt_Tw_zero (ω : ConfigSpace Bool) : freshAt Tw ω 0 false = 1 := by
  unfold freshAt; rw [pathPrefix_zero, pathPrefix_Tw_one]; simp


lemma cExp_false_branch (ω : ConfigSpace Bool) :
    cExp muU {false} fAvg ω = if ω false then (3:ℝ)/4 else 1/4 := by
  have hfm := cExp_Fmeas muU {false} fAvg
  by_cases hb : ω false
  · rw [if_pos hb]
    rw [← cExp_true]; apply hfm
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx; rw [hb]
  · rw [if_neg hb]
    rw [← cExp_false]; apply hfm
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    simp only [Bool.not_eq_true] at hb; rw [hb]



lemma mean_step_witness :
    mean muU (fun ω => |adaptM muU Tw fAvg (0 + 1) ω - adaptM muU Tw fAvg 0 ω|
        * freshAt Tw ω 0 false) = 1 / 4 := by
  have hadapt0 : ∀ ω, adaptM muU Tw fAvg 0 ω = 1 / 2 := by
    intro ω; rw [adaptM, pathPrefix_zero, cExp_empty muU_sum_one, mean_fAvg]
  have hadapt1 : ∀ ω, adaptM muU Tw fAvg (0 + 1) ω = if ω false then (3:ℝ)/4 else 1/4 := by
    intro ω; rw [adaptM, pathPrefix_Tw_one, cExp_false_branch]
  have hpt : ∀ ω, |adaptM muU Tw fAvg (0 + 1) ω - adaptM muU Tw fAvg 0 ω|
      * freshAt Tw ω 0 false = 1 / 4 := by
    intro ω
    rw [hadapt0, hadapt1, freshAt_Tw_zero, mul_one]
    by_cases hb : ω false
    · rw [if_pos hb]; rw [show (3:ℝ)/4 - 1/2 = 1/4 from by norm_num, abs_of_pos (by norm_num)]
    · rw [if_neg hb]; rw [show (1:ℝ)/4 - 1/2 = -(1/4) from by norm_num, abs_neg,
        abs_of_pos (by norm_num)]
  unfold mean
  rw [show (fun ω => (fun ω => |adaptM muU Tw fAvg (0 + 1) ω - adaptM muU Tw fAvg 0 ω|
      * freshAt Tw ω 0 false) ω * muU ω) = (fun ω => (1:ℝ)/4 * muU ω) from by
        funext ω; simp only []; rw [hpt ω]]
  rw [← Finset.mul_sum, muU_sum_one, mul_one]




theorem stepCovBound_no_factor_false :
    ¬ LindebergTree.StepCovBound muU Tw fAvg := by
  intro hSCB
  have h := hSCB 0 false
  rw [mean_step_witness] at h
  
  have hrhs : Lindeberg.cov muU fAvg (coord false)
      * mean muU (fun ω => freshAt Tw ω 0 false) = 1 / 8 := by
    rw [cov_fAvg]
    have hfresh : mean muU (fun ω => freshAt Tw ω 0 false) = 1 := by
      unfold mean
      rw [show (fun ω => (fun ω => freshAt Tw ω 0 false) ω * muU ω)
            = (fun ω => (1:ℝ) * muU ω) from by funext ω; simp only []; rw [freshAt_Tw_zero]]
      rw [← Finset.mul_sum, muU_sum_one, mul_one]
    rw [hfresh, mul_one]
  rw [hrhs] at h
  norm_num at h

end Counterexample

end StepCov

end OSSS

end StatMech
