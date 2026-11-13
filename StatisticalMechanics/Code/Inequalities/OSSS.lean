/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























import Code.Foundations.ProductMeasure
import Code.Inequalities.Pivotal

open scoped BigOperators
open Finset

set_option linter.style.longLine false

namespace StatMech
namespace OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]








noncomputable def weight (ν : E → Bool → ℝ) (ω : ConfigSpace E) : ℝ := ∏ e, ν e (ω e)


noncomputable def expect (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, weight ν ω * g ω



structure IsProbWeight (ν : E → Bool → ℝ) : Prop where
  nonneg : ∀ e b, 0 ≤ ν e b
  normalized : ∀ e, ν e false + ν e true = 1


def pt (b : Bool) : Bool → ℝ := fun c => if c = b then 1 else 0

@[simp] lemma pt_self (b : Bool) : pt b b = 1 := by simp [pt]

lemma pt_apply (b c : Bool) : pt b c = if c = b then 1 else 0 := rfl





lemma weight_factor (ν : E → Bool → ℝ) (e : E) (ω : ConfigSpace E) :
    weight ν ω = ν e (ω e) * ∏ e' ∈ univ.erase e, ν e' (ω e') := by
  unfold weight
  rw [← Finset.prod_erase_mul univ _ (Finset.mem_univ e), mul_comm]



lemma restrict_update (ν : E → Bool → ℝ) (e : E) (ω : ConfigSpace E) (b : Bool) :
    (∏ e' ∈ univ.erase e, ν e' (Function.update ω e b e'))
      = ∏ e' ∈ univ.erase e, ν e' (ω e') := by
  apply Finset.prod_congr rfl
  intro e' he'
  rw [Function.update_of_ne (Finset.ne_of_mem_erase he')]


lemma weight_cond (ν : E → Bool → ℝ) (e : E) (b : Bool) (ω : ConfigSpace E) :
    weight (Function.update ν e (pt b)) ω
      = pt b (ω e) * ∏ e' ∈ univ.erase e, ν e' (ω e') := by
  rw [weight_factor (Function.update ν e (pt b)) e ω, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro e' he'
  rw [Function.update_of_ne (Finset.ne_of_mem_erase he')]





lemma expect_cond (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ) :
    expect ν g = ν e true * expect (Function.update ν e (pt true)) g
               + ν e false * expect (Function.update ν e (pt false)) g := by
  unfold expect
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  rw [weight_factor ν e ω, weight_cond ν e true ω, weight_cond ν e false ω]
  cases ω e <;>
    simp only [pt, Bool.false_eq_true, if_false, if_true, reduceCtorEq] <;> ring




lemma expect_add (ν : E → Bool → ℝ) (g h : ConfigSpace E → ℝ) :
    expect ν (fun ω => g ω + h ω) = expect ν g + expect ν h := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma expect_sub (ν : E → Bool → ℝ) (g h : ConfigSpace E → ℝ) :
    expect ν (fun ω => g ω - h ω) = expect ν g - expect ν h := by
  unfold expect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma expect_const_mul (ν : E → Bool → ℝ) (c : ℝ) (g : ConfigSpace E → ℝ) :
    expect ν (fun ω => c * g ω) = c * expect ν g := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)



lemma expect_mono {ν : E → Bool → ℝ} (hν : IsProbWeight ν) {g h : ConfigSpace E → ℝ}
    (hgh : ∀ ω, g ω ≤ h ω) : expect ν g ≤ expect ν h := by
  unfold expect
  apply Finset.sum_le_sum
  intro ω _
  have hw : 0 ≤ weight ν ω := Finset.prod_nonneg (fun e _ => hν.nonneg e (ω e))
  exact mul_le_mul_of_nonneg_left (hgh ω) hw


lemma expect_one {ν : E → Bool → ℝ} (hν : IsProbWeight ν) :
    expect ν (fun _ => 1) = 1 := by
  unfold expect
  simp only [mul_one]
  unfold weight
  
  rw [← Fintype.prod_sum]
  rw [Finset.prod_eq_one]
  intro e _
  rw [Fintype.sum_bool, add_comm]
  exact hν.normalized e




noncomputable def cov (ν : E → Bool → ℝ) (f g : ConfigSpace E → ℝ) : ℝ :=
  expect ν (fun ω => f ω * g ω) - expect ν f * expect ν g


noncomputable def var (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) : ℝ := cov ν g g



noncomputable def infl (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) (e : E) : ℝ :=
  expect ν (fun ω => |g (setOpen e ω) - g (setClosed e ω)|)




noncomputable def condMean (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ) :
    ConfigSpace E → ℝ :=
  fun ω => ν e true * g (setOpen e ω) + ν e false * g (setClosed e ω)

omit [Fintype E] in

lemma condMean_setOpen (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    condMean ν e g (setOpen e ω) = condMean ν e g ω := by
  unfold condMean
  rw [setOpen_setOpen, setClosed_setOpen]

omit [Fintype E] in

lemma condMean_setClosed (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    condMean ν e g (setClosed e ω) = condMean ν e g ω := by
  unfold condMean
  rw [setOpen_setClosed, setClosed_setClosed]

omit [Fintype E] in

lemma condMean_eq (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    condMean ν e g ω = ν e true * g (setOpen e ω) + ν e false * g (setClosed e ω) := rfl






inductive DecisionTree (E : Type*) where
  | leaf : Bool → DecisionTree E
  | node : E → DecisionTree E → DecisionTree E → DecisionTree E

namespace DecisionTree


def eval : DecisionTree E → ConfigSpace E → Bool
  | leaf b, _ => b
  | node e t f, ω => if ω e then eval t ω else eval f ω


def queried : DecisionTree E → ConfigSpace E → Finset E
  | leaf _, _ => ∅
  | node e t f, ω => insert e (if ω e then queried t ω else queried f ω)


noncomputable def evalR (T : DecisionTree E) (ω : ConfigSpace E) : ℝ :=
  if T.eval ω then 1 else 0

omit [Fintype E] [DecidableEq E] in

lemma evalR_le_one (T : DecisionTree E) (ω : ConfigSpace E) : T.evalR ω ≤ 1 := by
  unfold evalR; split <;> norm_num

omit [Fintype E] [DecidableEq E] in

lemma evalR_nonneg (T : DecisionTree E) (ω : ConfigSpace E) : 0 ≤ T.evalR ω := by
  unfold evalR; split <;> norm_num

omit [Fintype E] in


lemma abs_evalR_diff_le_one (T : DecisionTree E) (e : E) (ω : ConfigSpace E) :
    |T.evalR (setOpen e ω) - T.evalR (setClosed e ω)| ≤ 1 := by
  have h1 := evalR_le_one T (setOpen e ω)
  have h2 := evalR_nonneg T (setOpen e ω)
  have h3 := evalR_le_one T (setClosed e ω)
  have h4 := evalR_nonneg T (setClosed e ω)
  rw [abs_le]; constructor <;> linarith

end DecisionTree



noncomputable def reveal (ν : E → Bool → ℝ) (T : DecisionTree E) (e : E) : ℝ :=
  expect ν (fun ω => if e ∈ T.queried ω then (1 : ℝ) else 0)

open DecisionTree

lemma expect_cond_forces (ν : E → Bool → ℝ) (e : E) (b : Bool) (h : ConfigSpace E → ℝ) :
    expect (Function.update ν e (pt b)) h
      = expect (Function.update ν e (pt b)) (fun ω => h (Function.update ω e b)) := by
  unfold expect
  apply Finset.sum_congr rfl
  intro ω _
  rw [weight_cond ν e b ω]
  simp only []
  by_cases hb : ω e = b
  · have : Function.update ω e b = ω := by
      funext e'
      by_cases he : e' = e
      · subst he; simp [hb]
      · rw [Function.update_of_ne he]
    rw [this]
  · have h0 : pt b (ω e) = 0 := by simp [pt, hb]
    rw [h0]; ring

lemma reveal_root (hν : IsProbWeight ν) (e : E) (t f : DecisionTree E) :
    reveal ν (.node e t f) e = 1 := by
  unfold reveal
  have : (fun ω => if e ∈ (DecisionTree.node e t f).queried ω then (1:ℝ) else 0)
       = (fun _ => (1:ℝ)) := by
    funext ω
    rw [if_pos]; unfold DecisionTree.queried; exact Finset.mem_insert_self e _
  rw [this, expect_one hν]

omit [Fintype E] in
lemma mem_queried_node_iff (e i : E) (hi : i ≠ e) (t f : DecisionTree E)
    (ω : ConfigSpace E) (b : Bool) (h : ω e = b) :
    (i ∈ (DecisionTree.node e t f).queried ω) ↔ (i ∈ (if b then t else f).queried ω) := by
  conv_lhs => unfold DecisionTree.queried
  rw [h, Finset.mem_insert]
  cases b <;> simp [hi]

lemma expect_indQ_node_cond (ν : E → Bool → ℝ) (e i : E) (hi : i ≠ e) (b : Bool)
    (t f : DecisionTree E) :
    expect (Function.update ν e (pt b))
        (fun ω => if i ∈ (DecisionTree.node e t f).queried ω then (1:ℝ) else 0)
      = expect (Function.update ν e (pt b))
        (fun ω => if i ∈ (if b then t else f).queried ω then (1:ℝ) else 0) := by
  rw [expect_cond_forces ν e b, expect_cond_forces ν e b
        (fun ω => if i ∈ (if b then t else f).queried ω then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  congr 1
  have hωe : (Function.update ω e b) e = b := Function.update_self e b ω
  exact if_congr (mem_queried_node_iff e i hi t f _ b hωe) rfl rfl

lemma reveal_node_ne (ν : E → Bool → ℝ) (e i : E) (hi : i ≠ e) (t f : DecisionTree E) :
    reveal ν (.node e t f) i
      = ν e true * reveal (Function.update ν e (pt true)) t i
      + ν e false * reveal (Function.update ν e (pt false)) f i := by
  unfold reveal
  rw [expect_cond ν e]
  rw [expect_indQ_node_cond ν e i hi true t f, expect_indQ_node_cond ν e i hi false t f]
  simp only [if_true, Bool.false_eq_true, if_false]


lemma infl_cond (ν : E → Bool → ℝ) (e : E) (h : ConfigSpace E → ℝ) (i : E) :
    infl ν h i = ν e true * infl (Function.update ν e (pt true)) h i
               + ν e false * infl (Function.update ν e (pt false)) h i := by
  unfold infl
  exact expect_cond ν e _


lemma infl_condMean_self (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ) :
    infl ν (condMean ν e g) e = 0 := by
  unfold infl
  have : (fun ω => |condMean ν e g (setOpen e ω) - condMean ν e g (setClosed e ω)|)
       = (fun _ => (0:ℝ)) := by
    funext ω
    rw [condMean_setOpen, condMean_setClosed, sub_self, abs_zero]
  rw [this]
  unfold expect; simp


def flipAt (e : E) (ω : ConfigSpace E) : ConfigSpace E := Function.update ω e (!(ω e))

omit [Fintype E] in
lemma flipAt_involutive (e : E) : Function.Involutive (flipAt e) := by
  intro ω; funext e'; unfold flipAt
  by_cases h : e' = e
  · subst h; simp
  · simp [Function.update_of_ne h]

omit [Fintype E] in
lemma flipAt_eval (e : E) (ω : ConfigSpace E) : flipAt e ω e = !(ω e) := by
  unfold flipAt; simp

omit [Fintype E] in
lemma flipAt_eval_ne (e e' : E) (he : e' ≠ e) (ω : ConfigSpace E) : flipAt e ω e' = ω e' := by
  unfold flipAt; rw [Function.update_of_ne he]

omit [Fintype E] in
lemma pt_not (b c : Bool) : pt b (!c) = pt (!b) c := by
  unfold pt; cases b <;> cases c <;> simp


lemma expect_cond_indep_flip (ν : E → Bool → ℝ) (e : E) (b : Bool) (k : ConfigSpace E → ℝ)
    (hk : ∀ ω, k (flipAt e ω) = k ω) :
    expect (Function.update ν e (pt b)) k = expect (Function.update ν e (pt (!b))) k := by
  unfold expect
  have hbij := Fintype.sum_bijective (flipAt e) (flipAt_involutive e).bijective
        (fun ω => weight (Function.update ν e (pt (!b))) (flipAt e ω) * k (flipAt e ω))
        (fun ω => weight (Function.update ν e (pt (!b))) ω * k ω)
        (fun ω => rfl)
  rw [← hbij]
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  rw [weight_cond ν e b ω, weight_cond ν e (!b) (flipAt e ω), hk]
  congr 1
  congr 1
  · rw [flipAt_eval, pt_not, Bool.not_not]
  · apply Finset.prod_congr rfl
    intro e' he'
    rw [flipAt_eval_ne e e' (Finset.ne_of_mem_erase he')]


omit [Fintype E] in
lemma setOpen_flipAt (e : E) (ω : ConfigSpace E) : setOpen e (flipAt e ω) = setOpen e ω := by
  unfold setOpen flipAt; rw [Function.update_idem]

omit [Fintype E] in
lemma setClosed_flipAt (e : E) (ω : ConfigSpace E) : setClosed e (flipAt e ω) = setClosed e ω := by
  unfold setClosed flipAt; rw [Function.update_idem]


lemma expect_condT_setOpen (ν : E → Bool → ℝ) (e : E) (h : ConfigSpace E → ℝ) :
    expect (Function.update ν e (pt true)) (fun ω => h (setOpen e ω))
      = expect (Function.update ν e (pt true)) h := by
  rw [expect_cond_forces ν e true (fun ω => h (setOpen e ω)),
      expect_cond_forces ν e true h]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [setOpen, Function.update_idem]

lemma expect_setOpen (hν : IsProbWeight ν) (e : E) (h : ConfigSpace E → ℝ) :
    expect ν (fun ω => h (setOpen e ω)) = expect (Function.update ν e (pt true)) h := by
  rw [expect_cond ν e (fun ω => h (setOpen e ω))]
  have hflip : expect (Function.update ν e (pt false)) (fun ω => h (setOpen e ω))
        = expect (Function.update ν e (pt true)) (fun ω => h (setOpen e ω)) := by
    have h2 := expect_cond_indep_flip ν e false (fun ω => h (setOpen e ω))
      (fun ω => by simp only [setOpen_flipAt])
    rw [h2]; norm_num
  rw [hflip, expect_condT_setOpen]
  have hsum : ν e false + ν e true = 1 := hν.normalized e
  have : ν e true * expect (Function.update ν e (pt true)) h
       + ν e false * expect (Function.update ν e (pt true)) h
       = (ν e true + ν e false) * expect (Function.update ν e (pt true)) h := by ring
  rw [this, add_comm (ν e true) (ν e false), hsum, one_mul]

lemma expect_condF_setClosed (ν : E → Bool → ℝ) (e : E) (h : ConfigSpace E → ℝ) :
    expect (Function.update ν e (pt false)) (fun ω => h (setClosed e ω))
      = expect (Function.update ν e (pt false)) h := by
  rw [expect_cond_forces ν e false (fun ω => h (setClosed e ω)),
      expect_cond_forces ν e false h]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [setClosed, Function.update_idem]

lemma expect_setClosed (hν : IsProbWeight ν) (e : E) (h : ConfigSpace E → ℝ) :
    expect ν (fun ω => h (setClosed e ω)) = expect (Function.update ν e (pt false)) h := by
  rw [expect_cond ν e (fun ω => h (setClosed e ω))]
  have hflip : expect (Function.update ν e (pt true)) (fun ω => h (setClosed e ω))
        = expect (Function.update ν e (pt false)) (fun ω => h (setClosed e ω)) := by
    have h2 := expect_cond_indep_flip ν e true (fun ω => h (setClosed e ω))
      (fun ω => by simp only [setClosed_flipAt])
    rw [h2]; norm_num
  rw [hflip, expect_condF_setClosed]
  have hsum : ν e false + ν e true = 1 := hν.normalized e
  have : ν e true * expect (Function.update ν e (pt false)) h
       + ν e false * expect (Function.update ν e (pt false)) h
       = (ν e true + ν e false) * expect (Function.update ν e (pt false)) h := by ring
  rw [this, add_comm (ν e true) (ν e false), hsum, one_mul]


omit [Fintype E] in
lemma setOpen_comm {e i : E} (h : i ≠ e) (ω : ConfigSpace E) :
    setOpen e (setOpen i ω) = setOpen i (setOpen e ω) := by
  unfold setOpen; rw [Function.update_comm h]

omit [Fintype E] in
lemma setClosed_setOpen_comm {e i : E} (h : i ≠ e) (ω : ConfigSpace E) :
    setClosed e (setOpen i ω) = setOpen i (setClosed e ω) := by
  unfold setClosed setOpen; rw [Function.update_comm h]

omit [Fintype E] in
lemma setOpen_setClosed_comm {e i : E} (h : i ≠ e) (ω : ConfigSpace E) :
    setOpen e (setClosed i ω) = setClosed i (setOpen e ω) := by
  unfold setOpen setClosed; rw [Function.update_comm h]

omit [Fintype E] in
lemma setClosed_comm {e i : E} (h : i ≠ e) (ω : ConfigSpace E) :
    setClosed e (setClosed i ω) = setClosed i (setClosed e ω) := by
  unfold setClosed; rw [Function.update_comm h]


lemma infl_eq_expect_H (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) (i : E) :
    infl ν g i = expect ν (fun ω => |g (setOpen i ω) - g (setClosed i ω)|) := rfl


lemma infl_condMean_le (hν : IsProbWeight ν) (e i : E) (hi : i ≠ e) (g : ConfigSpace E → ℝ) :
    infl ν (condMean ν e g) i ≤ infl ν g i := by
  set H : ConfigSpace E → ℝ := fun ω => |g (setOpen i ω) - g (setClosed i ω)| with hH
  
  have step : infl ν (condMean ν e g) i
      ≤ ν e true * expect ν (fun ω => H (setOpen e ω))
      + ν e false * expect ν (fun ω => H (setClosed e ω)) := by
    rw [infl_eq_expect_H]
    rw [← expect_const_mul ν (ν e true), ← expect_const_mul ν (ν e false), ← expect_add]
    apply expect_mono hν
    intro ω
    
    unfold condMean
    have e1 : setOpen e (setOpen i ω) = setOpen i (setOpen e ω) := setOpen_comm hi ω
    have e2 : setClosed e (setOpen i ω) = setOpen i (setClosed e ω) := setClosed_setOpen_comm hi ω
    have e3 : setOpen e (setClosed i ω) = setClosed i (setOpen e ω) := setOpen_setClosed_comm hi ω
    have e4 : setClosed e (setClosed i ω) = setClosed i (setClosed e ω) := setClosed_comm hi ω
    rw [e1, e2, e3, e4]
    
    
    have hreorg : ν e true * g (setOpen i (setOpen e ω)) + ν e false * g (setOpen i (setClosed e ω))
        - (ν e true * g (setClosed i (setOpen e ω)) + ν e false * g (setClosed i (setClosed e ω)))
        = ν e true * (g (setOpen i (setOpen e ω)) - g (setClosed i (setOpen e ω)))
        + ν e false * (g (setOpen i (setClosed e ω)) - g (setClosed i (setClosed e ω))) := by ring
    rw [hreorg]
    have habs := abs_add_le (ν e true * (g (setOpen i (setOpen e ω)) - g (setClosed i (setOpen e ω))))
                         (ν e false * (g (setOpen i (setClosed e ω)) - g (setClosed i (setClosed e ω))))
    refine le_trans habs ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hν.nonneg e true), abs_of_nonneg (hν.nonneg e false)]
  
  rw [expect_setOpen hν e H, expect_setClosed hν e H] at step
  
  rw [infl_cond ν e g i] at *
  
  have hT : infl (Function.update ν e (pt true)) g i = expect (Function.update ν e (pt true)) H := rfl
  have hF : infl (Function.update ν e (pt false)) g i = expect (Function.update ν e (pt false)) H := rfl
  rw [hT, hF]
  exact step


lemma expect_cond_eq_of_indep (hν : IsProbWeight ν) (e : E) (b : Bool) (k : ConfigSpace E → ℝ)
    (hk : ∀ ω, k (flipAt e ω) = k ω) :
    expect (Function.update ν e (pt b)) k = expect ν k := by
  rw [expect_cond ν e k]
  have hflip : expect (Function.update ν e (pt false)) k = expect (Function.update ν e (pt true)) k := by
    have := expect_cond_indep_flip ν e false k hk
    rw [this]; norm_num
  have hflip2 : expect (Function.update ν e (pt true)) k = expect (Function.update ν e (pt b)) k := by
    cases b with
    | true => rfl
    | false => exact hflip.symm
  rw [hflip, ← hflip2]
  have hsum : ν e false + ν e true = 1 := hν.normalized e
  have : ν e true * expect (Function.update ν e (pt true)) k
       + ν e false * expect (Function.update ν e (pt true)) k
       = (ν e true + ν e false) * expect (Function.update ν e (pt true)) k := by ring
  rw [this, add_comm (ν e true) (ν e false), hsum, one_mul]

lemma expect_condMean (hν : IsProbWeight ν) (e : E) (g : ConfigSpace E → ℝ) :
    expect ν (condMean ν e g) = expect ν g := by
  have h1 : expect ν (condMean ν e g)
      = expect ν (fun ω => ν e true * g (setOpen e ω))
      + expect ν (fun ω => ν e false * g (setClosed e ω)) := by
    rw [← expect_add ν (fun ω => ν e true * g (setOpen e ω))
          (fun ω => ν e false * g (setClosed e ω))]
    rfl
  rw [h1, expect_const_mul ν (ν e true) (fun ω => g (setOpen e ω)),
      expect_const_mul ν (ν e false) (fun ω => g (setClosed e ω)),
      expect_setOpen hν, expect_setClosed hν, ← expect_cond ν e g]


omit [Fintype E] in
lemma diff_flip (e : E) (g : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    (g (setOpen e (flipAt e ω)) - g (setClosed e (flipAt e ω)))
      = g (setOpen e ω) - g (setClosed e ω) := by
  rw [setOpen_flipAt, setClosed_flipAt]


lemma expect_fluct_condT (hν : IsProbWeight ν) (e : E) (F g : ConfigSpace E → ℝ) :
    expect (Function.update ν e (pt true)) (fun ω => F ω * (g ω - condMean ν e g ω))
      = ν e false * expect ν (fun ω =>
          F (setOpen e ω) * (g (setOpen e ω) - g (setClosed e ω))) := by
  rw [expect_cond_forces ν e true (fun ω => F ω * (g ω - condMean ν e g ω))]
  
  have hint : ∀ ω : ConfigSpace E,
      F (Function.update ω e true) * (g (Function.update ω e true)
        - condMean ν e g (Function.update ω e true))
      = ν e false * (F (setOpen e ω) * (g (setOpen e ω) - g (setClosed e ω))) := by
    intro ω
    have hO : Function.update ω e true = setOpen e ω := rfl
    rw [hO]
    have hcm : condMean ν e g (setOpen e ω) = condMean ν e g ω := condMean_setOpen ν e g ω
    rw [hcm]
    unfold condMean
    have hsum : ν e false + ν e true = 1 := hν.normalized e
    have hnt : ν e true = 1 - ν e false := by linarith
    rw [hnt]; ring
  have heq : (fun ω => F (Function.update ω e true) * (g (Function.update ω e true)
        - condMean ν e g (Function.update ω e true)))
      = (fun ω => ν e false * (F (setOpen e ω) * (g (setOpen e ω) - g (setClosed e ω)))) := by
    funext ω; exact hint ω
  rw [heq]
  rw [expect_const_mul (Function.update ν e (pt true)) (ν e false)
        (fun ω => F (setOpen e ω) * (g (setOpen e ω) - g (setClosed e ω)))]
  congr 1
  exact expect_cond_eq_of_indep hν e true _
    (fun ω => by simp only [setOpen_flipAt, setClosed_flipAt])

lemma expect_fluct_condF (hν : IsProbWeight ν) (e : E) (F g : ConfigSpace E → ℝ) :
    expect (Function.update ν e (pt false)) (fun ω => F ω * (g ω - condMean ν e g ω))
      = (- ν e true) * expect ν (fun ω =>
          F (setClosed e ω) * (g (setOpen e ω) - g (setClosed e ω))) := by
  rw [expect_cond_forces ν e false (fun ω => F ω * (g ω - condMean ν e g ω))]
  have hint : ∀ ω : ConfigSpace E,
      F (Function.update ω e false) * (g (Function.update ω e false)
        - condMean ν e g (Function.update ω e false))
      = (- ν e true) * (F (setClosed e ω) * (g (setOpen e ω) - g (setClosed e ω))) := by
    intro ω
    have hC : Function.update ω e false = setClosed e ω := rfl
    rw [hC]
    have hcm : condMean ν e g (setClosed e ω) = condMean ν e g ω := condMean_setClosed ν e g ω
    rw [hcm]
    unfold condMean
    have hsum : ν e false + ν e true = 1 := hν.normalized e
    have hnf : ν e false = 1 - ν e true := by linarith
    rw [hnf]; ring
  have heq : (fun ω => F (Function.update ω e false) * (g (Function.update ω e false)
        - condMean ν e g (Function.update ω e false)))
      = (fun ω => (- ν e true) * (F (setClosed e ω) * (g (setOpen e ω) - g (setClosed e ω)))) := by
    funext ω; exact hint ω
  rw [heq]
  rw [expect_const_mul (Function.update ν e (pt false)) (- ν e true)
        (fun ω => F (setClosed e ω) * (g (setOpen e ω) - g (setClosed e ω)))]
  congr 1
  exact expect_cond_eq_of_indep hν e false _
    (fun ω => by simp only [setOpen_flipAt, setClosed_flipAt])

lemma expect_fluctuation (hν : IsProbWeight ν) (e : E) (F g : ConfigSpace E → ℝ) :
    expect ν (fun ω => F ω * (g ω - condMean ν e g ω))
      = ν e true * ν e false
        * expect ν (fun ω =>
            (F (setOpen e ω) - F (setClosed e ω))
            * (g (setOpen e ω) - g (setClosed e ω))) := by
  rw [expect_cond ν e (fun ω => F ω * (g ω - condMean ν e g ω))]
  rw [expect_fluct_condT hν e F g, expect_fluct_condF hν e F g]
  have hsplit : expect ν (fun ω =>
        (F (setOpen e ω) - F (setClosed e ω)) * (g (setOpen e ω) - g (setClosed e ω)))
      = expect ν (fun ω => F (setOpen e ω) * (g (setOpen e ω) - g (setClosed e ω)))
      - expect ν (fun ω => F (setClosed e ω) * (g (setOpen e ω) - g (setClosed e ω))) := by
    rw [← expect_sub]
    apply Finset.sum_congr rfl
    intro ω _; ring
  rw [hsplit]; ring


lemma expect_zero (ν : E → Bool → ℝ) : expect ν (fun _ => 0) = 0 := by
  unfold expect; simp

lemma infl_nonneg (hν : IsProbWeight ν) (g : ConfigSpace E → ℝ) (i : E) : 0 ≤ infl ν g i := by
  unfold infl
  rw [← expect_zero ν]
  apply expect_mono hν
  intro ω; exact abs_nonneg _


lemma claimA (hν : IsProbWeight ν) (e : E) (F g : ConfigSpace E → ℝ)
    (hF : ∀ ω, |F (setOpen e ω) - F (setClosed e ω)| ≤ 1) :
    cov ν F (fun ω => g ω - condMean ν e g ω) ≤ infl ν g e := by
  unfold cov
  
  have hzero : expect ν (fun ω => g ω - condMean ν e g ω) = 0 := by
    rw [expect_sub, expect_condMean hν, sub_self]
  rw [hzero, mul_zero, sub_zero]
  
  rw [expect_fluctuation hν e F g]
  
  have hTF : 0 ≤ ν e true := hν.nonneg e true
  have hFF : 0 ≤ ν e false := hν.nonneg e false
  have hprod : 0 ≤ ν e true * ν e false := mul_nonneg hTF hFF
  
  have hle1 : ν e true * ν e false ≤ 1 := by
    have h1 : ν e true ≤ 1 := by have := hν.normalized e; linarith
    have h2 : ν e false ≤ 1 := by have := hν.normalized e; linarith
    nlinarith [mul_nonneg hTF hFF]
  calc ν e true * ν e false
          * expect ν (fun ω => (F (setOpen e ω) - F (setClosed e ω)) * (g (setOpen e ω) - g (setClosed e ω)))
      ≤ ν e true * ν e false
          * expect ν (fun ω => |g (setOpen e ω) - g (setClosed e ω)|) := by
        apply mul_le_mul_of_nonneg_left _ hprod
        apply expect_mono hν
        intro ω
        calc (F (setOpen e ω) - F (setClosed e ω)) * (g (setOpen e ω) - g (setClosed e ω))
            ≤ |(F (setOpen e ω) - F (setClosed e ω)) * (g (setOpen e ω) - g (setClosed e ω))| := le_abs_self _
          _ = |F (setOpen e ω) - F (setClosed e ω)| * |g (setOpen e ω) - g (setClosed e ω)| := abs_mul _ _
          _ ≤ 1 * |g (setOpen e ω) - g (setClosed e ω)| := by
                apply mul_le_mul_of_nonneg_right (hF ω) (abs_nonneg _)
          _ = |g (setOpen e ω) - g (setClosed e ω)| := one_mul _
    _ = ν e true * ν e false * infl ν g e := rfl
    _ ≤ 1 * infl ν g e := by
        apply mul_le_mul_of_nonneg_right hle1 (infl_nonneg hν g e)
    _ = infl ν g e := one_mul _


lemma cov_add_right (ν : E → Bool → ℝ) (F g h : ConfigSpace E → ℝ) :
    cov ν F (fun ω => g ω + h ω) = cov ν F g + cov ν F h := by
  unfold cov
  have h1 : expect ν (fun ω => F ω * (g ω + h ω))
      = expect ν (fun ω => F ω * g ω) + expect ν (fun ω => F ω * h ω) := by
    rw [← expect_add]; apply Finset.sum_congr rfl; intro ω _; ring
  rw [h1, expect_add]; ring


lemma cov_decomp (ν : E → Bool → ℝ) (e : E) (F g : ConfigSpace E → ℝ) :
    cov ν F g = cov ν F (fun ω => g ω - condMean ν e g ω) + cov ν F (condMean ν e g) := by
  rw [← cov_add_right]
  congr 1
  funext ω; ring

omit [Fintype E] [DecidableEq E] in
lemma evalR_node_of_eq (e : E) (t f : DecisionTree E) (ω : ConfigSpace E) (b : Bool)
    (h : ω e = b) :
    (DecisionTree.node e t f).evalR ω = (if b then t else f).evalR ω := by
  unfold DecisionTree.evalR
  cases b with
  | true => simp only [DecisionTree.eval, h, if_true]
  | false => simp only [DecisionTree.eval, h, Bool.false_eq_true, if_false]


lemma expect_evalR_node_cond (ν : E → Bool → ℝ) (e : E) (b : Bool) (t f : DecisionTree E)
    (h : ConfigSpace E → ℝ) :
    expect (Function.update ν e (pt b)) (fun ω => (DecisionTree.node e t f).evalR ω * h ω)
      = expect (Function.update ν e (pt b)) (fun ω => (if b then t else f).evalR ω * h ω) := by
  rw [expect_cond_forces ν e b (fun ω => (DecisionTree.node e t f).evalR ω * h ω),
      expect_cond_forces ν e b (fun ω => (if b then t else f).evalR ω * h ω)]
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  have hωe : (Function.update ω e b) e = b := Function.update_self e b ω
  rw [evalR_node_of_eq e t f _ b hωe]


lemma claimB (hν : IsProbWeight ν) (e : E) (t f : DecisionTree E) (G : ConfigSpace E → ℝ)
    (hG : ∀ ω, G (flipAt e ω) = G ω) :
    cov ν (DecisionTree.node e t f).evalR G
      = ν e true * cov (Function.update ν e (pt true)) t.evalR G
      + ν e false * cov (Function.update ν e (pt false)) f.evalR G := by
  unfold cov
  
  have hprodexp : expect ν (fun ω => (DecisionTree.node e t f).evalR ω * G ω)
      = ν e true * expect (Function.update ν e (pt true)) (fun ω => t.evalR ω * G ω)
      + ν e false * expect (Function.update ν e (pt false)) (fun ω => f.evalR ω * G ω) := by
    rw [expect_cond ν e (fun ω => (DecisionTree.node e t f).evalR ω * G ω)]
    rw [expect_evalR_node_cond ν e true t f G, expect_evalR_node_cond ν e false t f G]
    simp only [if_true, Bool.false_eq_true, if_false]
  
  have hFexp : expect ν (DecisionTree.node e t f).evalR
      = ν e true * expect (Function.update ν e (pt true)) t.evalR
      + ν e false * expect (Function.update ν e (pt false)) f.evalR := by
    have h0 : expect ν (DecisionTree.node e t f).evalR
        = expect ν (fun ω => (DecisionTree.node e t f).evalR ω * (fun _ => (1:ℝ)) ω) := by
      apply Finset.sum_congr rfl; intro ω _; simp
    rw [h0, expect_cond ν e]
    rw [expect_evalR_node_cond ν e true t f (fun _ => 1), expect_evalR_node_cond ν e false t f (fun _ => 1)]
    simp only [if_true, Bool.false_eq_true, if_false, mul_one]
  
  have hGT : expect (Function.update ν e (pt true)) G = expect ν G :=
    expect_cond_eq_of_indep hν e true G hG
  have hGF : expect (Function.update ν e (pt false)) G = expect ν G :=
    expect_cond_eq_of_indep hν e false G hG
  rw [hprodexp, hFexp, hGT, hGF]
  ring

omit [Fintype E] in

lemma condMean_flipAt (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    condMean ν e g (flipAt e ω) = condMean ν e g ω := by
  unfold condMean
  rw [setOpen_flipAt, setClosed_flipAt]


lemma infl_condMean_cond_eq (hν : IsProbWeight ν) (e i : E) (hi : i ≠ e) (b : Bool)
    (g : ConfigSpace E → ℝ) :
    infl (Function.update ν e (pt b)) (condMean ν e g) i = infl ν (condMean ν e g) i := by
  unfold infl
  apply expect_cond_eq_of_indep hν e b
  intro ω
  
  have hei : e ≠ i := Ne.symm hi
  have h1 : setOpen i (flipAt e ω) = flipAt e (setOpen i ω) := by
    unfold setOpen flipAt
    rw [Function.update_comm hi, Function.update_of_ne hei]
  have h2 : setClosed i (flipAt e ω) = flipAt e (setClosed i ω) := by
    unfold setClosed flipAt
    rw [Function.update_comm hi, Function.update_of_ne hei]
  rw [h1, h2, condMean_flipAt, condMean_flipAt]

lemma expect_nonneg (hν : IsProbWeight ν) {g : ConfigSpace E → ℝ} (hg : ∀ ω, 0 ≤ g ω) :
    0 ≤ expect ν g := by
  rw [← expect_zero ν]; exact expect_mono hν hg

lemma reveal_nonneg (hν : IsProbWeight ν) (T : DecisionTree E) (i : E) : 0 ≤ reveal ν T i := by
  unfold reveal
  apply expect_nonneg hν
  intro ω; split <;> norm_num


omit [Fintype E] in
lemma isProbWeight_cond (hν : IsProbWeight ν) (e : E) (b : Bool) :
    IsProbWeight (Function.update ν e (pt b)) := by
  constructor
  · intro e' b'
    by_cases h : e' = e
    · subst h; rw [Function.update_self]; unfold pt; split <;> norm_num
    · rw [Function.update_of_ne h]; exact hν.nonneg e' b'
  · intro e'
    by_cases h : e' = e
    · subst h; rw [Function.update_self]; unfold pt; cases b <;> norm_num
    · rw [Function.update_of_ne h]; exact hν.normalized e'


lemma infl_condMean_self' (μ ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ) :
    infl μ (condMean ν e g) e = 0 := by
  unfold infl
  have : (fun ω => |condMean ν e g (setOpen e ω) - condMean ν e g (setClosed e ω)|)
       = (fun _ => (0:ℝ)) := by
    funext ω
    rw [condMean_setOpen, condMean_setClosed, sub_self, abs_zero]
  rw [this]
  unfold expect; simp


lemma recombine_term (hν : IsProbWeight ν) (e i : E) (t f : DecisionTree E)
    (g : ConfigSpace E → ℝ) :
    ν e true * (reveal (Function.update ν e (pt true)) t i
                  * infl (Function.update ν e (pt true)) (condMean ν e g) i)
    + ν e false * (reveal (Function.update ν e (pt false)) f i
                  * infl (Function.update ν e (pt false)) (condMean ν e g) i)
      = reveal ν (.node e t f) i * infl ν (condMean ν e g) i := by
  by_cases hi : i = e
  · subst hi
    rw [infl_condMean_self' (Function.update ν i (pt true)) ν i g,
        infl_condMean_self' (Function.update ν i (pt false)) ν i g,
        infl_condMean_self' ν ν i g]
    ring
  · rw [infl_condMean_cond_eq hν e i hi true g, infl_condMean_cond_eq hν e i hi false g,
        reveal_node_ne ν e i hi t f]
    ring


lemma recombine (hν : IsProbWeight ν) (e : E) (t f : DecisionTree E) (g : ConfigSpace E → ℝ) :
    ν e true * (∑ i, reveal (Function.update ν e (pt true)) t i
                      * infl (Function.update ν e (pt true)) (condMean ν e g) i)
    + ν e false * (∑ i, reveal (Function.update ν e (pt false)) f i
                      * infl (Function.update ν e (pt false)) (condMean ν e g) i)
      = ∑ i, reveal ν (.node e t f) i * infl ν (condMean ν e g) i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact recombine_term hν e i t f g


lemma cov_condMean_bound (hν : IsProbWeight ν) (e : E) (t f : DecisionTree E)
    (g : ConfigSpace E → ℝ)
    (IHt : ∀ μ, IsProbWeight μ → ∀ h : ConfigSpace E → ℝ,
        cov μ t.evalR h ≤ ∑ i, reveal μ t i * infl μ h i)
    (IHf : ∀ μ, IsProbWeight μ → ∀ h : ConfigSpace E → ℝ,
        cov μ f.evalR h ≤ ∑ i, reveal μ f i * infl μ h i) :
    cov ν (DecisionTree.node e t f).evalR (condMean ν e g)
      ≤ ∑ i, reveal ν (.node e t f) i * infl ν (condMean ν e g) i := by
  set G := condMean ν e g with hG
  have hGflip : ∀ ω, G (flipAt e ω) = G ω := condMean_flipAt ν e g
  rw [claimB hν e t f G hGflip]
  have hT := IHt (Function.update ν e (pt true)) (isProbWeight_cond hν e true) G
  have hF := IHf (Function.update ν e (pt false)) (isProbWeight_cond hν e false) G
  have hcomb : ν e true * cov (Function.update ν e (pt true)) t.evalR G
             + ν e false * cov (Function.update ν e (pt false)) f.evalR G
      ≤ ν e true * (∑ i, reveal (Function.update ν e (pt true)) t i
                        * infl (Function.update ν e (pt true)) G i)
      + ν e false * (∑ i, reveal (Function.update ν e (pt false)) f i
                        * infl (Function.update ν e (pt false)) G i) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hT (hν.nonneg e true)
    · exact mul_le_mul_of_nonneg_left hF (hν.nonneg e false)
  refine hcomb.trans ?_
  rw [recombine hν e t f g]


lemma reveal_infl_condMean_le (hν : IsProbWeight ν) (e i : E) (t f : DecisionTree E)
    (g : ConfigSpace E → ℝ) :
    reveal ν (.node e t f) i * infl ν (condMean ν e g) i
      ≤ reveal ν (.node e t f) i * infl ν g i := by
  apply mul_le_mul_of_nonneg_left _ (reveal_nonneg hν _ i)
  by_cases hi : i = e
  · subst hi
    rw [infl_condMean_self' ν ν i g]
    exact infl_nonneg hν g i
  · exact infl_condMean_le hν e i hi g

theorem osss_cov (T : DecisionTree E) :
    ∀ ν, IsProbWeight ν → ∀ g : ConfigSpace E → ℝ,
      cov ν T.evalR g ≤ ∑ i, reveal ν T i * infl ν g i := by
  induction T with
  | leaf b =>
    intro ν hν g
    
    have hconst : ∀ ω : ConfigSpace E, (DecisionTree.leaf b).evalR ω = (if b then (1:ℝ) else 0) := fun ω => rfl
    have hcov : cov ν (DecisionTree.leaf b).evalR g = 0 := by
      unfold cov
      have h1 : expect ν (fun ω => (DecisionTree.leaf b).evalR ω * g ω)
          = (if b then (1:ℝ) else 0) * expect ν g := by
        rw [← expect_const_mul ν (if b then (1:ℝ) else 0) g]
        apply Finset.sum_congr rfl; intro ω _; simp only []; rw [hconst ω]
      have h2 : expect ν (DecisionTree.leaf b).evalR = (if b then (1:ℝ) else 0) := by
        have : (DecisionTree.leaf b).evalR = (fun _ : ConfigSpace E => (if b then (1:ℝ) else 0)) := by
          funext ω; rw [hconst ω]
        rw [this]
        rw [show (fun _ : ConfigSpace E => (if b then (1:ℝ) else 0))
              = (fun ω => (if b then (1:ℝ) else 0) * (fun _ => (1:ℝ)) ω) from by funext; simp]
        rw [expect_const_mul, expect_one hν, mul_one]
      rw [h1, h2]; ring
    have hrev : ∀ i, reveal ν (DecisionTree.leaf b) i = 0 := by
      intro i
      unfold reveal
      have : (fun ω => if i ∈ (DecisionTree.leaf b).queried ω then (1:ℝ) else 0)
           = (fun _ => (0:ℝ)) := by
        funext ω
        rw [if_neg]
        unfold DecisionTree.queried
        exact Finset.notMem_empty i
      rw [this, expect_zero]
    rw [hcov]
    apply Finset.sum_nonneg
    intro i _
    rw [hrev i, zero_mul]
  | node e t f IHt IHf =>
    intro ν hν g
    
    rw [cov_decomp ν e (DecisionTree.node e t f).evalR g]
    
    have hA : cov ν (DecisionTree.node e t f).evalR (fun ω => g ω - condMean ν e g ω)
        ≤ infl ν g e := by
      apply claimA hν e (DecisionTree.node e t f).evalR g
      intro ω
      exact (DecisionTree.node e t f).abs_evalR_diff_le_one e ω
    
    have hB := cov_condMean_bound hν e t f g IHt IHf
    
    have hB2 : cov ν (DecisionTree.node e t f).evalR (condMean ν e g)
        ≤ ∑ i ∈ Finset.univ.erase e, reveal ν (.node e t f) i * infl ν g i := by
      refine hB.trans ?_
      
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ e)]
      have he0 : reveal ν (.node e t f) e * infl ν (condMean ν e g) e = 0 := by
        rw [infl_condMean_self' ν ν e g, mul_zero]
      rw [he0, zero_add]
      apply Finset.sum_le_sum
      intro i _
      exact reveal_infl_condMean_le hν e i t f g
    
    rw [← Finset.add_sum_erase Finset.univ
          (fun i => reveal ν (.node e t f) i * infl ν g i) (Finset.mem_univ e)]
    have hrev_e : reveal ν (.node e t f) e = 1 := reveal_root hν e t f
    rw [hrev_e, one_mul]
    exact add_le_add hA hB2






theorem osss_var (hν : IsProbWeight ν) (T : DecisionTree E) :
    var ν T.evalR ≤ ∑ i, reveal ν T i * infl ν T.evalR i :=
  osss_cov T ν hν T.evalR


theorem osss (hν : IsProbWeight ν) (T : DecisionTree E) (g : ConfigSpace E → ℝ) :
    cov ν T.evalR g ≤ ∑ i, reveal ν T i * infl ν g i :=
  osss_cov T ν hν g









noncomputable def bernoulliWeight (p : ℝ) : E → Bool → ℝ :=
  fun _ b => if b then p else 1 - p

omit [Fintype E] [DecidableEq E] in

lemma bernoulliWeight_isProbWeight {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbWeight (E := E) (bernoulliWeight p) := by
  constructor
  · intro e b; unfold bernoulliWeight; cases b <;> simp <;> linarith
  · intro e; unfold bernoulliWeight; simp


theorem osss_bernoulli {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T : DecisionTree E) (g : ConfigSpace E → ℝ) :
    cov (bernoulliWeight p) T.evalR g
      ≤ ∑ i, reveal (bernoulliWeight p) T i * infl (bernoulliWeight p) g i :=
  osss_cov T (bernoulliWeight p) (bernoulliWeight_isProbWeight hp0 hp1) g







omit [Fintype E] in


lemma abs_indicator_diff_eq_pivotal (A : Set (ConfigSpace E)) (e : E) (ω : ConfigSpace E) :
    |A.indicator (fun _ => (1:ℝ)) (setOpen e ω) - A.indicator (fun _ => (1:ℝ)) (setClosed e ω)|
      = {ω | IsPivotal e A ω}.indicator (fun _ => (1:ℝ)) ω := by
  by_cases hp : IsPivotal e A ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | IsPivotal e A ω} from hp)]
    unfold IsPivotal at hp
    by_cases hO : setOpen e ω ∈ A <;> by_cases hC : setClosed e ω ∈ A <;>
      simp_all [Set.indicator_of_mem, Set.indicator_of_notMem]
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | IsPivotal e A ω} from hp)]
    unfold IsPivotal at hp
    by_cases hO : setOpen e ω ∈ A <;> by_cases hC : setClosed e ω ∈ A <;>
      simp_all [Set.indicator_of_mem, Set.indicator_of_notMem]



theorem infl_indicator_eq_pivotal (ν : E → Bool → ℝ) (A : Set (ConfigSpace E)) (e : E) :
    infl ν (A.indicator (fun _ => (1:ℝ))) e
      = expect ν ({ω | IsPivotal e A ω}.indicator (fun _ => (1:ℝ))) := by
  unfold infl
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  rw [abs_indicator_diff_eq_pivotal]

end OSSS
end StatMech
