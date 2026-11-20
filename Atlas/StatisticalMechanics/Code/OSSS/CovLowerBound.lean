/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Code.OSSS.Poincare
import Code.Inequalities.IncreasingEvent

open scoped BigOperators
open Finset

set_option linter.style.longLine false

namespace StatMech
namespace OSSS.CovLowerBound

open StatMech.OSSS
open StatMech.OSSS.Poincare
open DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {ν : E → Bool → ℝ}






noncomputable def coordI (e : E) : ConfigSpace E → ℝ := fun ω => if ω e then (1 : ℝ) else 0

omit [Fintype E] in

lemma coordI_setOpen (e : E) (ω : ConfigSpace E) : coordI e (setOpen e ω) = 1 := by
  unfold coordI; rw [setOpen_self]; simp

omit [Fintype E] in

lemma coordI_setClosed (e : E) (ω : ConfigSpace E) : coordI e (setClosed e ω) = 0 := by
  unfold coordI; rw [setClosed_self]; simp

omit [Fintype E] [DecidableEq E] in


lemma coordI_eq_tree (e : E) :
    coordI e = (DecisionTree.node e (DecisionTree.leaf true) (DecisionTree.leaf false)).evalR := by
  funext ω
  unfold coordI DecisionTree.evalR
  simp only [DecisionTree.eval]
  by_cases h : ω e = true
  · simp [h]
  · simp [h]





lemma cov_const (hν : IsProbWeight ν) (c : ℝ) (G : ConfigSpace E → ℝ) :
    cov ν (fun _ => c) G = 0 := by
  unfold cov
  rw [show (fun ω => (fun _ : ConfigSpace E => c) ω * G ω) = (fun ω => c * G ω) from rfl,
      expect_const_mul]
  rw [show (fun _ : ConfigSpace E => c) = (fun ω => c * (fun _ => (1 : ℝ)) ω) from by funext; simp,
      expect_const_mul, expect_one hν, mul_one]
  ring


lemma cov_leaf (hν : IsProbWeight ν) (b : Bool) (G : ConfigSpace E → ℝ) :
    cov ν (DecisionTree.leaf b).evalR G = 0 := by
  have hc : (DecisionTree.leaf b).evalR = (fun _ : ConfigSpace E => (if b then (1 : ℝ) else 0)) := by
    funext ω; rfl
  rw [hc]; exact cov_const hν _ G


lemma cov_comm (ν : E → Bool → ℝ) (F G : ConfigSpace E → ℝ) : cov ν F G = cov ν G F := by
  unfold cov
  rw [mul_comm (expect ν F)]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _; ring






lemma cov_coordI_indep (hν : IsProbWeight ν) (e : E) (H : ConfigSpace E → ℝ)
    (hH : ∀ ω, H (flipAt e ω) = H ω) : cov ν (coordI e) H = 0 := by
  rw [coordI_eq_tree, claimB hν e (DecisionTree.leaf true) (DecisionTree.leaf false) H hH,
      cov_leaf (isProbWeight_cond hν e true) true H,
      cov_leaf (isProbWeight_cond hν e false) false H]
  ring













lemma cov_coordI (hν : IsProbWeight ν) (e : E) (g : ConfigSpace E → ℝ) :
    cov ν (coordI e) g
      = ν e true * ν e false * expect ν (fun ω => g (setOpen e ω) - g (setClosed e ω)) := by
  rw [cov_decomp ν e (coordI e) g,
      cov_coordI_indep hν e (condMean ν e g) (condMean_flipAt ν e g), add_zero]
  have hzero : expect ν (fun ω => g ω - condMean ν e g ω) = 0 := by
    rw [expect_sub, expect_condMean hν, sub_self]
  have hF : cov ν (coordI e) (fun ω => g ω - condMean ν e g ω)
      = expect ν (fun ω => (coordI e) ω * (g ω - condMean ν e g ω)) := by
    unfold cov; rw [hzero, mul_zero, sub_zero]
  rw [hF, expect_fluctuation hν e (coordI e) g]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  rw [coordI_setOpen, coordI_setClosed]; ring



lemma infl_mono {g : ConfigSpace E → ℝ} (hg : Monotone g) (ν : E → Bool → ℝ) (e : E) :
    infl ν g e = expect ν (fun ω => g (setOpen e ω) - g (setClosed e ω)) := by
  unfold infl
  congr 1
  funext ω
  have hle : g (setClosed e ω) ≤ g (setOpen e ω) := hg (setClosed_le_setOpen e ω)
  rw [abs_of_nonneg (by linarith)]










lemma cov_coordI_mono (hν : IsProbWeight ν) {g : ConfigSpace E → ℝ} (hg : Monotone g) (e : E) :
    cov ν (coordI e) g = ν e true * ν e false * infl ν g e := by
  rw [cov_coordI hν e g, infl_mono hg ν e]

omit [Fintype E] [DecidableEq E] in

lemma siteVar_nonneg (hν : IsProbWeight ν) (e : E) : 0 ≤ ν e true * ν e false :=
  mul_nonneg (hν.nonneg e true) (hν.nonneg e false)




lemma cov_coordI_nonneg (hν : IsProbWeight ν) {g : ConfigSpace E → ℝ} (hg : Monotone g) (e : E) :
    0 ≤ cov ν (coordI e) g := by
  rw [cov_coordI_mono hν hg e]
  exact mul_nonneg (siteVar_nonneg hν e) (infl_nonneg hν g e)























theorem cov_lower_bound {κ : Type*} [Fintype κ] [Nonempty κ]
    (hν : IsProbWeight ν) {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {f : ConfigSpace E → ℝ} (hf : f = A.indicator (fun _ => (1 : ℝ)))
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = f)
    (R : κ → E → ℝ) (hR : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D) (hD : ∀ e, (∑ k, R k e) ≤ D) :
    (Fintype.card κ : ℝ) * c₀ * var ν f ≤ D * ∑ e, cov ν (coordI e) f := by
  
  have hmono : Monotone f := by rw [hf]; exact hA.indicator_monotone
  have hinflnn : ∀ e, 0 ≤ infl ν f e := fun e => infl_nonneg hν f e
  
  have hvarbound : ∀ k, var ν f ≤ ∑ e, reveal ν (T k) e * infl ν f e := by
    intro k
    have h := osss_var hν (T k)
    rwa [hT k] at h
  
  have step1 : (Fintype.card κ : ℝ) * var ν f ≤ ∑ k, ∑ e, R k e * infl ν f e := by
    have hsum : ∑ _k : κ, var ν f ≤ ∑ k, ∑ e, R k e * infl ν f e := by
      apply Finset.sum_le_sum
      intro k _
      refine (hvarbound k).trans ?_
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_right (hR k e) (hinflnn e)
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  
  have step2 : ∑ k, ∑ e, R k e * infl ν f e = ∑ e, (∑ k, R k e) * infl ν f e := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _; rw [Finset.sum_mul]
  
  have step3 : ∑ e, (∑ k, R k e) * infl ν f e ≤ D * ∑ e, infl ν f e := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    exact mul_le_mul_of_nonneg_right (hD e) (hinflnn e)
  
  have hcomb : (Fintype.card κ : ℝ) * var ν f ≤ D * ∑ e, infl ν f e :=
    step1.trans (step2.le.trans step3)
  
  have hcov_ge : c₀ * ∑ e, infl ν f e ≤ ∑ e, cov ν (coordI e) f := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    rw [cov_coordI_mono hν hmono e]
    exact mul_le_mul_of_nonneg_right (hc₀ e) (hinflnn e)
  
  calc (Fintype.card κ : ℝ) * c₀ * var ν f
      = c₀ * ((Fintype.card κ : ℝ) * var ν f) := by ring
    _ ≤ c₀ * (D * ∑ e, infl ν f e) := mul_le_mul_of_nonneg_left hcomb hc₀nn
    _ = D * (c₀ * ∑ e, infl ν f e) := by ring
    _ ≤ D * ∑ e, cov ν (coordI e) f := mul_le_mul_of_nonneg_left hcov_ge hDnn






theorem cov_lower_bound_div {κ : Type*} [Fintype κ] [Nonempty κ]
    (hν : IsProbWeight ν) {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {f : ConfigSpace E → ℝ} (hf : f = A.indicator (fun _ => (1 : ℝ)))
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = f)
    (R : κ → E → ℝ) (hR : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ e, (∑ k, R k e) ≤ D) :
    ((Fintype.card κ : ℝ) * c₀ / D) * var ν f ≤ ∑ e, cov ν (coordI e) f := by
  have hmain := cov_lower_bound hν hA hf T hT R hR c₀ hc₀nn hc₀ D hDpos.le hD
  rw [div_mul_eq_mul_div, div_le_iff₀ hDpos]
  calc (Fintype.card κ : ℝ) * c₀ * var ν f ≤ D * ∑ e, cov ν (coordI e) f := hmain
    _ = (∑ e, cov ν (coordI e) f) * D := by ring









theorem cov_lower_bound_poincare
    (hν : IsProbWeight ν) {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    (φ : ConfigSpace E → Bool)
    (hφ : (fullTreeUniv φ).evalR = A.indicator (fun _ => (1 : ℝ)))
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false) :
    c₀ * var ν (A.indicator (fun _ => (1 : ℝ)))
      ≤ ∑ e, cov ν (coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
  
  have hmain := cov_lower_bound (κ := Unit) hν hA (f := A.indicator (fun _ => (1 : ℝ))) rfl
    (fun _ => fullTreeUniv φ) (fun _ => hφ)
    (fun _ _ => 1) (fun _ e => le_of_eq (reveal_fullTreeUniv hν φ e))
    c₀ hc₀nn hc₀ 1 (by norm_num) (fun e => by simp)
  simpa using hmain

end OSSS.CovLowerBound
end StatMech
