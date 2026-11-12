/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Code.Probability.PBiasedConvexity
import Code.Probability.KKLpBiased
import Code.Probability.RhoOptimiseClose2

open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]




def ptn_val (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem ptn_val_true : ptn_val true = 1 := rfl
@[simp] theorem ptn_val_false : ptn_val false = 0 := rfl


noncomputable def ptn_sigma (p : ℝ) : ℝ := Real.sqrt (p * (1 - p))

theorem ptn_sigma_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < ptn_sigma p :=
  Real.sqrt_pos.mpr (by nlinarith)

theorem ptn_sigma_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ptn_sigma p ^ 2 = p * (1 - p) := by
  unfold ptn_sigma; rw [Real.sq_sqrt (by nlinarith)]


noncomputable def ptn_psi (p : ℝ) (b : Bool) : ℝ := (ptn_val b - p) / ptn_sigma p


theorem ptn_psi_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (1 - p) * ptn_psi p false + p * ptn_psi p true = 0 := by
  unfold ptn_psi
  have hσ : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  simp only [ptn_val_false, ptn_val_true]
  field_simp
  ring



theorem ptn_psi_sq_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (1 - p) * ptn_psi p false ^ 2 + p * ptn_psi p true ^ 2 = 1 := by
  unfold ptn_psi
  have hσ2 : ptn_sigma p ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  simp only [ptn_val_false, ptn_val_true]
  rw [div_pow, div_pow]
  field_simp
  nlinarith [hσ2]









theorem ptn_expect_prod (p : ℝ) (h : ι → Bool → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => ∏ e : ι, h e (ω e))
      = ∏ e : ι, ((1 - p) * h e false + p * h e true) := by
  unfold OSSS.expect OSSS.weight OSSS.bernoulliWeight
  have hstep : ∀ ω : ConfigSpace ι,
      (∏ e : ι, (if ω e then p else 1 - p)) * ∏ e : ι, h e (ω e)
        = ∏ e : ι, ((if ω e then p else 1 - p) * h e (ω e)) := by
    intro ω; rw [← Finset.prod_mul_distrib]
  simp_rw [hstep]
  rw [← Fintype.prod_sum (fun (e : ι) (c : Bool) => (if c then p else 1 - p) * h e c)]
  apply Finset.prod_congr rfl
  intro e _
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  ring




noncomputable def ptn_pchar (p : ℝ) (S : Finset ι) (ω : ConfigSpace ι) : ℝ :=
  ∏ i ∈ S, ptn_psi p (ω i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem ptn_pchar_empty (p : ℝ) (ω : ConfigSpace ι) :
    ptn_pchar p (∅ : Finset ι) ω = 1 := by simp [ptn_pchar]


theorem ptn_pchar_as_univ (p : ℝ) (S : Finset ι) (ω : ConfigSpace ι) :
    ptn_pchar p S ω = ∏ i : ι, (if i ∈ S then ptn_psi p (ω i) else 1) := by
  unfold ptn_pchar; rw [Finset.prod_ite_mem, Finset.univ_inter]





theorem ptn_orthonormal {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (S T : Finset ι) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => ptn_pchar p S ω * ptn_pchar p T ω)
      = if S = T then 1 else 0 := by
  have hmean := ptn_psi_mean hp0 hp1
  have hsq := ptn_psi_sq_mean hp0 hp1
  
  have hprod : (fun ω : ConfigSpace ι => ptn_pchar p S ω * ptn_pchar p T ω)
      = (fun ω => ∏ e : ι,
          ((if e ∈ S then ptn_psi p (ω e) else 1) * (if e ∈ T then ptn_psi p (ω e) else 1))) := by
    funext ω
    rw [ptn_pchar_as_univ, ptn_pchar_as_univ, ← Finset.prod_mul_distrib]
  rw [hprod]
  rw [ptn_expect_prod p (fun e b => (if e ∈ S then ptn_psi p b else 1) * (if e ∈ T then ptn_psi p b else 1))]
  
  have hfac : ∀ e : ι,
      (1 - p) * ((if e ∈ S then ptn_psi p false else 1) * (if e ∈ T then ptn_psi p false else 1))
        + p * ((if e ∈ S then ptn_psi p true else 1) * (if e ∈ T then ptn_psi p true else 1))
        = if e ∈ S ↔ e ∈ T then 1 else 0 := by
    intro e
    by_cases hS : e ∈ S <;> by_cases hT : e ∈ T <;>
      simp only [hS, hT, if_true, if_false, one_mul, mul_one, iff_true, iff_false,
        iff_self, not_true_eq_false]
    · 
      nlinarith [hsq]
    · 
      linarith [hmean]
    · 
      linarith [hmean]
    · 
      ring
  simp_rw [hfac]
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro e _; rw [if_pos Iff.rfl]
  · rw [if_neg hST]
    
    have : ∃ e : ι, ¬ (e ∈ S ↔ e ∈ T) := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hST (Finset.ext (fun e => h e))
    obtain ⟨e, he⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by rw [if_neg he])




noncomputable def ptn_coeff (p : ℝ) (f : ConfigSpace ι → ℝ) (S : Finset ι) : ℝ :=
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => f ω * ptn_pchar p S ω)


theorem ptn_coeff_empty (p : ℝ) (f : ConfigSpace ι → ℝ) :
    ptn_coeff p f ∅ = OSSS.expect (OSSS.bernoulliWeight p) f := by
  unfold ptn_coeff; congr 1; funext ω; rw [ptn_pchar_empty, mul_one]

omit [DecidableEq ι] in


theorem ptn_repro_kernel {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x y : ConfigSpace ι) :
    (∑ S : Finset ι, ptn_pchar p S x * ptn_pchar p S y)
      = if x = y then 1 / OSSS.weight (OSSS.bernoulliWeight p) x else 0 := by
  have hσ2 : ptn_sigma p ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  have hpt : ∀ S : Finset ι, ptn_pchar p S x * ptn_pchar p S y
      = ∏ i ∈ S, (ptn_psi p (x i) * ptn_psi p (y i)) := by
    intro S; unfold ptn_pchar; rw [← Finset.prod_mul_distrib]
  simp_rw [hpt]
  have hpow : (univ : Finset (Finset ι)) = (univ : Finset ι).powerset := by ext S; simp
  rw [hpow, ← Finset.prod_one_add]
  have h1p : (0:ℝ) < 1 - p := by linarith
  
  have hpsi0sq : ptn_psi p false ^ 2 = p / (1 - p) := by
    unfold ptn_psi; rw [div_pow, ptn_val_false, hσ2]
    rw [show ((0:ℝ) - p) ^ 2 = p ^ 2 by ring]
    rw [pow_two, mul_div_assoc]
    field_simp
  have hpsi1sq : ptn_psi p true ^ 2 = (1 - p) / p := by
    unfold ptn_psi; rw [div_pow, ptn_val_true, hσ2]
    rw [pow_two (1 - p)]
    field_simp
  have hpsicross : ptn_psi p false * ptn_psi p true = -1 := by
    unfold ptn_psi; rw [div_mul_div_comm, ptn_val_false, ptn_val_true,
      ← pow_two, hσ2]
    rw [show ((0:ℝ) - p) * (1 - p) = -(p * (1-p)) by ring]
    rw [neg_div, div_self (by nlinarith)]
  
  have hfac : ∀ i : ι, (1 + ptn_psi p (x i) * ptn_psi p (y i))
      = if x i = y i then 1 / (if x i then p else 1 - p) else 0 := by
    intro i
    cases hx : x i <;> cases hy : y i <;>
      simp only [Bool.false_eq_true, if_true, if_false, Bool.true_eq_false]
    · 
      rw [show ptn_psi p false * ptn_psi p false = ptn_psi p false ^ 2 by ring, hpsi0sq]
      field_simp; ring
    · 
      rw [hpsicross]; ring
    · 
      rw [mul_comm, hpsicross]; ring
    · 
      rw [show ptn_psi p true * ptn_psi p true = ptn_psi p true ^ 2 by ring, hpsi1sq]
      field_simp; ring
  simp_rw [hfac]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    rw [show OSSS.weight (OSSS.bernoulliWeight p) x = ∏ i : ι, (if x i then p else 1 - p) from rfl]
    simp only [one_div, if_true]
    rw [← Finset.prod_inv_distrib]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])


theorem ptn_expansion {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : ConfigSpace ι → ℝ) (x : ConfigSpace ι) :
    (∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S x) = f x := by
  calc (∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S x)
      = ∑ S : Finset ι,
          (∑ y : ConfigSpace ι, OSSS.weight (OSSS.bernoulliWeight p) y * (f y * ptn_pchar p S y))
            * ptn_pchar p S x := by
        apply Finset.sum_congr rfl; intro S _; rfl
    _ = ∑ y : ConfigSpace ι, OSSS.weight (OSSS.bernoulliWeight p) y * f y
          * (∑ S : Finset ι, ptn_pchar p S y * ptn_pchar p S x) := by
        rw [show (∑ S : Finset ι, (∑ y : ConfigSpace ι,
              OSSS.weight (OSSS.bernoulliWeight p) y * (f y * ptn_pchar p S y)) * ptn_pchar p S x)
            = ∑ S : Finset ι, ∑ y : ConfigSpace ι,
              OSSS.weight (OSSS.bernoulliWeight p) y * f y * (ptn_pchar p S y * ptn_pchar p S x)
            from by apply Finset.sum_congr rfl; intro S _; rw [Finset.sum_mul];
                    apply Finset.sum_congr rfl; intro y _; ring]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro y _
        rw [Finset.mul_sum]
    _ = ∑ y : ConfigSpace ι, OSSS.weight (OSSS.bernoulliWeight p) y * f y
          * (if y = x then 1 / OSSS.weight (OSSS.bernoulliWeight p) y else 0) := by
        apply Finset.sum_congr rfl; intro y _
        rw [ptn_repro_kernel hp0 hp1 y x]
    _ = f x := by
        rw [Finset.sum_eq_single x]
        · rw [if_pos rfl]
          have hw : OSSS.weight (OSSS.bernoulliWeight p) x ≠ 0 := by
            rw [show OSSS.weight (OSSS.bernoulliWeight p) x = ∏ i : ι, (if x i then p else 1 - p) from rfl]
            apply Finset.prod_ne_zero_iff.mpr
            intro i _; cases x i <;> simp only [Bool.false_eq_true, if_true, if_false] <;>
              first | exact hp0.ne' | (intro h; linarith)
          field_simp
        · intro y _ hyx; rw [if_neg hyx, mul_zero]
        · intro h; exact absurd (Finset.mem_univ x) h




theorem ptn_expect_finsetSum {κ : Type*} (p : ℝ) (s : Finset κ) (g : κ → ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => ∑ k ∈ s, g k ω)
      = ∑ k ∈ s, OSSS.expect (OSSS.bernoulliWeight p) (g k) := by
  unfold OSSS.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]


theorem ptn_parseval {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (f g : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => f ω * g ω)
      = ∑ S : Finset ι, ptn_coeff p f S * ptn_coeff p g S := by
  
  have hf : (fun ω : ConfigSpace ι => f ω * g ω)
      = (fun ω => (∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S ω)
                  * (∑ T : Finset ι, ptn_coeff p g T * ptn_pchar p T ω)) := by
    funext ω; rw [ptn_expansion hp0 hp1 f ω, ptn_expansion hp0 hp1 g ω]
  rw [hf]
  
  have hdist : (fun ω : ConfigSpace ι =>
        (∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S ω)
          * (∑ T : Finset ι, ptn_coeff p g T * ptn_pchar p T ω))
      = (fun ω => ∑ S : Finset ι, ∑ T : Finset ι,
          (ptn_coeff p f S * ptn_coeff p g T) * (ptn_pchar p S ω * ptn_pchar p T ω)) := by
    funext ω; rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro S _
    apply Finset.sum_congr rfl; intro T _; ring
  rw [hdist, ptn_expect_finsetSum]
  apply Finset.sum_congr rfl; intro S _
  rw [ptn_expect_finsetSum]
  have hterm : ∀ T ∈ (univ : Finset (Finset ι)),
      OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => ptn_coeff p f S * ptn_coeff p g T * (ptn_pchar p S ω * ptn_pchar p T ω))
        = ptn_coeff p f S * ptn_coeff p g T * (if S = T then 1 else 0) := by
    intro T _
    rw [OSSS.expect_const_mul, ptn_orthonormal hp0 hp1 S T]
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single_of_mem S (Finset.mem_univ S)]
  · rw [if_pos rfl, mul_one]
  · intro T _ hTS; rw [if_neg (fun h => hTS h.symm), mul_zero]


theorem ptn_parseval_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (f : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2)
      = ∑ S : Finset ι, (ptn_coeff p f S) ^ 2 := by
  rw [show (fun ω : ConfigSpace ι => (f ω) ^ 2) = (fun ω => f ω * f ω) from by funext ω; ring]
  rw [ptn_parseval hp0 hp1 f f]
  apply Finset.sum_congr rfl; intro S _; rw [sq]



theorem ptn_var_eq_fourierWeight {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (f : ConfigSpace ι → ℝ) :
    OSSS.var (OSSS.bernoulliWeight p) f
      = ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 := by
  unfold OSSS.var OSSS.cov
  rw [show (fun ω : ConfigSpace ι => f ω * f ω) = (fun ω => (f ω) ^ 2) from by funext ω; ring]
  rw [ptn_parseval_sq hp0 hp1 f]
  rw [← Finset.add_sum_erase univ (fun S => (ptn_coeff p f S) ^ 2) (Finset.mem_univ (∅ : Finset ι))]
  rw [ptn_coeff_empty]
  ring





theorem ptn_psi_jump {p : ℝ} (_hp0 : 0 < p) (_hp1 : p < 1) :
    ptn_psi p true - ptn_psi p false = 1 / ptn_sigma p := by
  unfold ptn_psi; rw [ptn_val_true, ptn_val_false, div_sub_div_same]
  congr 1; ring

omit [Fintype ι] in


theorem ptn_pchar_deriv {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (S : Finset ι) (e : ι)
    (ω : ConfigSpace ι) :
    ptn_pchar p S (StatMech.setOpen e ω) - ptn_pchar p S (StatMech.setClosed e ω)
      = if e ∈ S then (1 / ptn_sigma p) * ptn_pchar p (S.erase e) ω else 0 := by
  by_cases he : e ∈ S
  · rw [if_pos he]
    unfold ptn_pchar
    rw [← Finset.prod_erase_mul S _ he, ← Finset.prod_erase_mul S _ he]
    have hprodO : (∏ i ∈ S.erase e, ptn_psi p (StatMech.setOpen e ω i))
        = ∏ i ∈ S.erase e, ptn_psi p (ω i) := by
      apply Finset.prod_congr rfl
      intro i hi; rw [StatMech.setOpen_of_ne (Finset.ne_of_mem_erase hi)]
    have hprodC : (∏ i ∈ S.erase e, ptn_psi p (StatMech.setClosed e ω i))
        = ∏ i ∈ S.erase e, ptn_psi p (ω i) := by
      apply Finset.prod_congr rfl
      intro i hi; rw [StatMech.setClosed_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hprodO, hprodC, StatMech.setOpen_self, StatMech.setClosed_self]
    rw [← mul_sub, ptn_psi_jump hp0 hp1]
    ring
  · rw [if_neg he]
    unfold ptn_pchar
    have : (∏ i ∈ S, ptn_psi p (StatMech.setOpen e ω i))
        = ∏ i ∈ S, ptn_psi p (StatMech.setClosed e ω i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hie : i ≠ e := fun h => he (h ▸ hi)
      rw [StatMech.setOpen_of_ne hie, StatMech.setClosed_of_ne hie]
    rw [this, sub_self]



theorem ptn_deriv_fourier {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : ConfigSpace ι → ℝ) (e : ι) (ω : ConfigSpace ι) :
    f (StatMech.setOpen e ω) - f (StatMech.setClosed e ω)
      = ∑ S ∈ univ.filter (fun S => e ∈ S),
          (ptn_coeff p f S / ptn_sigma p) * ptn_pchar p (S.erase e) ω := by
  have hO : f (StatMech.setOpen e ω)
      = ∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S (StatMech.setOpen e ω) := by
    rw [ptn_expansion hp0 hp1]
  have hC : f (StatMech.setClosed e ω)
      = ∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S (StatMech.setClosed e ω) := by
    rw [ptn_expansion hp0 hp1]
  rw [hO, hC, ← Finset.sum_sub_distrib]
  have hterm : ∀ S : Finset ι,
      ptn_coeff p f S * ptn_pchar p S (StatMech.setOpen e ω)
        - ptn_coeff p f S * ptn_pchar p S (StatMech.setClosed e ω)
        = if e ∈ S then (ptn_coeff p f S / ptn_sigma p) * ptn_pchar p (S.erase e) ω else 0 := by
    intro S; rw [← mul_sub, ptn_pchar_deriv hp0 hp1]
    by_cases he : e ∈ S
    · rw [if_pos he, if_pos he]; rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]; ring
    · rw [if_neg he, if_neg he, mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_filter]



theorem ptn_expect_sum_pchar_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (s : Finset (Finset ι)) (a : Finset ι → ℝ) (T : Finset ι → Finset ι)
    (hTinj : Set.InjOn T s) :
    OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => (∑ S ∈ s, a S * ptn_pchar p (T S) ω) ^ 2)
      = ∑ S ∈ s, (a S) ^ 2 := by
  rw [show (fun ω : ConfigSpace ι => (∑ S ∈ s, a S * ptn_pchar p (T S) ω) ^ 2)
      = (fun ω => ∑ S ∈ s, ∑ U ∈ s,
          (a S * a U) * (ptn_pchar p (T S) ω * ptn_pchar p (T U) ω)) from ?_]
  · rw [ptn_expect_finsetSum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [ptn_expect_finsetSum]
    have hterm : ∀ U ∈ s,
        OSSS.expect (OSSS.bernoulliWeight p)
          (fun ω => a S * a U * (ptn_pchar p (T S) ω * ptn_pchar p (T U) ω))
          = a S * a U * (if T S = T U then 1 else 0) := by
      intro U _; rw [OSSS.expect_const_mul, ptn_orthonormal hp0 hp1]
    rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single_of_mem S hS]
    · rw [if_pos rfl, mul_one, sq]
    · intro U hU hUS
      have hne : T S ≠ T U := fun h => hUS (hTinj hU hS h.symm)
      rw [if_neg hne, mul_zero]
  · funext ω; rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro S _
    apply Finset.sum_congr rfl; intro U _; ring


theorem ptn_erase_injOn (e : ι) :
    Set.InjOn (fun S => Finset.erase S e) ↑(univ.filter (fun S : Finset ι => e ∈ S)) := by
  intro S hS U hU h
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hS hU
  simp only at h
  rw [← Finset.insert_erase hS, ← Finset.insert_erase hU, h]

omit [Fintype ι] in

theorem ptn_abs_diff_indicator (φ : ConfigSpace ι → Bool) (e : ι) (ω : ConfigSpace ι) :
    |(fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω)
        - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)|
      = ((fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω)
        - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)) ^ 2 := by
  simp only
  by_cases hO : φ (StatMech.setOpen e ω) <;> by_cases hC : φ (StatMech.setClosed e ω) <;>
    simp [hO, hC]





theorem ptn_infl_eq_fourierWeight {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) (e : ι) :
    OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e
      = (1 / (ptn_sigma p) ^ 2) * ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  set g := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hg
  unfold OSSS.infl
  have habs : (fun ω => |g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω)|)
      = (fun ω => (g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω)) ^ 2) := by
    funext ω; exact ptn_abs_diff_indicator φ e ω
  rw [habs]
  have hd : (fun ω : ConfigSpace ι => (g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω)) ^ 2)
      = (fun ω => (∑ S ∈ univ.filter (fun S => e ∈ S),
          (ptn_coeff p g S / ptn_sigma p) * ptn_pchar p (S.erase e) ω) ^ 2) := by
    funext ω; rw [ptn_deriv_fourier hp0 hp1 g e ω]
  rw [hd, ptn_expect_sum_pchar_sq hp0 hp1 _ _ (fun S => S.erase e) (ptn_erase_injOn e)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [div_pow, one_div, ← div_eq_inv_mul]



theorem ptn_totalInfl_eq_fourierWeight {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) :
    totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      = (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  set c := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  unfold totalInfl
  have hinfl : ∀ e : ι,
      OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e
        = (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (if e ∈ S then c S else 0) := by
    intro e; rw [ptn_infl_eq_fourierWeight hp0 hp1, Finset.sum_filter]
  simp_rw [hinfl]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hc, nsmul_eq_mul]




noncomputable def ptn_qnormPow (p q : ℝ) (f : ConfigSpace ι → ℝ) : ℝ :=
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => |f ω| ^ q)


noncomputable def ptn_qnorm (p q : ℝ) (f : ConfigSpace ι → ℝ) : ℝ :=
  (ptn_qnormPow p q f) ^ (1 / q)

theorem ptn_qnormPow_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℝ) (f : ConfigSpace ι → ℝ) :
    0 ≤ ptn_qnormPow p q f := by
  unfold ptn_qnormPow OSSS.expect
  exact Finset.sum_nonneg (fun ω _ =>
    mul_nonneg (Finset.prod_nonneg (fun e _ => (bernoulliWeight_isProbWeight hp0 hp1).nonneg e (ω e)))
      (Real.rpow_nonneg (abs_nonneg _) q))

theorem ptn_qnorm_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℝ) (f : ConfigSpace ι → ℝ) :
    0 ≤ ptn_qnorm p q f :=
  Real.rpow_nonneg (ptn_qnormPow_nonneg hp0 hp1 q f) _


theorem ptn_qnorm_rpow_self {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : ℝ} (hq : q ≠ 0)
    (f : ConfigSpace ι → ℝ) :
    ptn_qnorm p q f ^ q = ptn_qnormPow p q f := by
  unfold ptn_qnorm
  rw [← Real.rpow_mul (ptn_qnormPow_nonneg hp0 hp1 q f), one_div, inv_mul_cancel₀ hq,
    Real.rpow_one]


noncomputable def ptn_noiseOp (p ρ : ℝ) (f : ConfigSpace ι → ℝ) : ConfigSpace ι → ℝ :=
  fun ω => ∑ S : Finset ι, (ρ ^ S.card * ptn_coeff p f S) * ptn_pchar p S ω


theorem ptn_noiseOp_l2sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : ℝ) (f : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (ptn_noiseOp p ρ f ω) ^ 2)
      = ∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2 := by
  unfold ptn_noiseOp
  have hT : Set.InjOn (fun S : Finset ι => S) ↑(univ : Finset (Finset ι)) :=
    fun _ _ _ _ h => h
  rw [ptn_expect_sum_pchar_sq hp0 hp1 univ (fun S => ρ ^ S.card * ptn_coeff p f S)
      (fun S => S) hT]
  apply Finset.sum_congr rfl; intro S _; ring


theorem ptn_qnormPow2_eq_expect_sq {p : ℝ} (f : ConfigSpace ι → ℝ) :
    ptn_qnormPow p 2 f = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2) := by
  unfold ptn_qnormPow
  congr 1; funext ω
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]


theorem ptn_qnorm2_sq {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : ConfigSpace ι → ℝ) :
    (ptn_qnorm p 2 f) ^ 2 = ptn_qnormPow p 2 f := by
  rw [show (ptn_qnorm p 2 f) ^ 2 = (ptn_qnorm p 2 f) ^ (2 : ℝ) from by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
  exact ptn_qnorm_rpow_self hp0 hp1 (by norm_num) f




theorem ptn_sum_cons_split {n : ℕ} {M : Type*} [AddCommMonoid M]
    (F : (Fin (n + 1) → Bool) → M) :
    (∑ y : Fin (n + 1) → Bool, F y)
      = ∑ c : Bool, ∑ ω' : Fin n → Bool, F (Fin.cons c ω') := by
  rw [← Fintype.sum_prod_type (fun q : Bool × (Fin n → Bool) => F (Fin.cons q.1 q.2))]
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool))
    (fun q => F (Fin.cons q.1 q.2)) F (fun _ => rfl)).symm



theorem ptn_expect_cons_split {n : ℕ} (p : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) f
      = (1 - p) * OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool => f (Fin.cons false ω'))
        + p * OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool => f (Fin.cons true ω')) := by
  unfold OSSS.expect
  rw [ptn_sum_cons_split (fun y => OSSS.weight (OSSS.bernoulliWeight p) y * f y), Fintype.sum_bool]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [show (∑ x : Fin n → Bool, (1 - p) * (OSSS.weight (OSSS.bernoulliWeight p) x * f (Fin.cons false x)))
        + ∑ x : Fin n → Bool, p * (OSSS.weight (OSSS.bernoulliWeight p) x * f (Fin.cons true x))
      = ∑ x : Fin n → Bool, ((1 - p) * (OSSS.weight (OSSS.bernoulliWeight p) x * f (Fin.cons false x))
          + p * (OSSS.weight (OSSS.bernoulliWeight p) x * f (Fin.cons true x)))
      from (Finset.sum_add_distrib).symm]
  rw [show (∑ ω' : Fin n → Bool, OSSS.weight (OSSS.bernoulliWeight p) (Fin.cons true ω') * f (Fin.cons true ω'))
        + ∑ ω' : Fin n → Bool, OSSS.weight (OSSS.bernoulliWeight p) (Fin.cons false ω') * f (Fin.cons false ω')
      = ∑ ω' : Fin n → Bool, (OSSS.weight (OSSS.bernoulliWeight p) (Fin.cons true ω') * f (Fin.cons true ω')
          + OSSS.weight (OSSS.bernoulliWeight p) (Fin.cons false ω') * f (Fin.cons false ω'))
      from (Finset.sum_add_distrib).symm]
  apply Finset.sum_congr rfl
  intro ω' _
  
  have hwc : ∀ c : Bool, OSSS.weight (OSSS.bernoulliWeight p) (Fin.cons c ω')
      = OSSS.bernoulliWeight p (0 : Fin (n+1)) c * OSSS.weight (OSSS.bernoulliWeight p) ω' := by
    intro c
    unfold OSSS.weight
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, OSSS.bernoulliWeight]
  rw [hwc false, hwc true]
  unfold OSSS.bernoulliWeight
  simp only [Bool.false_eq_true, if_false, if_true]
  ring









noncomputable def ptn_kbit (p ρ : ℝ) (x y : Bool) : ℝ :=
  ρ * (if x = y then 1 else 0) + (1 - ρ) * (if y then p else 1 - p)


noncomputable def ptn_kernel (p ρ : ℝ) (x y : ConfigSpace ι) : ℝ :=
  ∏ i : ι, ptn_kbit p ρ (x i) (y i)


noncomputable def ptn_kop (p ρ : ℝ) (f : ConfigSpace ι → ℝ) : ConfigSpace ι → ℝ :=
  fun x => ∑ y : ConfigSpace ι, ptn_kernel p ρ x y * f y





theorem ptn_kop_pchar_apply {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : ℝ) (S : Finset ι)
    (x : ConfigSpace ι) :
    ptn_kop p ρ (ptn_pchar p S) x = ρ ^ S.card * ptn_pchar p S x := by
  have hmean := ptn_psi_mean hp0 hp1
  unfold ptn_kop ptn_kernel ptn_pchar
  
  have hchar : ∀ y : ConfigSpace ι, (∏ i ∈ S, ptn_psi p (y i))
      = ∏ i : ι, (if i ∈ S then ptn_psi p (y i) else 1) := by
    intro y; rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [hchar]
  have hcomb : ∀ y : ConfigSpace ι,
      (∏ i : ι, ptn_kbit p ρ (x i) (y i)) * (∏ i : ι, (if i ∈ S then ptn_psi p (y i) else 1))
        = ∏ i : ι, (ptn_kbit p ρ (x i) (y i) * (if i ∈ S then ptn_psi p (y i) else 1)) := by
    intro y; rw [← Finset.prod_mul_distrib]
  simp_rw [hcomb]
  rw [← Fintype.prod_sum (fun (i : ι) (c : Bool) =>
        ptn_kbit p ρ (x i) c * (if i ∈ S then ptn_psi p c else 1))]
  
  have hfac : ∀ i : ι,
      (∑ c : Bool, ptn_kbit p ρ (x i) c * (if i ∈ S then ptn_psi p c else 1))
        = if i ∈ S then ρ * ptn_psi p (x i) else 1 := by
    intro i
    unfold ptn_kbit
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      rw [Fintype.sum_bool]
      cases hx : x i <;>
        simp only [Bool.false_eq_true, if_false, if_true, Bool.true_eq_false] <;>
        linear_combination (1 - ρ) * hmean
    · simp only [hi, if_false, mul_one]
      rw [Fintype.sum_bool]
      cases hx : x i <;>
        simp only [Bool.false_eq_true, if_false, if_true, Bool.true_eq_false] <;> ring
  simp_rw [hfac]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_mul_distrib, Finset.prod_const]


theorem ptn_kop_finsetSum {κ : Type*} (p ρ : ℝ) (s : Finset κ) (g : κ → ConfigSpace ι → ℝ) :
    ptn_kop p ρ (fun x => ∑ k ∈ s, g k x) = fun x => ∑ k ∈ s, ptn_kop p ρ (g k) x := by
  funext x; unfold ptn_kop; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]


theorem ptn_kop_const_mul (p ρ c : ℝ) (g : ConfigSpace ι → ℝ) :
    ptn_kop p ρ (fun x => c * g x) = fun x => c * ptn_kop p ρ g x := by
  funext x; unfold ptn_kop; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro y _; ring




theorem ptn_kop_eq_noiseOp {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : ℝ) (f : ConfigSpace ι → ℝ) :
    ptn_kop p ρ f = ptn_noiseOp p ρ f := by
  have hf : f = (fun x => ∑ S : Finset ι, ptn_coeff p f S * ptn_pchar p S x) := by
    funext x; rw [ptn_expansion hp0 hp1]
  conv_lhs => rw [hf]
  rw [ptn_kop_finsetSum]
  funext x
  unfold ptn_noiseOp
  simp_rw [ptn_kop_const_mul p ρ (ptn_coeff p f _) (ptn_pchar p _)]
  apply Finset.sum_congr rfl
  intro S _
  rw [ptn_kop_pchar_apply hp0 hp1]
  ring





theorem ptn_expect_sq_lincomb (p a b : ℝ) (u v : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (a * u ω + b * v ω) ^ 2)
      = a ^ 2 * OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (u ω) ^ 2)
        + 2 * a * b * OSSS.expect (OSSS.bernoulliWeight p) (fun ω => u ω * v ω)
        + b ^ 2 * OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (v ω) ^ 2) := by
  rw [show (fun ω : ConfigSpace ι => (a * u ω + b * v ω) ^ 2)
      = (fun ω => a ^ 2 * (u ω) ^ 2 + (2 * a * b) * (u ω * v ω) + b ^ 2 * (v ω) ^ 2)
    from by funext ω; ring]
  rw [OSSS.expect_add, OSSS.expect_add, OSSS.expect_const_mul, OSSS.expect_const_mul,
    OSSS.expect_const_mul]


theorem ptn_expect_inner_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u v : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => u ω * v ω)
      ≤ Real.sqrt (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (u ω) ^ 2))
        * Real.sqrt (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (v ω) ^ 2)) := by
  set W := fun ω : ConfigSpace ι => OSSS.weight (OSSS.bernoulliWeight p) ω with hW
  have hWnn : ∀ ω, 0 ≤ W ω := fun ω =>
    Finset.prod_nonneg (fun e _ => (bernoulliWeight_isProbWeight hp0 hp1).nonneg e (ω e))
  
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (ConfigSpace ι))
    (fun ω => Real.sqrt (W ω) * u ω) (fun ω => Real.sqrt (W ω) * v ω)
  
  have hsqW : ∀ ω, Real.sqrt (W ω) * Real.sqrt (W ω) = W ω := fun ω =>
    Real.mul_self_sqrt (hWnn ω)
  have he1 : (∑ ω : ConfigSpace ι, (Real.sqrt (W ω) * u ω) * (Real.sqrt (W ω) * v ω))
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => u ω * v ω) := by
    unfold OSSS.expect; apply Finset.sum_congr rfl
    intro ω _; rw [show (Real.sqrt (W ω) * u ω) * (Real.sqrt (W ω) * v ω)
        = (Real.sqrt (W ω) * Real.sqrt (W ω)) * (u ω * v ω) by ring, hsqW]
  have he2 : (∑ ω : ConfigSpace ι, (Real.sqrt (W ω) * u ω) ^ 2)
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (u ω) ^ 2) := by
    unfold OSSS.expect; apply Finset.sum_congr rfl
    intro ω _; rw [mul_pow, Real.sq_sqrt (hWnn ω)]
  have he3 : (∑ ω : ConfigSpace ι, (Real.sqrt (W ω) * v ω) ^ 2)
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (v ω) ^ 2) := by
    unfold OSSS.expect; apply Finset.sum_congr rfl
    intro ω _; rw [mul_pow, Real.sq_sqrt (hWnn ω)]
  rw [he1, he2, he3] at hcs
  
  set Euv := OSSS.expect (OSSS.bernoulliWeight p) (fun ω => u ω * v ω)
  set Eu := OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (u ω) ^ 2) with hEu
  set Ev := OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (v ω) ^ 2) with hEv
  have hEunn : 0 ≤ Eu := by
    rw [hEu]; unfold OSSS.expect
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hWnn ω) (sq_nonneg _))
  have hEvnn : 0 ≤ Ev := by
    rw [hEv]; unfold OSSS.expect
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hWnn ω) (sq_nonneg _))
  calc Euv ≤ Real.sqrt (Euv ^ 2) := by rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
    _ ≤ Real.sqrt (Eu * Ev) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt Eu * Real.sqrt Ev := Real.sqrt_mul hEunn Ev





theorem ptn_kernel_cons {n : ℕ} (p ρ : ℝ) (a c : Bool) (ω ω' : Fin n → Bool) :
    ptn_kernel p ρ (Fin.cons a ω) (Fin.cons c ω')
      = ptn_kbit p ρ a c * ptn_kernel p ρ ω ω' := by
  unfold ptn_kernel
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]



theorem ptn_kop_cons {n : ℕ} (p ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) (a : Bool)
    (ω : Fin n → Bool) :
    ptn_kop p ρ f (Fin.cons a ω)
      = ∑ c : Bool, ptn_kbit p ρ a c
          * ptn_kop p ρ (fun ω' : Fin n → Bool => f (Fin.cons c ω')) ω := by
  unfold ptn_kop
  rw [ptn_sum_cons_split (fun y : Fin (n + 1) → Bool => ptn_kernel p ρ (Fin.cons a ω) y * f y)]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω' _
  rw [ptn_kernel_cons]
  ring



theorem ptn_kop_cons_pair {n : ℕ} (p ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) (a : Bool)
    (ω : Fin n → Bool) :
    ptn_kop p ρ f (Fin.cons a ω)
      = ptn_kbit p ρ a false * ptn_kop p ρ (fun ω' => f (Fin.cons false ω')) ω
        + ptn_kbit p ρ a true * ptn_kop p ρ (fun ω' => f (Fin.cons true ω')) ω := by
  rw [ptn_kop_cons, Fintype.sum_bool, add_comm]




theorem ptn_kop_fin_zero (p ρ : ℝ) (f : (Fin 0 → Bool) → ℝ) :
    ptn_kop p ρ f = f := by
  funext x
  unfold ptn_kop ptn_kernel
  rw [Finset.sum_eq_single x]
  · rw [Finset.prod_eq_one (fun i _ => absurd i.2 (by simp)), one_mul]
  · intro y _ hyx; exact absurd (Subsingleton.elim y x) hyx
  · intro h; exact absurd (Finset.mem_univ x) h


theorem ptn_qnorm_fin_zero {p q : ℝ} (hq : 0 < q) (f : (Fin 0 → Bool) → ℝ) :
    ptn_qnorm p q f = |f default| := by
  unfold ptn_qnorm ptn_qnormPow OSSS.expect
  rw [Finset.sum_eq_single (default : Fin 0 → Bool)]
  · rw [show OSSS.weight (OSSS.bernoulliWeight p) (default : Fin 0 → Bool) = 1 from by
        unfold OSSS.weight; rw [Finset.prod_eq_one (fun i _ => absurd i.2 (by simp))]]
    simp only [one_mul]
    rw [← Real.rpow_mul (abs_nonneg _), one_div, mul_inv_cancel₀ (ne_of_gt hq), Real.rpow_one]
  · intro y _ hy; exact absurd (Subsingleton.elim y default) hy
  · intro h; exact absurd (Finset.mem_univ _) h



theorem ptn_qnormPow_cons_split {n : ℕ} (p q : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) :
    ptn_qnormPow p q f
      = (1 - p) * ptn_qnormPow p q (fun ω' : Fin n → Bool => f (Fin.cons false ω'))
        + p * ptn_qnormPow p q (fun ω' : Fin n → Bool => f (Fin.cons true ω')) := by
  unfold ptn_qnormPow
  rw [ptn_expect_cons_split p (fun ω => |f ω| ^ q)]




theorem ptn_kbit_ff (p ρ : ℝ) : ptn_kbit p ρ false false = ρ + (1 - ρ) * (1 - p) := by
  unfold ptn_kbit; norm_num
theorem ptn_kbit_ft (p ρ : ℝ) : ptn_kbit p ρ false true = (1 - ρ) * p := by
  unfold ptn_kbit; norm_num
theorem ptn_kbit_tf (p ρ : ℝ) : ptn_kbit p ρ true false = (1 - ρ) * (1 - p) := by
  unfold ptn_kbit; norm_num
theorem ptn_kbit_tt (p ρ : ℝ) : ptn_kbit p ρ true true = ρ + (1 - ρ) * p := by
  unfold ptn_kbit; norm_num



theorem ptn_kop_l2sq_cons {n : ℕ} (p ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) :
    ptn_qnormPow p 2 (ptn_kop p ρ f)
      = (1 - p) * OSSS.expect (OSSS.bernoulliWeight p)
            (fun ω : Fin n → Bool => (ptn_kbit p ρ false false
              * ptn_kop p ρ (fun ω' => f (Fin.cons false ω')) ω
              + ptn_kbit p ρ false true * ptn_kop p ρ (fun ω' => f (Fin.cons true ω')) ω) ^ 2)
        + p * OSSS.expect (OSSS.bernoulliWeight p)
            (fun ω : Fin n → Bool => (ptn_kbit p ρ true false
              * ptn_kop p ρ (fun ω' => f (Fin.cons false ω')) ω
              + ptn_kbit p ρ true true * ptn_kop p ρ (fun ω' => f (Fin.cons true ω')) ω) ^ 2) := by
  rw [ptn_qnormPow2_eq_expect_sq, ptn_expect_cons_split p (fun ω => (ptn_kop p ρ f ω) ^ 2)]
  congr 2 <;> · congr 1; funext ω; rw [ptn_kop_cons_pair]




theorem ptn_cons_quadform_eq {p q ρ u v : ℝ} (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) :
    (1 - p) * (ptn_kbit p ρ false false * u + ptn_kbit p ρ false true * v) ^ 2
        + p * (ptn_kbit p ρ true false * u + ptn_kbit p ρ true true * v) ^ 2
      = ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2 := by
  rw [ptn_kbit_ff, ptn_kbit_ft, ptn_kbit_tf, ptn_kbit_tt]
  linear_combination (p * (1 - p) * (u - v) ^ 2) * hρsq


theorem ptn_kbit_nonneg {p ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a c : Bool) : 0 ≤ ptn_kbit p ρ a c := by
  cases a <;> cases c <;>
    simp only [ptn_kbit_ff, ptn_kbit_ft, ptn_kbit_tf, ptn_kbit_tt] <;> nlinarith








theorem ptn_tensorStep {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) (n : ℕ)
    (ih : ∀ g : (Fin n → Bool) → ℝ, ptn_qnorm p 2 (ptn_kop p ρ g) ≤ ptn_qnorm p q g)
    (f : (Fin (n + 1) → Bool) → ℝ) :
    ptn_qnorm p 2 (ptn_kop p ρ f) ≤ ptn_qnorm p q f := by
  have hq0 : (0 : ℝ) < q := by linarith
  set g₀ : (Fin n → Bool) → ℝ := fun ω' => f (Fin.cons false ω') with hg0
  set g₁ : (Fin n → Bool) → ℝ := fun ω' => f (Fin.cons true ω') with hg1
  set F₀ := ptn_kop p ρ g₀ with hF0
  set F₁ := ptn_kop p ρ g₁ with hF1
  set Eu := OSSS.expect (OSSS.bernoulliWeight p) (fun ω : Fin n → Bool => (F₀ ω) ^ 2) with hEu
  set Ev := OSSS.expect (OSSS.bernoulliWeight p) (fun ω : Fin n → Bool => (F₁ ω) ^ 2) with hEv
  set Euv := OSSS.expect (OSSS.bernoulliWeight p) (fun ω : Fin n → Bool => F₀ ω * F₁ ω) with hEuv
  set u := Real.sqrt Eu with hu
  set v := Real.sqrt Ev with hv
  have hEunn : 0 ≤ Eu := by
    rw [hEu]; unfold OSSS.expect
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg
      (Finset.prod_nonneg (fun e _ => (bernoulliWeight_isProbWeight hp0.le hp1.le).nonneg e (ω e)))
      (sq_nonneg _))
  have hEvnn : 0 ≤ Ev := by
    rw [hEv]; unfold OSSS.expect
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg
      (Finset.prod_nonneg (fun e _ => (bernoulliWeight_isProbWeight hp0.le hp1.le).nonneg e (ω e)))
      (sq_nonneg _))
  have hunn : 0 ≤ u := Real.sqrt_nonneg _
  have hvnn : 0 ≤ v := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = Eu := Real.sq_sqrt hEunn
  have hv2 : v ^ 2 = Ev := Real.sq_sqrt hEvnn
  have hCS : Euv ≤ u * v := by rw [hu, hv]; exact ptn_expect_inner_le hp0.le hp1.le F₀ F₁
  
  have hLHS : ptn_qnormPow p 2 (ptn_kop p ρ f)
      = (1 - p) * (ptn_kbit p ρ false false ^ 2 * Eu
            + 2 * ptn_kbit p ρ false false * ptn_kbit p ρ false true * Euv
            + ptn_kbit p ρ false true ^ 2 * Ev)
        + p * (ptn_kbit p ρ true false ^ 2 * Eu
            + 2 * ptn_kbit p ρ true false * ptn_kbit p ρ true true * Euv
            + ptn_kbit p ρ true true ^ 2 * Ev) := by
    rw [ptn_kop_l2sq_cons]
    rw [ptn_expect_sq_lincomb p (ptn_kbit p ρ false false) (ptn_kbit p ρ false true) F₀ F₁,
        ptn_expect_sq_lincomb p (ptn_kbit p ρ true false) (ptn_kbit p ρ true true) F₀ F₁]
  
  have hcoef0 : 0 ≤ (1 - p) * (2 * ptn_kbit p ρ false false * ptn_kbit p ρ false true) := by
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le false false
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le false true
    positivity
  have hcoef1 : 0 ≤ p * (2 * ptn_kbit p ρ true false * ptn_kbit p ρ true true) := by
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le true false
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le true true
    positivity
  
  set a00 := ptn_kbit p ρ false false with ha00
  set a01 := ptn_kbit p ρ false true with ha01
  set a10 := ptn_kbit p ρ true false with ha10
  set a11 := ptn_kbit p ρ true true with ha11
  have hbound : ptn_qnormPow p 2 (ptn_kop p ρ f)
      ≤ (1 - p) * (a00 * u + a01 * v) ^ 2 + p * (a10 * u + a11 * v) ^ 2 := by
    rw [hLHS]
    have hgoal : (1 - p) * (a00 * u + a01 * v) ^ 2 + p * (a10 * u + a11 * v) ^ 2
        - ((1 - p) * (a00 ^ 2 * Eu + 2 * a00 * a01 * Euv + a01 ^ 2 * Ev)
          + p * (a10 ^ 2 * Eu + 2 * a10 * a11 * Euv + a11 ^ 2 * Ev))
        = (1 - p) * (2 * a00 * a01) * (u * v - Euv) + p * (2 * a10 * a11) * (u * v - Euv) := by
      rw [← hu2, ← hv2]; ring
    have hc0 : 0 ≤ (1 - p) * (2 * a00 * a01) * (u * v - Euv) :=
      mul_nonneg hcoef0 (by linarith [hCS])
    have hc1 : 0 ≤ p * (2 * a10 * a11) * (u * v - Euv) :=
      mul_nonneg hcoef1 (by linarith [hCS])
    linarith [hgoal, hc0, hc1]
  
  have hquad := ptn_cons_quadform_eq (p := p) (q := q) (ρ := ρ) (u := u) (v := v) hρsq
  have hpcx := pcx_two_point_value hp0 hp1 hq1 hq2 u v
  rw [abs_of_nonneg hunn, abs_of_nonneg hvnn] at hpcx
  have hstep1 : ptn_qnormPow p 2 (ptn_kop p ρ f)
      ≤ ((1 - p) * u ^ q + p * v ^ q) ^ (2 / q) := by
    refine le_trans hbound ?_
    rw [hquad]; exact hpcx
  
  have hub : u ≤ ptn_qnorm p q g₀ := by
    have hsq : Eu = (ptn_qnorm p 2 F₀) ^ 2 := by
      rw [hEu, ← ptn_qnormPow2_eq_expect_sq, ptn_qnorm2_sq hp0.le hp1.le F₀]
    rw [hu, hsq, Real.sqrt_sq (ptn_qnorm_nonneg hp0.le hp1.le 2 F₀)]
    exact ih g₀
  have hvb : v ≤ ptn_qnorm p q g₁ := by
    have hsq : Ev = (ptn_qnorm p 2 F₁) ^ 2 := by
      rw [hEv, ← ptn_qnormPow2_eq_expect_sq, ptn_qnorm2_sq hp0.le hp1.le F₁]
    rw [hv, hsq, Real.sqrt_sq (ptn_qnorm_nonneg hp0.le hp1.le 2 F₁)]
    exact ih g₁
  have huq : u ^ q ≤ ptn_qnormPow p q g₀ := by
    rw [← ptn_qnorm_rpow_self hp0.le hp1.le (ne_of_gt hq0) g₀]
    exact Real.rpow_le_rpow hunn hub hq0.le
  have hvq : v ^ q ≤ ptn_qnormPow p q g₁ := by
    rw [← ptn_qnorm_rpow_self hp0.le hp1.le (ne_of_gt hq0) g₁]
    exact Real.rpow_le_rpow hvnn hvb hq0.le
  have hbasebound : (1 - p) * u ^ q + p * v ^ q ≤ ptn_qnormPow p q f := by
    rw [ptn_qnormPow_cons_split p q f, ← hg0, ← hg1]
    have h1p : 0 ≤ 1 - p := by linarith
    have hA := mul_le_mul_of_nonneg_left huq h1p
    have hB := mul_le_mul_of_nonneg_left hvq hp0.le
    linarith
  have hBnn : (0 : ℝ) ≤ (1 - p) * u ^ q + p * v ^ q := by
    have : (0:ℝ) ≤ u ^ q := Real.rpow_nonneg hunn q
    have : (0:ℝ) ≤ v ^ q := Real.rpow_nonneg hvnn q
    have h1p : 0 ≤ 1 - p := by linarith
    positivity
  
  have hstep2 : ptn_qnormPow p 2 (ptn_kop p ρ f) ≤ (ptn_qnormPow p q f) ^ (2 / q) := by
    refine le_trans hstep1 ?_
    exact Real.rpow_le_rpow hBnn hbasebound (by positivity)
  
  unfold ptn_qnorm
  calc (ptn_qnormPow p 2 (ptn_kop p ρ f)) ^ (1 / (2:ℝ))
      ≤ ((ptn_qnormPow p q f) ^ (2 / q)) ^ (1 / (2:ℝ)) :=
        Real.rpow_le_rpow (ptn_qnormPow_nonneg hp0.le hp1.le 2 _) hstep2 (by norm_num)
    _ = (ptn_qnormPow p q f) ^ (1 / q) := by
        rw [← Real.rpow_mul (ptn_qnormPow_nonneg hp0.le hp1.le q f)]
        congr 1; field_simp





theorem ptn_hypercontractivity_fin {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    ptn_qnorm p 2 (ptn_kop p ρ f) ≤ ptn_qnorm p q f := by
  induction n with
  | zero =>
    rw [ptn_kop_fin_zero, ptn_qnorm_fin_zero (by norm_num : (0:ℝ) < 2),
        ptn_qnorm_fin_zero (by linarith : (0:ℝ) < q)]
  | succ m ih => exact ptn_tensorStep hp0 hp1 h0 h1 hq1 hq2 hρsq m (fun g => ih g) f





theorem ptn_lowDegreeWeight_fin {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    (∑ S : Finset (Fin n), (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2)
      ≤ (ptn_qnorm p q f) ^ 2 := by
  have hhc := ptn_hypercontractivity_fin hp0 hp1 h0 h1 hq1 hq2 hρsq n f
  have hlhsnn : 0 ≤ ptn_qnorm p 2 (ptn_kop p ρ f) := ptn_qnorm_nonneg hp0.le hp1.le 2 _
  have hrhsnn : 0 ≤ ptn_qnorm p q f := ptn_qnorm_nonneg hp0.le hp1.le q f
  have hsq : (ptn_qnorm p 2 (ptn_kop p ρ f)) ^ 2 ≤ (ptn_qnorm p q f) ^ 2 := by
    nlinarith [hhc, hlhsnn, hrhsnn]
  rw [ptn_qnorm2_sq hp0.le hp1.le, ptn_qnormPow2_eq_expect_sq, ptn_kop_eq_noiseOp hp0 hp1,
      ptn_noiseOp_l2sq hp0 hp1] at hsq
  exact hsq





noncomputable def ptn_reindex {κ : Type*} (σ : κ ≃ ι) (f : ConfigSpace ι → ℝ) :
    ConfigSpace κ → ℝ :=
  fun y => f (fun i => y (σ.symm i))


def ptn_cubeEquiv {κ : Type*} (σ : κ ≃ ι) : ConfigSpace ι ≃ ConfigSpace κ :=
  Equiv.arrowCongr σ.symm (Equiv.refl Bool)


theorem ptn_expect_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (σ : κ ≃ ι) (p : ℝ)
    (f : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (ptn_reindex σ f)
      = OSSS.expect (OSSS.bernoulliWeight p) f := by
  unfold OSSS.expect ptn_reindex
  symm
  apply Fintype.sum_equiv (ptn_cubeEquiv σ)
  intro x
  unfold ptn_cubeEquiv
  have hxj : ∀ j : κ, (σ.symm.arrowCongr (Equiv.refl Bool)) x j = x (σ j) := by
    intro j; simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp, Equiv.symm_symm,
      id_eq]
  congr 1
  · unfold OSSS.weight
    rw [← Equiv.prod_comp σ (fun i : ι => OSSS.bernoulliWeight p i (x i))]
    apply Finset.prod_congr rfl
    intro j _
    rw [hxj j]; simp only [OSSS.bernoulliWeight]
  · congr 1; funext i
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp, Equiv.symm_symm, id_eq,
      Equiv.apply_symm_apply]


theorem ptn_qnorm_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (σ : κ ≃ ι) (p q : ℝ)
    (f : ConfigSpace ι → ℝ) :
    ptn_qnorm p q (ptn_reindex σ f) = ptn_qnorm p q f := by
  unfold ptn_qnorm ptn_qnormPow
  congr 2
  rw [show (fun y => |ptn_reindex σ f y| ^ q) = ptn_reindex σ (fun x => |f x| ^ q) from rfl,
      ptn_expect_reindex]


theorem ptn_kop_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (σ : κ ≃ ι) (p ρ : ℝ)
    (f : ConfigSpace ι → ℝ) :
    ptn_kop p ρ (ptn_reindex σ f) = ptn_reindex σ (ptn_kop p ρ f) := by
  funext y
  unfold ptn_kop ptn_reindex ptn_kernel
  symm
  apply Fintype.sum_equiv (ptn_cubeEquiv σ)
  intro w
  unfold ptn_cubeEquiv
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp, Equiv.symm_symm, id_eq]
  congr 1
  · rw [← Equiv.prod_comp σ (fun i : ι => ptn_kbit p ρ (y (σ.symm i)) (w i))]
    apply Finset.prod_congr rfl
    intro j _
    simp only [Equiv.symm_apply_apply]
  · congr 1; funext i; rw [Equiv.apply_symm_apply]




theorem ptn_lowDegreeWeight {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (f : ConfigSpace ι → ℝ) :
    (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2)
      ≤ (ptn_qnorm p q f) ^ 2 := by
  set σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with hσ
  
  have hfin := ptn_lowDegreeWeight_fin hp0 hp1 h0 h1 hq1 hq2 hρsq (Fintype.card ι)
    (ptn_reindex σ f)
  
  have hL : (∑ S : Finset (Fin (Fintype.card ι)), (ρ ^ S.card) ^ 2 * (ptn_coeff p (ptn_reindex σ f) S) ^ 2)
      = ∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2 := by
    rw [← ptn_noiseOp_l2sq hp0 hp1, ← ptn_noiseOp_l2sq hp0 hp1,
        ← ptn_kop_eq_noiseOp hp0 hp1, ← ptn_kop_eq_noiseOp hp0 hp1,
        ptn_kop_reindex σ p ρ f]
    rw [show (fun ω => (ptn_reindex σ (ptn_kop p ρ f) ω) ^ 2)
        = ptn_reindex σ (fun x => (ptn_kop p ρ f x) ^ 2) from rfl, ptn_expect_reindex]
  rw [hL, ptn_qnorm_reindex σ p q f] at hfin
  exact hfin




noncomputable def ptn_deriv (f : ConfigSpace ι → ℝ) (e : ι) : ConfigSpace ι → ℝ :=
  fun ω => f (StatMech.setOpen e ω) - f (StatMech.setClosed e ω)



theorem ptn_qnormPow_deriv {p q : ℝ} (hq : 0 < q) (φ : ConfigSpace ι → Bool) (e : ι) :
    ptn_qnormPow p q (ptn_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e)
      = OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
  unfold ptn_qnormPow OSSS.infl ptn_deriv
  congr 1; funext ω
  simp only
  by_cases hO : φ (StatMech.setOpen e ω) <;> by_cases hC : φ (StatMech.setClosed e ω) <;>
    simp [hO, hC, Real.one_rpow, Real.zero_rpow (ne_of_gt hq)]



theorem ptn_qnorm_deriv_sq {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ConfigSpace ι → Bool) (e : ι) :
    (ptn_qnorm p q (ptn_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e)) ^ 2
      = (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
  unfold ptn_qnorm
  rw [ptn_qnormPow_deriv hq φ e]
  set Ie := OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e with hIe
  have hIenn : 0 ≤ Ie := by
    rw [hIe]; exact OSSS.infl_nonneg (bernoulliWeight_isProbWeight hp0.le hp1.le) _ e
  rw [show (Ie ^ (1 / q)) ^ 2 = (Ie ^ (1 / q)) ^ (2:ℝ) from by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]]
  rw [← Real.rpow_mul hIenn]
  congr 1; field_simp




theorem ptn_kop_deriv_l2sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : ℝ) (f : ConfigSpace ι → ℝ)
    (e : ι) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun x => (ptn_kop p ρ (ptn_deriv f e) x) ^ 2)
      = ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p f S / ptn_sigma p) ^ 2 := by
  
  have heq : ptn_deriv f e
      = fun x => ∑ S ∈ univ.filter (fun S => e ∈ S),
          (ptn_coeff p f S / ptn_sigma p) * ptn_pchar p (S.erase e) x := by
    funext ω; exact ptn_deriv_fourier hp0 hp1 f e ω
  
  rw [heq]
  have hkop : ptn_kop p ρ (fun x => ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ptn_coeff p f S / ptn_sigma p) * ptn_pchar p (S.erase e) x)
      = fun x => ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        ((ptn_coeff p f S / ptn_sigma p) * ρ ^ (S.erase e).card) * ptn_pchar p (S.erase e) x := by
    rw [ptn_kop_finsetSum]
    funext x
    apply Finset.sum_congr rfl
    intro S _
    rw [ptn_kop_const_mul p ρ (ptn_coeff p f S / ptn_sigma p) (ptn_pchar p (S.erase e))]
    change (ptn_coeff p f S / ptn_sigma p) * ptn_kop p ρ (ptn_pchar p (S.erase e)) x = _
    rw [ptn_kop_pchar_apply hp0 hp1]; ring
  rw [hkop]
  rw [ptn_expect_sum_pchar_sq hp0 hp1 _ (fun S => (ptn_coeff p f S / ptn_sigma p) * ρ ^ (S.erase e).card)
      (fun S => S.erase e) (ptn_erase_injOn e)]
  apply Finset.sum_congr rfl
  intro S _; ring









theorem ptn_perCoord_hc {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (φ : ConfigSpace ι → Bool) (e : ι) :
    (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S
          / ptn_sigma p) ^ 2)
      ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  have hldw := ptn_lowDegreeWeight hp0 hp1 h0 h1 hq1 hq2 hρsq (ptn_deriv f e)
  
  rw [show (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p (ptn_deriv f e) S) ^ 2)
      = OSSS.expect (OSSS.bernoulliWeight p) (fun x => (ptn_kop p ρ (ptn_deriv f e) x) ^ 2) from by
        rw [ptn_kop_eq_noiseOp hp0 hp1, ptn_noiseOp_l2sq hp0 hp1]] at hldw
  rw [ptn_kop_deriv_l2sq hp0 hp1] at hldw
  rw [ptn_qnorm_deriv_sq hp0 hp1 (by linarith : (0:ℝ) < q)] at hldw
  exact hldw







theorem ptn_summed_hc {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (φ : ConfigSpace ι → Bool) :
    (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ ∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
  set σ2 := (ptn_sigma p) ^ 2 with hσ2
  set cc := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hcc
  have hσ2pos : 0 < σ2 := by rw [hσ2]; exact pow_pos (ptn_sigma_pos hp0 hp1) 2
  
  have hper : ∀ e : ι,
      (1 / σ2) * ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ρ ^ (S.erase e).card) ^ 2 * cc S
        ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
    intro e
    have h := ptn_perCoord_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ e
    refine le_trans (le_of_eq ?_) h
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [hcc, div_pow, one_div, hσ2]; ring
  refine le_trans ?_ (Finset.sum_le_sum (fun e _ => hper e))
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  
  apply le_of_eq
  symm
  have hinner : ∀ e : ι, (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * cc S)
      = ∑ S : Finset ι, (if e ∈ S then (ρ ^ (S.card - 1)) ^ 2 * cc S else 0) := by
    intro e
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases he : e ∈ S
    · rw [if_pos he, if_pos he, Finset.card_erase_of_mem he]
    · rw [if_neg he, if_neg he]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]



theorem ptn_cap_sum [Nonempty ι] {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (φ : ConfigSpace ι → Bool) :
    (∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p)
        (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q))
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1)
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set θ := 2 / q with hθdef
  have hθ1 : 1 ≤ θ := by rw [hθdef, le_div_iff₀ (by linarith)]; linarith
  have hprob := bernoulliWeight_isProbWeight (E := ι) hp0.le hp1.le
  have hterm : ∀ e : ι, (OSSS.infl (OSSS.bernoulliWeight p) f e) ^ θ
      ≤ δ ^ (θ - 1) * (OSSS.infl (OSSS.bernoulliWeight p) f e) :=
    fun e => bph_cap_term _ _ _ (kkl_infl_nonneg hprob f e) (kkl_infl_le_maxInfl _ f e) hθ1
  calc (∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p) f e) ^ θ)
      ≤ ∑ e : ι, δ ^ (θ - 1) * (OSSS.infl (OSSS.bernoulliWeight p) f e) :=
        Finset.sum_le_sum (fun e _ => hterm e)
    _ = δ ^ (θ - 1) * totalInfl (OSSS.bernoulliWeight p) f := by
        rw [← Finset.mul_sum]
        rfl







theorem ptn_capped_hc [Nonempty ι] {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (φ : ConfigSpace ι → Bool) :
    (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1)
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  le_trans (ptn_summed_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ) (ptn_cap_sum hp0 hp1 hq1 hq2 φ)



































def ptn_RhoOptimise (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
    (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ q' : ℝ, 1 ≤ q' → q' ≤ 2 → ρ ^ 2 = (q' - 1) * 4 * p * (1 - p) →
        (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1)
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) →
      2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
          * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
        ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)





theorem ptn_rhoOptimise_hyp_holds {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ q' : ℝ, 1 ≤ q' → q' ≤ 2 → ρ ^ 2 = (q' - 1) * 4 * p * (1 - p) →
      (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  intro ρ h0 h1 q' hq1 hq2 hρsq
  exact ptn_capped_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ





theorem ptn_kklHC_of_rhoOptimise {q : ℝ} (H : ptn_RhoOptimise q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1) :
    KKLHypercontractive p 2 := by
  have hp0 : 0 < p := by have := hp.1; linarith
  intro E _ _ _ φ
  exact H p hp hp1 φ (ptn_rhoOptimise_hyp_holds hp0 hp1 φ)





theorem ptn_PBiasedHC_of_rhoOptimise {q : ℝ} (hq : q ≤ 1) (H : ptn_RhoOptimise q) :
    kpb_PBiasedHC q :=
  fun p hp => ptn_kklHC_of_rhoOptimise H hp (by have := hp.2; linarith)





theorem ptn_rhoOptimise_c0 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    (0 : ℝ) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  rw [zero_mul, zero_mul]
  exact kkl_totalInfl_nonneg (bernoulliWeight_isProbWeight hp0 hp1) _








theorem ptn_residue_noncirc {q : ℝ} (H : ptn_RhoOptimise q) {p : ℝ}
    (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  ptn_kklHC_of_rhoOptimise H hp hp1 φ






theorem ptn_sharpThreshold_of_rhoOptimise {q : ℝ} (hq1 : q ≤ 1) (H : ptn_RhoOptimise q)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {v₀ L : ℝ} (hq : (1 : ℝ) / 2 ≤ q) (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
    1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A :=
  kpb_sharpThreshold A hA hq hv0 hL hhalf (ptn_PBiasedHC_of_rhoOptimise hq1 H) hvar hLL'

end StatMech.Probability
