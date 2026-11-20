/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Code.Probability.VectorTwoPoint
import Code.Probability.KKLInequality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open scoped BigOperators
open Finset

set_option linter.style.longLine false

namespace StatMech
namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]








def khc_sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem khc_sign_false : khc_sign false = 1 := rfl
@[simp] theorem khc_sign_true : khc_sign true = -1 := rfl


theorem khc_sign_sq (b : Bool) : khc_sign b * khc_sign b = 1 := by
  cases b <;> simp [khc_sign]


noncomputable def khc_walshChar (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ S, khc_sign (x i)

omit [Fintype ι] [DecidableEq ι] in

@[simp] theorem khc_walshChar_empty (x : ι → Bool) :
    khc_walshChar (∅ : Finset ι) x = 1 := by
  simp [khc_walshChar]

omit [Fintype ι] [DecidableEq ι] in

theorem khc_walshChar_sq (S : Finset ι) (x : ι → Bool) :
    (khc_walshChar S x) ^ 2 = 1 := by
  unfold khc_walshChar
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one (fun i _ => by rw [sq]; exact khc_sign_sq (x i))



theorem khc_walshChar_as_univ (S : Finset ι) (x : ι → Bool) :
    khc_walshChar S x = ∏ i : ι, (if i ∈ S then khc_sign (x i) else 1) := by
  unfold khc_walshChar; rw [Finset.prod_ite_mem, Finset.univ_inter]



theorem khc_walshChar_mul (S T : Finset ι) (x : ι → Bool) :
    khc_walshChar S x * khc_walshChar T x = khc_walshChar (symmDiff S T) x := by
  rw [khc_walshChar_as_univ, khc_walshChar_as_univ, khc_walshChar_as_univ,
      ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT, Finset.mem_symmDiff, khc_sign_sq]





theorem khc_uexp_walshChar (S : Finset ι) :
    bnt_uexp (khc_walshChar S) = if S = ∅ then 1 else 0 := by
  unfold bnt_uexp khc_walshChar
  have hchar : ∀ x : ι → Bool, (∏ i ∈ S, khc_sign (x i))
      = ∏ i : ι, (if i ∈ S then khc_sign (x i) else 1) := by
    intro x; rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp only [khc_sign] at hchar ⊢
  simp_rw [hchar]
  rw [← Fintype.prod_sum (fun (i : ι) (c : Bool) =>
    if i ∈ S then (if c then (-1 : ℝ) else 1) else 1)]
  have hfac : ∀ i : ι, (∑ c : Bool, if i ∈ S then (if c then (-1 : ℝ) else 1) else 1)
      = (if i ∈ S then 0 else 2) := by
    intro i; by_cases hi : i ∈ S <;> simp [hi]
  simp_rw [hfac]
  by_cases hS : S = ∅
  · subst hS
    simp only [Finset.notMem_empty, if_false, if_true]
    rw [Finset.prod_const, Finset.card_univ, div_self (by positivity)]
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), zero_div]




theorem khc_orthonormal (S T : Finset ι) :
    bnt_uexp (fun x => khc_walshChar S x * khc_walshChar T x) = if S = T then 1 else 0 := by
  simp_rw [khc_walshChar_mul]
  rw [khc_uexp_walshChar]
  by_cases h : S = T
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hsd
    exact h (symmDiff_eq_bot.mp (by simpa using hsd))



omit [DecidableEq ι] in



theorem khc_sum_walshChar_mul (x y : ι → Bool) :
    (∑ S : Finset ι, khc_walshChar S x * khc_walshChar S y)
      = if x = y then (2 ^ Fintype.card ι : ℝ) else 0 := by
  have hpt : ∀ S : Finset ι, khc_walshChar S x * khc_walshChar S y
      = ∏ i ∈ S, (khc_sign (x i) * khc_sign (y i)) := by
    intro S; unfold khc_walshChar; rw [← Finset.prod_mul_distrib]
  simp_rw [hpt]
  have hpow : (univ : Finset (Finset ι)) = (univ : Finset ι).powerset := by ext S; simp
  rw [hpow, ← Finset.prod_one_add]
  have hfac : ∀ i : ι, (1 + khc_sign (x i) * khc_sign (y i)) = if x i = y i then (2 : ℝ) else 0 := by
    intro i; cases hxi : x i <;> cases hyi : y i <;> simp [khc_sign] <;> norm_num
  simp_rw [hfac]
  by_cases hxy : x = y
  · subst hxy; simp only [if_true]; rw [Finset.prod_const, Finset.card_univ]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])


noncomputable def khc_fourierCoeff (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  bnt_uexp (fun x => f x * khc_walshChar S x)



theorem khc_fourier_expansion (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    (∑ S : Finset ι, khc_fourierCoeff f S * khc_walshChar S x) = f x := by
  calc (∑ S : Finset ι, khc_fourierCoeff f S * khc_walshChar S x)
      = ∑ S : Finset ι, (∑ y : ι → Bool, f y * khc_walshChar S y) / (2 ^ Fintype.card ι)
          * khc_walshChar S x := by
        unfold khc_fourierCoeff bnt_uexp; rfl
    _ = (∑ S : Finset ι, ∑ y : ι → Bool, f y * khc_walshChar S y * khc_walshChar S x)
          / (2 ^ Fintype.card ι) := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro S _
        rw [div_mul_eq_mul_div, Finset.sum_mul]
    _ = (∑ y : ι → Bool, f y * (∑ S : Finset ι, khc_walshChar S y * khc_walshChar S x))
          / (2 ^ Fintype.card ι) := by
        rw [Finset.sum_comm]; congr 1; apply Finset.sum_congr rfl; intro y _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _; ring
    _ = (∑ y : ι → Bool, f y * (if y = x then (2 ^ Fintype.card ι : ℝ) else 0))
          / (2 ^ Fintype.card ι) := by
        congr 1; apply Finset.sum_congr rfl; intro y _; rw [khc_sum_walshChar_mul]
    _ = f x := by
        rw [Finset.sum_eq_single x]
        · rw [if_pos rfl, mul_div_assoc, div_self (by positivity), mul_one]
        · intro y _ hy; rw [if_neg hy, mul_zero]
        · intro h; exact absurd (Finset.mem_univ x) h




theorem khc_uexp_finset_sum {κ : Type*} (s : Finset κ) (g : κ → (ι → Bool) → ℝ) :
    bnt_uexp (fun x => ∑ k ∈ s, g k x) = ∑ k ∈ s, bnt_uexp (g k) := by
  unfold bnt_uexp; simp_rw [Finset.sum_div]; rw [Finset.sum_comm]


theorem khc_uexp_const_mul (c : ℝ) (g : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => c * g x) = c * bnt_uexp g := by
  unfold bnt_uexp; rw [← Finset.mul_sum, mul_div_assoc]



theorem khc_uexp_fourier_mul (a b : Finset ι → ℝ) :
    bnt_uexp (fun x => (∑ S : Finset ι, a S * khc_walshChar S x)
        * (∑ T : Finset ι, b T * khc_walshChar T x))
      = ∑ S : Finset ι, a S * b S := by
  have hexp : (fun x => (∑ S : Finset ι, a S * khc_walshChar S x)
        * (∑ T : Finset ι, b T * khc_walshChar T x))
      = (fun x => ∑ S : Finset ι, ∑ T : Finset ι,
          (a S * b T) * (khc_walshChar S x * khc_walshChar T x)) := by
    funext x; rw [Finset.sum_mul_sum]; apply Finset.sum_congr rfl; intro S _
    apply Finset.sum_congr rfl; intro T _; ring
  rw [hexp, khc_uexp_finset_sum]
  apply Finset.sum_congr rfl; intro S _
  rw [khc_uexp_finset_sum]
  have hterm : ∀ T : Finset ι,
      bnt_uexp (fun x => a S * b T * (khc_walshChar S x * khc_walshChar T x))
        = a S * b T * (if S = T then 1 else 0) := by
    intro T
    rw [khc_uexp_const_mul (a S * b T) (fun x => khc_walshChar S x * khc_walshChar T x),
        khc_orthonormal]
  simp_rw [hterm]
  rw [Finset.sum_eq_single S]
  · rw [if_pos rfl, mul_one]
  · intro T _ hT; rw [if_neg (Ne.symm hT), mul_zero]
  · intro h; exact absurd (Finset.mem_univ S) h



theorem khc_parseval (f g : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => f x * g x)
      = ∑ S : Finset ι, khc_fourierCoeff f S * khc_fourierCoeff g S := by
  have hf : (fun x => f x * g x)
      = (fun x => (∑ S : Finset ι, khc_fourierCoeff f S * khc_walshChar S x)
          * (∑ T : Finset ι, khc_fourierCoeff g T * khc_walshChar T x)) := by
    funext x; rw [khc_fourier_expansion, khc_fourier_expansion]
  rw [hf, khc_uexp_fourier_mul]


theorem khc_parseval_sq (f : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => (f x) ^ 2) = ∑ S : Finset ι, (khc_fourierCoeff f S) ^ 2 := by
  have h := khc_parseval f f
  simp_rw [← sq] at h
  exact h








theorem khc_noiseOp_walshChar_apply (ρ : ℝ) (S : Finset ι) (x : ι → Bool) :
    bnt_noiseOp ρ (khc_walshChar S) x = ρ ^ S.card * khc_walshChar S x := by
  unfold bnt_noiseOp bnt_noiseKernel khc_walshChar
  have hchar : ∀ y : ι → Bool, (∏ i ∈ S, khc_sign (y i))
      = ∏ i : ι, (if i ∈ S then khc_sign (y i) else 1) := by
    intro y; rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [hchar]
  have hcomb : ∀ y : ι → Bool,
      (∏ i : ι, (if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2))
        * (∏ i : ι, (if i ∈ S then khc_sign (y i) else 1))
      = ∏ i : ι, ((if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2)
                  * (if i ∈ S then khc_sign (y i) else 1)) := by
    intro y; rw [← Finset.prod_mul_distrib]
  simp_rw [hcomb]
  rw [← Fintype.prod_sum (fun (i : ι) (c : Bool) =>
        (if x i = c then (1 + ρ) / 2 else (1 - ρ) / 2) * (if i ∈ S then khc_sign c else 1))]
  have hfac : ∀ i : ι,
      (∑ c : Bool, (if x i = c then (1 + ρ) / 2 else (1 - ρ) / 2) * (if i ∈ S then khc_sign c else 1))
        = (if i ∈ S then ρ * khc_sign (x i) else 1) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]; rw [Fintype.sum_bool]; cases (x i) <;> simp [khc_sign] <;> ring
    · simp only [hi, if_false, mul_one]; rw [Fintype.sum_bool]; cases (x i) <;> simp <;> ring
  simp_rw [hfac]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_ite_mem, Finset.univ_inter,
      Finset.prod_mul_distrib, Finset.prod_const]


theorem khc_noiseOp_walshChar (ρ : ℝ) (S : Finset ι) :
    bnt_noiseOp ρ (khc_walshChar S) = fun x => ρ ^ S.card * khc_walshChar S x := by
  funext x; exact khc_noiseOp_walshChar_apply ρ S x


theorem khc_noiseOp_finset_sum {κ : Type*} (ρ : ℝ) (s : Finset κ) (g : κ → (ι → Bool) → ℝ) :
    bnt_noiseOp ρ (fun x => ∑ k ∈ s, g k x) = fun x => ∑ k ∈ s, bnt_noiseOp ρ (g k) x := by
  funext x; unfold bnt_noiseOp; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]


theorem khc_noiseOp_const_mul (ρ c : ℝ) (g : (ι → Bool) → ℝ) :
    bnt_noiseOp ρ (fun x => c * g x) = fun x => c * bnt_noiseOp ρ g x := by
  funext x; unfold bnt_noiseOp; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro y _; ring



theorem khc_noiseOp_fourier (ρ : ℝ) (f : (ι → Bool) → ℝ) :
    bnt_noiseOp ρ f
      = fun x => ∑ S : Finset ι, (ρ ^ S.card * khc_fourierCoeff f S) * khc_walshChar S x := by
  have hf : f = (fun x => ∑ S : Finset ι, khc_fourierCoeff f S * khc_walshChar S x) := by
    funext x; rw [khc_fourier_expansion]
  conv_lhs => rw [hf]
  rw [khc_noiseOp_finset_sum]
  funext x
  simp_rw [khc_noiseOp_const_mul ρ (khc_fourierCoeff f _) (khc_walshChar _)]
  apply Finset.sum_congr rfl
  intro S _
  rw [khc_noiseOp_walshChar_apply]
  ring



theorem khc_noiseOp_l2sq (ρ : ℝ) (f : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => (bnt_noiseOp ρ f x) ^ 2)
      = ∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2 := by
  rw [khc_noiseOp_fourier]
  have h := khc_uexp_fourier_mul (fun S => ρ ^ S.card * khc_fourierCoeff f S)
      (fun S => ρ ^ S.card * khc_fourierCoeff f S)
  simp_rw [← sq] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro S _; ring













noncomputable def khc_reindex {κ : Type*} (e : κ ≃ ι) (f : (ι → Bool) → ℝ) :
    (κ → Bool) → ℝ :=
  fun y => f (fun i => y (e.symm i))


def khc_cubeEquiv {κ : Type*} (e : κ ≃ ι) : (ι → Bool) ≃ (κ → Bool) :=
  Equiv.arrowCongr e.symm (Equiv.refl Bool)


theorem khc_uexp_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (f : (ι → Bool) → ℝ) :
    bnt_uexp (khc_reindex e f) = bnt_uexp f := by
  unfold bnt_uexp khc_reindex
  rw [Fintype.card_congr e]
  congr 1
  symm
  apply Fintype.sum_equiv (khc_cubeEquiv e)
  intro x
  unfold khc_cubeEquiv
  congr 1
  funext i
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp,
    Equiv.symm_symm, id_eq, Equiv.apply_symm_apply]


theorem khc_qnorm_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (q : ℝ)
    (f : (ι → Bool) → ℝ) :
    bnt_qnorm q (khc_reindex e f) = bnt_qnorm q f := by
  unfold bnt_qnorm bnt_qnormPow
  congr 2
  rw [show (fun y => |khc_reindex e f y| ^ q) = khc_reindex e (fun x => |f x| ^ q) from rfl]
  rw [khc_uexp_reindex]


theorem khc_noiseOp_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (ρ : ℝ)
    (f : (ι → Bool) → ℝ) :
    bnt_noiseOp ρ (khc_reindex e f) = khc_reindex e (bnt_noiseOp ρ f) := by
  funext y
  unfold bnt_noiseOp khc_reindex bnt_noiseKernel
  symm
  apply Fintype.sum_equiv (khc_cubeEquiv e)
  intro w
  unfold khc_cubeEquiv
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp, Equiv.symm_symm, id_eq]
  congr 1
  · rw [← Equiv.prod_comp e (fun j => if (fun i => y (e.symm i)) j = w j then (1 + ρ) / 2 else (1 - ρ) / 2)]
    apply Finset.prod_congr rfl
    intro i _; simp [Equiv.symm_apply_apply]
  · congr 1; funext j; simp [Equiv.apply_symm_apply]




theorem khc_hypercontractivity_general {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (g : (ι → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp ρ g) ≤ bnt_qnorm (1 + ρ ^ 2) g := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  have hHC := bnt_hypercontractivity (vtp_vectorTwoPoint h0 h1) (Fintype.card ι)
    (khc_reindex e.symm g)
  rw [khc_noiseOp_reindex e.symm ρ g, khc_qnorm_reindex e.symm 2 (bnt_noiseOp ρ g),
      khc_qnorm_reindex e.symm (1 + ρ ^ 2) g] at hHC
  exact hHC


















theorem khc_lowDegreeWeight_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (f : (ι → Bool) → ℝ) :
    (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2)
      ≤ (bnt_qnorm (1 + ρ ^ 2) f) ^ 2 := by
  
  have hhc : bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f :=
    khc_hypercontractivity_general h0 h1 f
  
  have hlhs : 0 ≤ bnt_qnorm 2 (bnt_noiseOp ρ f) := bnt_qnorm_nonneg 2 _
  have hsq : (bnt_qnorm 2 (bnt_noiseOp ρ f)) ^ 2 ≤ (bnt_qnorm (1 + ρ ^ 2) f) ^ 2 := by
    have hrhs : 0 ≤ bnt_qnorm (1 + ρ ^ 2) f := bnt_qnorm_nonneg _ _
    nlinarith [hhc, hlhs, hrhs]
  
  rw [vtp_qnorm2_sq, vtp_qnormPow2_eq_uexp_sq, khc_noiseOp_l2sq] at hsq
  exact hsq








theorem khc_lowDegreeWeight_fluct_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (f : (ι → Bool) → ℝ) :
    (∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2)
      ≤ (bnt_qnorm (1 + ρ ^ 2) f) ^ 2 - (khc_fourierCoeff f ∅) ^ 2 := by
  have hfull := khc_lowDegreeWeight_le h0 h1 f
  have hsplit : (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2)
      = (ρ ^ (∅ : Finset ι).card) ^ 2 * (khc_fourierCoeff f ∅) ^ 2
        + ∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2 := by
    rw [← Finset.add_sum_erase univ _ (Finset.mem_univ (∅ : Finset ι))]
  rw [hsplit] at hfull
  simp only [Finset.card_empty, pow_zero, one_pow, one_mul] at hfull
  linarith


















open StatMech.OSSS in
omit [DecidableEq ι] in

theorem khc_bernoulliWeight_half (ω : ConfigSpace ι) :
    OSSS.weight (OSSS.bernoulliWeight (1 / 2 : ℝ)) ω = 1 / (2 ^ Fintype.card ι) := by
  unfold OSSS.weight OSSS.bernoulliWeight
  have hfac : ∀ e : ι, (if ω e then (1 / 2 : ℝ) else 1 - 1 / 2) = 1 / 2 := by
    intro e; cases ω e <;> norm_num
  simp_rw [hfac]
  rw [Finset.prod_const, Finset.card_univ, div_pow, one_pow]

open StatMech.OSSS in

theorem khc_expect_half (g : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) g = bnt_uexp g := by
  unfold OSSS.expect bnt_uexp
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [khc_bernoulliWeight_half, one_div, div_eq_mul_inv, ← div_eq_mul_inv]
  ring


theorem khc_uexp_eq_coeff_empty (g : ConfigSpace ι → ℝ) :
    bnt_uexp g = khc_fourierCoeff g ∅ := by
  unfold khc_fourierCoeff
  congr 1; funext x; rw [khc_walshChar_empty, mul_one]

open StatMech.OSSS in


theorem khc_var_eq_fourierWeight (g : ConfigSpace ι → ℝ) :
    OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ)) g
      = ∑ S ∈ (univ.erase (∅ : Finset ι)), (khc_fourierCoeff g S) ^ 2 := by
  unfold OSSS.var OSSS.cov
  rw [khc_expect_half, khc_expect_half,
      show (fun ω => g ω * g ω) = (fun ω => (g ω) ^ 2) from by funext ω; ring,
      khc_parseval_sq, khc_uexp_eq_coeff_empty,
      ← Finset.add_sum_erase univ (fun S => (khc_fourierCoeff g S) ^ 2)
        (Finset.mem_univ (∅ : Finset ι))]
  ring



omit [Fintype ι] in


theorem khc_walshChar_setOpen_sub_setClosed (S : Finset ι) (e : ι) (ω : ConfigSpace ι) :
    khc_walshChar S (StatMech.setOpen e ω) - khc_walshChar S (StatMech.setClosed e ω)
      = if e ∈ S then (-2 : ℝ) * khc_walshChar (S.erase e) ω else 0 := by
  by_cases he : e ∈ S
  · rw [if_pos he]
    unfold khc_walshChar
    rw [← Finset.prod_erase_mul S _ he, ← Finset.prod_erase_mul S _ he]
    have hprodO : (∏ i ∈ S.erase e, khc_sign (StatMech.setOpen e ω i))
        = ∏ i ∈ S.erase e, khc_sign (ω i) := by
      apply Finset.prod_congr rfl
      intro i hi; rw [StatMech.setOpen_of_ne (Finset.ne_of_mem_erase hi)]
    have hprodC : (∏ i ∈ S.erase e, khc_sign (StatMech.setClosed e ω i))
        = ∏ i ∈ S.erase e, khc_sign (ω i) := by
      apply Finset.prod_congr rfl
      intro i hi; rw [StatMech.setClosed_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hprodO, hprodC, StatMech.setOpen_self, StatMech.setClosed_self]
    simp only [khc_sign_true, khc_sign_false]; ring
  · rw [if_neg he]
    unfold khc_walshChar
    have : (∏ i ∈ S, khc_sign (StatMech.setOpen e ω i))
        = ∏ i ∈ S, khc_sign (StatMech.setClosed e ω i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hie : i ≠ e := fun h => he (h ▸ hi)
      rw [StatMech.setOpen_of_ne hie, StatMech.setClosed_of_ne hie]
    rw [this, sub_self]



theorem khc_deriv_fourier (g : ConfigSpace ι → ℝ) (e : ι) (ω : ConfigSpace ι) :
    g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω)
      = ∑ S ∈ univ.filter (fun S => e ∈ S),
          ((-2 : ℝ) * khc_fourierCoeff g S) * khc_walshChar (S.erase e) ω := by
  have hO : g (StatMech.setOpen e ω)
      = ∑ S : Finset ι, khc_fourierCoeff g S * khc_walshChar S (StatMech.setOpen e ω) := by
    rw [khc_fourier_expansion]
  have hC : g (StatMech.setClosed e ω)
      = ∑ S : Finset ι, khc_fourierCoeff g S * khc_walshChar S (StatMech.setClosed e ω) := by
    rw [khc_fourier_expansion]
  rw [hO, hC, ← Finset.sum_sub_distrib]
  have hterm : ∀ S : Finset ι,
      khc_fourierCoeff g S * khc_walshChar S (StatMech.setOpen e ω)
        - khc_fourierCoeff g S * khc_walshChar S (StatMech.setClosed e ω)
        = if e ∈ S then ((-2 : ℝ) * khc_fourierCoeff g S) * khc_walshChar (S.erase e) ω else 0 := by
    intro S; rw [← mul_sub, khc_walshChar_setOpen_sub_setClosed]
    by_cases he : e ∈ S
    · rw [if_pos he, if_pos he]; ring
    · rw [if_neg he, if_neg he, mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_filter]



theorem khc_uexp_sum_walsh_sq (s : Finset (Finset ι)) (a : Finset ι → ℝ)
    (T : Finset ι → Finset ι) (hTinj : Set.InjOn T s) :
    bnt_uexp (fun x => (∑ S ∈ s, a S * khc_walshChar (T S) x) ^ 2)
      = ∑ S ∈ s, (a S) ^ 2 := by
  rw [show (fun x => (∑ S ∈ s, a S * khc_walshChar (T S) x) ^ 2)
      = (fun x => ∑ S ∈ s, ∑ U ∈ s,
          (a S * a U) * (khc_walshChar (T S) x * khc_walshChar (T U) x)) from ?_]
  · rw [khc_uexp_finset_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [khc_uexp_finset_sum]
    have hterm : ∀ U ∈ s,
        bnt_uexp (fun x => a S * a U * (khc_walshChar (T S) x * khc_walshChar (T U) x))
          = a S * a U * (if T S = T U then 1 else 0) := by
      intro U _; rw [khc_uexp_const_mul, khc_orthonormal]
    rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single_of_mem S hS]
    · rw [if_pos rfl, mul_one, sq]
    · intro U hU hUS
      have hne : T S ≠ T U := fun h => hUS (hTinj hU hS h.symm)
      rw [if_neg hne, mul_zero]
  · funext x; rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro S _
    apply Finset.sum_congr rfl; intro U _; ring


theorem khc_erase_injOn (e : ι) :
    Set.InjOn (fun S => Finset.erase S e) ↑(univ.filter (fun S : Finset ι => e ∈ S)) := by
  intro S hS U hU h
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hS hU
  simp only at h
  rw [← Finset.insert_erase hS, ← Finset.insert_erase hU, h]

omit [Fintype ι] in


theorem khc_abs_diff_indicator (φ : ConfigSpace ι → Bool) (e : ι) (ω : ConfigSpace ι) :
    |(fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω)
        - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)|
      = ((fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω)
        - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)) ^ 2 := by
  simp only
  by_cases hO : φ (StatMech.setOpen e ω) <;> by_cases hC : φ (StatMech.setClosed e ω) <;>
    simp [hO, hC]

open StatMech.OSSS in




theorem khc_infl_eq_fourierWeight (φ : ConfigSpace ι → Bool) (e : ι) :
    OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e
      = ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          4 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  set g := fun ω => if φ ω then (1 : ℝ) else 0 with hg
  unfold OSSS.infl
  have habs : (fun ω => |g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω)|)
      = (fun ω => (g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω)) ^ 2) := by
    funext ω; exact khc_abs_diff_indicator φ e ω
  rw [habs, khc_expect_half]
  have hd : (fun ω => (g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω)) ^ 2)
      = (fun ω => (∑ S ∈ univ.filter (fun S => e ∈ S),
          ((-2 : ℝ) * khc_fourierCoeff g S) * khc_walshChar (S.erase e) ω) ^ 2) := by
    funext ω; rw [khc_deriv_fourier g e ω]
  rw [hd, khc_uexp_sum_walsh_sq _ _ (fun S => S.erase e) (khc_erase_injOn e)]
  apply Finset.sum_congr rfl
  intro S _; ring

open StatMech.OSSS in



theorem khc_totalInfl_eq_fourierWeight (φ : ConfigSpace ι → Bool) :
    totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
      = ∑ S : Finset ι, 4 * (S.card : ℝ)
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  set c := fun S : Finset ι => (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  unfold totalInfl
  have hinfl : ∀ e : ι,
      OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e
        = ∑ S : Finset ι, (if e ∈ S then 4 * c S else 0) := by
    intro e; rw [khc_infl_eq_fourierWeight, Finset.sum_filter]
  simp_rw [hinfl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hc, nsmul_eq_mul]
  ring


































def khc_LogSobolevStep (c : ℝ) : Prop :=
  ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool),
    (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
        (∑ S : Finset E, (ρ ^ S.card) ^ 2
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          ≤ (bnt_qnorm (1 + ρ ^ 2) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2) →
      c * (∑ S ∈ (univ.erase (∅ : Finset E)),
            (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if φ ω then (1 : ℝ) else 0))
        ≤ ∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2






theorem khc_logSobolevStep_zero : khc_LogSobolevStep 0 := by
  intro E _ _ _ φ _
  rw [zero_mul, zero_mul]
  rw [← khc_totalInfl_eq_fourierWeight φ]
  exact kkl_totalInfl_nonneg
    (OSSS.bernoulliWeight_isProbWeight (by norm_num) (by norm_num)) _




















theorem khc_KKL {c : ℝ} (H : khc_LogSobolevStep c) :
    KKLHypercontractive (1 / 2 : ℝ) c := by
  intro E _ _ _ φ
  
  rw [show OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
        = ∑ S ∈ (univ.erase (∅ : Finset E)),
            (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      from khc_var_eq_fourierWeight _]
  rw [show totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
        = ∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      from khc_totalInfl_eq_fourierWeight _]
  
  exact H φ (fun ρ h0 h1 => khc_lowDegreeWeight_le h0 h1 _)

end Probability
end StatMech
