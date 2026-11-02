/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section
namespace MetaMathlibExt

private theorem tsum_int_eq_sum_range_tsum_mul_add (f : ℤ → ℂ) (hf : Summable f) (P : ℕ)
    (hP : 0 < P) :
    ∑' (n : ℤ), f n = ∑ r ∈ Finset.range P, ∑' (m : ℤ), f (m * (P : ℤ) + (r : ℤ)) := by
  have hP' : NeZero P := NeZero.of_pos hP
  have hsym : Summable (fun p : ℤ × Fin P => f ((Int.divModEquiv P).symm p)) :=
    (Equiv.summable_iff (Int.divModEquiv P).symm).mpr hf
  have h1 : (∑' (p : ℤ × Fin P), f ((Int.divModEquiv P).symm p)) = ∑' (n : ℤ), f n :=
    Equiv.tsum_eq (Int.divModEquiv P).symm f
  rw [← h1]
  have h2 : (∑' (p : ℤ × Fin P), f ((Int.divModEquiv P).symm p))
      = ∑' (q : Fin P × ℤ), f ((Int.divModEquiv P).symm ((Equiv.prodComm (Fin P) ℤ) q)) := by
    exact (Equiv.tsum_eq (Equiv.prodComm (Fin P) ℤ) _).symm
  rw [h2]
  have hsum : Summable (fun q : Fin P × ℤ => f
      ((Int.divModEquiv P).symm ((Equiv.prodComm (Fin P) ℤ) q))) :=
    (Equiv.summable_iff (Equiv.prodComm (Fin P) ℤ)).mpr hsym
  rw [hsum.tsum_prod]
  simp only [Equiv.prodComm_apply, Prod.swap, Int.divModEquiv_symm_apply]
  rw [tsum_fintype]
  rw [Fin.sum_univ_eq_sum_range (fun n => ∑' (m : ℤ), f (m * (P : ℤ) + ((n : ℤ)))) P]

private theorem summable_mul_cexp_neg_pi_mul_sq (c : ℤ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1)
    (t : ℂ) (ht : 0 < t.re) :
    Summable (fun n : ℤ => c n * Complex.exp (-(Real.pi : ℂ) * t * (n : ℂ) ^ 2)) := by
  have hI : (Complex.I * t).im = t.re := by simp [Complex.mul_im]
  have hsum : Summable (fun n : ℤ => jacobiTheta₂_term n 0 (Complex.I * t)) := by
    rw [summable_jacobiTheta₂_term_iff]
    rw [hI]; exact ht
  have hbound : Summable (fun n : ℤ => ‖jacobiTheta₂_term n 0 (Complex.I * t)‖) :=
    hsum.norm
  apply Summable.of_norm_bounded hbound
  intro n
  have heq : Complex.exp (-(Real.pi : ℂ) * t * (n : ℂ) ^ 2)
      = jacobiTheta₂_term n 0 (Complex.I * t) := by
    unfold jacobiTheta₂_term
    congr 1
    simp only [mul_zero]
    linear_combination (-(Real.pi : ℂ) * t * (n : ℂ) ^ 2) * Complex.I_sq
  rw [heq]
  calc ‖c n * jacobiTheta₂_term n 0 (Complex.I * t)‖
      = ‖c n‖ * ‖jacobiTheta₂_term n 0 (Complex.I * t)‖ := norm_mul _ _
    _ ≤ 1 * ‖jacobiTheta₂_term n 0 (Complex.I * t)‖ := by
        apply mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)
    _ = ‖jacobiTheta₂_term n 0 (Complex.I * t)‖ := one_mul _

private theorem ls_c1_periodic (p q : ℕ) (hp : 1 ≤ p) (n : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((((n + (p : ℤ)) : ℤ) : ℂ) ^ 2 * (q : ℂ) / (p : ℂ)))
    = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n : ℂ)) ^ 2 * (q : ℂ) / (p : ℂ))) := by
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : p ≠ 0)
  rw [Complex.exp_eq_exp_iff_exists_int]
  use (2 * n * (q : ℤ) + (p : ℤ) * (q : ℤ))
  push_cast
  field_simp
  ring

private theorem ls_c1_norm (p q : ℕ) (n : ℤ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n : ℂ)) ^ 2 * (q : ℂ) / (p : ℂ)))‖ ≤ 1 := by
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (((n : ℂ)) ^ 2 * (q : ℂ) / (p : ℂ))).re = 0 := by
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.I_re, Complex.I_im, Complex.intCast_im, Complex.intCast_re,
      Complex.natCast_im, Complex.natCast_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [Complex.norm_exp, hre]
  simp

private theorem ls_c2_periodic (p q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I *
        (((((n + ((2 * q : ℕ) : ℤ))) : ℤ) : ℂ) ^ 2 * (p : ℂ) / (2 * (q : ℂ))))
    = Complex.exp (-(Real.pi : ℂ) * Complex.I * (((n : ℂ)) ^ 2 * (p : ℂ) / (2 * (q : ℂ)))) := by
  have hq0 : (q : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : q ≠ 0)
  rw [Complex.exp_eq_exp_iff_exists_int]
  use (-(n * (p : ℤ) + (p : ℤ) * (q : ℤ)))
  push_cast
  field_simp
  ring

private theorem ls_c2_norm (p q : ℕ) (n : ℤ) :
    ‖Complex.exp (-(Real.pi : ℂ) * Complex.I * (((n : ℂ)) ^ 2 * (p : ℂ) / (2 * (q : ℂ))))‖ ≤ 1 := by
  have hre : (-(Real.pi : ℂ) * Complex.I * (((n : ℂ)) ^ 2 * (p : ℂ) / (2 * (q : ℂ)))).re = 0 := by
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.I_re, Complex.I_im, Complex.intCast_im, Complex.intCast_re,
      Complex.natCast_im, Complex.natCast_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [Complex.norm_exp, hre]
  simp

private theorem ls_a_re (p q : ℕ) (s : ℝ) :
    (((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)).re = s⁻¹ := by
  simp [Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.I_re, Complex.I_im, Complex.natCast_im, Complex.natCast_re,
    Complex.ofReal_re, Complex.inv_re]

private theorem ls_w_re (p q : ℕ) (hp : 1 ≤ p) (s : ℝ) :
    ((4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ))).re
      = 4 * (q : ℝ) ^ 2 * s / (p : ℝ) ^ 2 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.add_re, Complex.I_re, Complex.I_im,
    Complex.natCast_re, Complex.ofReal_re]
  field_simp

private theorem ls_key_inv (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (s : ℝ) (hs : 0 < s) :
    (1 : ℂ) / (((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ))
    = Complex.I * (p : ℂ) / (2 * (q : ℂ))
      + 1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ)) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  set u : ℂ := (p : ℂ) - 2 * Complex.I * (q : ℂ) * (s : ℂ) with hu_def
  have ha_eq : (((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) = u / ((p : ℂ) * (s : ℂ)) := by
    rw [hu_def]; field_simp
  have hIu : Complex.I * u = 2 * (q : ℂ) * (s : ℂ) + Complex.I * (p : ℂ) := by
    rw [hu_def]
    linear_combination (-2 * (q : ℂ) * (s : ℂ)) * Complex.I_sq
  have hw_eq : (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ))
      = 2 * (q : ℂ) * (Complex.I * u) / (p : ℂ) ^ 2 := by
    rw [hIu]; field_simp; ring
  have hu : u ≠ 0 := by
    intro h
    have hzero : (((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) = 0 := by
      rw [ha_eq, h]; simp
    have hre : (((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)).re = s⁻¹ := by
      simp [Complex.mul_re, Complex.mul_im, Complex.div_re,
        Complex.I_re, Complex.I_im, Complex.natCast_im, Complex.natCast_re,
        Complex.ofReal_re, Complex.inv_re]
    have hre0 : (((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)).re = 0 := by
      rw [hzero]; simp
    rw [hre] at hre0
    exact (inv_ne_zero (ne_of_gt hs)) hre0
  rw [ha_eq, hw_eq]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2q : (2 : ℂ) * (q : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hq0
  have hp2 : (p : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hp0
  have hIu0 : Complex.I * u ≠ 0 := mul_ne_zero hI hu
  field_simp
  linear_combination (-(p : ℂ) + 2 * (s : ℂ) * (q : ℂ) * Complex.I) * Complex.I_sq

private theorem ls_inv_re1 (p : ℕ) (hp : 1 ≤ p) (s : ℝ) (hs : 0 < s) :
    (1 / ((p : ℂ) ^ 2 * ((s : ℂ))⁻¹)).re = s / (p : ℝ) ^ 2 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  simp [pow_two, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im,
    Complex.natCast_re, Complex.ofReal_re]
  field_simp

private theorem ls_residue_poisson (P : ℕ) (hP : 0 < P) (r : ℤ) (t : ℂ) (ht : 0 < t.re) :
    ((P : ℂ)^2 * t) ^ ((1/2 : ℂ)) * ∑' (m : ℤ), Complex.exp
        (-(Real.pi : ℂ) * t * (((m : ℂ) * (P : ℂ) + (r : ℂ))^2))
    = ∑' (k : ℤ), Complex.exp (-(Real.pi : ℂ) * (1 / (((P : ℂ)^2 * t))) * (k : ℂ)^2) * Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (r : ℂ) / (P : ℂ)) := by
  have hP0 : (P : ℂ) ≠ 0 := by exact_mod_cast (by omega : P ≠ 0)
  have hP2 : ((P : ℂ)^2) ≠ 0 := pow_ne_zero 2 hP0
  have ht0 : t ≠ 0 := by
    intro h; rw [h] at ht; simp at ht
  have hA0 : ((P : ℂ)^2 * t) ≠ 0 := mul_ne_zero hP2 ht0
  have hAre : 0 < (((P : ℂ)^2 * t)).re := by
    have hcast : (((P : ℂ)^2 * t)).re = ((P : ℝ)^2) * t.re := by
      simp [pow_two, Complex.mul_re, Complex.natCast_re, Complex.mul_im]
    rw [hcast]
    apply mul_pos _ ht
    positivity
  have hPoisson := Complex.tsum_exp_neg_quadratic (a := ((P:ℂ)^2 * t)) hAre (-((P:ℂ) * t * (r:ℂ)))
  have hsplit : (fun m : ℤ => Complex.exp (-(Real.pi : ℂ) * t * (((m : ℂ) * (P : ℂ) + (r : ℂ))^2)))
      = (fun m : ℤ => Complex.exp (-(Real.pi : ℂ) * ((P:ℂ)^2 * t) * (m:ℂ)^2 + 2 * (Real.pi:ℂ) *
          (-((P:ℂ)*t*(r:ℂ))) * (m:ℂ)) * Complex.exp (-(Real.pi:ℂ) * t * (r:ℂ)^2)) := by
    funext m
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hsplit, tsum_mul_right] at *
  rw [hPoisson]
  have hcp : ((P:ℂ)^2 * t) ^ ((1/2:ℂ)) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left; exact hA0
  have hcancel : ((P:ℂ)^2 * t) ^ ((1/2:ℂ)) * (1 / (((P:ℂ)^2 * t) ^ ((1/2:ℂ)))) = 1 := by
    field_simp
  have hpush : (∑' (n : ℤ), Complex.exp
      (-(Real.pi:ℂ) / ((P:ℂ)^2 * t) * (↑n + Complex.I * -((P:ℂ) * t * ↑r)) ^ 2)) * Complex.exp
          (-(Real.pi:ℂ) * t * (r:ℂ)^2)
      = ∑' (n : ℤ), (Complex.exp (-(Real.pi:ℂ) / ((P:ℂ)^2 * t) *
          (↑n + Complex.I * -((P:ℂ) * t * ↑r)) ^ 2) * Complex.exp
              (-(Real.pi:ℂ) * t * (r:ℂ)^2)) := by
    rw [tsum_mul_right]
  have hterm : ∀ k : ℤ, Complex.exp
      (-(Real.pi:ℂ) / ((P:ℂ)^2 * t) * ((k:ℂ) + Complex.I * -((P:ℂ) * t * (r:ℂ))) ^ 2) * Complex.exp
          (-(Real.pi:ℂ) * t * (r:ℂ)^2)
      = Complex.exp (-(Real.pi : ℂ) * (1 / (((P : ℂ)^2 * t))) * (k : ℂ)^2) * Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (r : ℂ) / (P : ℂ)) := by
    intro k
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    field_simp
    linear_combination (-((P:ℂ)^2 * t^2 * (r:ℂ)^2)) * Complex.I_sq
  calc ((P:ℂ)^2 * t) ^ ((1/2:ℂ)) *
      ((1 / (((P:ℂ)^2 * t) ^ ((1/2:ℂ))) *
          (∑' (n : ℤ), Complex.exp (-(Real.pi:ℂ) / ((P:ℂ)^2 * t) *
              (↑n + Complex.I * -((P:ℂ) * t * ↑r)) ^ 2))) * Complex.exp
                  (-(Real.pi:ℂ) * t * (r:ℂ)^2))
      = (((P:ℂ)^2 * t) ^ ((1/2:ℂ)) * (1 / (((P:ℂ)^2 * t) ^ ((1/2:ℂ))))) *
          ((∑' (n : ℤ), Complex.exp (-(Real.pi:ℂ) / ((P:ℂ)^2 * t) *
              (↑n + Complex.I * -((P:ℂ) * t * ↑r)) ^ 2)) * Complex.exp
                  (-(Real.pi:ℂ) * t * (r:ℂ)^2)) := by ring
    _ = (∑' (n : ℤ), Complex.exp (-(Real.pi:ℂ) / ((P:ℂ)^2 * t) *
        (↑n + Complex.I * -((P:ℂ) * t * ↑r)) ^ 2)) * Complex.exp
            (-(Real.pi:ℂ) * t * (r:ℂ)^2) := by rw [hcancel, one_mul]
    _ = ∑' (k : ℤ), Complex.exp (-(Real.pi : ℂ) * (1 / (((P : ℂ)^2 * t))) * (k : ℂ)^2) * Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (r : ℂ) / (P : ℂ)) := by
        rw [hpush]
        apply tsum_congr hterm

private theorem ls_cusp_limit {α : Type*} {l : Filter α} (W : α → ℂ)
    (hW : Filter.Tendsto (fun x => (W x).re) l Filter.atTop)
    (g : ℤ → ℂ) (hg1 : ∀ k, ‖g k‖ ≤ 1) (hg0 : g 0 = 1) :
    Filter.Tendsto (fun x => ∑' (k : ℤ), Complex.exp (-(Real.pi : ℂ) * W x * (k : ℂ)^2) * g k) l
        (nhds 1) := by
  have hIsum : Summable (fun k : ℤ => jacobiTheta₂_term k 0 Complex.I) := by
    rw [summable_jacobiTheta₂_term_iff]
    simp
  have hbound : Summable (fun k : ℤ => Real.exp (-Real.pi * ((k : ℝ))^2)) := by
    have h := hIsum.norm
    simpa [norm_jacobiTheta₂_term] using h
  have hnorm : ∀ (x : α) (k : ℤ), ‖Complex.exp (-(Real.pi : ℂ) * W x * (k : ℂ)^2)‖ = Real.exp
      (-Real.pi * ((k:ℝ))^2 * (W x).re) := by
    intro x k
    rw [Complex.norm_exp]
    congr 1
    have hk2re : (((k : ℂ)^2 : ℂ)).re = ((k : ℝ))^2 := by
      simp [pow_two, Complex.intCast_re, Complex.intCast_im]
    have hk2im : (((k : ℂ)^2 : ℂ)).im = 0 := by
      simp [pow_two, Complex.mul_im, Complex.intCast_re, Complex.intCast_im]
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hpt : ∀ k : ℤ, Filter.Tendsto (fun x => Complex.exp (-(Real.pi : ℂ) * W x * (k : ℂ)^2) * g k)
      l (nhds (if k = 0 then 1 else 0)) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp only [ite_true]
      have heq : (fun x => Complex.exp (-(Real.pi : ℂ) * W x * ((0 : ℤ) : ℂ)^2) * g 0) = fun _ =>
          (1:ℂ) := by
        funext x
        simp [hg0]
      rw [heq]
      exact tendsto_const_nhds
    · simp only [hk, ite_false]
      apply (tendsto_zero_iff_norm_tendsto_zero).mpr
      have hkr : ((k : ℝ)) ≠ 0 := by exact_mod_cast hk
      have hneg : -Real.pi * ((k:ℝ))^2 < 0 := by
        apply mul_neg_of_neg_of_pos
        · exact neg_lt_zero.mpr Real.pi_pos
        · positivity
      have harg : Filter.Tendsto (fun x => -Real.pi * ((k:ℝ))^2 * (W x).re) l Filter.atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg hneg hW
      have hexp : Filter.Tendsto (fun x => Real.exp (-Real.pi * ((k:ℝ))^2 * (W x).re)) l (nhds 0) :=
        Real.tendsto_exp_atBot.comp harg
      refine squeeze_zero (fun x => norm_nonneg _) (fun x => ?_) hexp
      calc ‖Complex.exp (-(Real.pi : ℂ) * W x * (k : ℂ)^2) * g k‖
          = ‖Complex.exp (-(Real.pi : ℂ) * W x * (k : ℂ)^2)‖ * ‖g k‖ := norm_mul _ _
        _ ≤ ‖Complex.exp (-(Real.pi : ℂ) * W x * (k : ℂ)^2)‖ * 1 :=
            mul_le_mul_of_nonneg_left (hg1 k) (norm_nonneg _)
        _ = Real.exp (-Real.pi * ((k:ℝ))^2 * (W x).re) := by rw [hnorm, mul_one]
  have hdom : ∀ᶠ (x : α) in l, ∀ (k : ℤ), ‖Complex.exp (-(Real.pi : ℂ) * W x * (k : ℂ)^2) * g k‖ ≤
      Real.exp (-Real.pi * ((k:ℝ))^2) := by
    have hev := hW.eventually_ge_atTop 1
    filter_upwards [hev] with x hx k
    calc ‖Complex.exp (-(Real.pi : ℂ) * W x * (k : ℂ)^2) * g k‖
        = ‖Complex.exp (-(Real.pi : ℂ) * W x * (k : ℂ)^2)‖ * ‖g k‖ := norm_mul _ _
      _ ≤ ‖Complex.exp (-(Real.pi : ℂ) * W x * (k : ℂ)^2)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hg1 k) (norm_nonneg _)
      _ = Real.exp (-Real.pi * ((k:ℝ))^2 * (W x).re) := by rw [hnorm, mul_one]
      _ ≤ Real.exp (-Real.pi * ((k:ℝ))^2 * 1) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonpos_left hx
          nlinarith [Real.pi_pos, sq_nonneg ((k:ℝ))]
      _ = Real.exp (-Real.pi * ((k:ℝ))^2) := by ring_nf
  have hlim := tendsto_tsum_of_dominated_convergence hbound hpt hdom
  have hsum1 : (∑' (k : ℤ), (if k = 0 then (1:ℂ) else 0)) = 1 := by
    simp
  simpa [hsum1] using hlim

private theorem ls_normalized_residue {α : Type*} {l : Filter α} (P : ℕ) (hP : 0 < P) (r : ℤ)
    (t : α → ℂ)
    (ht : Filter.Tendsto (fun x => (1 / (((P : ℂ) ^ 2 * t x))).re) l Filter.atTop) :
    Filter.Tendsto (fun x => (((P : ℂ)^2 * t x) ^ ((1/2 : ℂ))) * ∑' (m : ℤ), Complex.exp
        (-(Real.pi : ℂ) * t x * (((m : ℂ) * (P : ℂ) + (r : ℂ))^2))) l (nhds 1) := by
  have hev0 := ht.eventually_gt_atTop 0
  have hret : ∀ᶠ x in l, 0 < (t x).re := by
    filter_upwards [hev0] with x hx
    set Y : ℂ := (P:ℂ)^2 * t x with hY
    have h1Y : (1 / Y) ≠ 0 := by
      intro h
      rw [h] at hx
      simp at hx
    have hY0 : Y ≠ 0 := by
      intro h
      rw [h] at h1Y
      simp at h1Y
    have hYre : 0 < Y.re := by
      have hinv : (1 / Y).re = Y.re / Complex.normSq Y := by
        rw [one_div, Complex.inv_re]
      have hns : 0 < Complex.normSq Y := Complex.normSq_pos.mpr hY0
      have hpos := mul_pos hx hns
      rwa [hinv, div_mul_cancel₀ _ (ne_of_gt hns)] at hpos
    have hYre2 : Y.re = ((P:ℝ)^2) * (t x).re := by
      simp [hY, pow_two, Complex.mul_re, Complex.natCast_re, Complex.mul_im]
    rw [hYre2] at hYre
    exact (pos_of_mul_pos_right hYre (sq_nonneg _))
  have hg1 : ∀ k : ℤ, ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (r : ℂ) / (P : ℂ))‖ ≤
      1 := by
    intro k
    have hre : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (r : ℂ) / (P : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.div_re,
        Complex.I_re, Complex.I_im, Complex.intCast_im, Complex.intCast_re,
        Complex.natCast_im, Complex.natCast_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [Complex.norm_exp, hre]
    simp
  have hg0 : (fun k : ℤ => Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (r : ℂ) / (P : ℂ))) 0 = 1 := by
    simp
  have hN4 := ls_cusp_limit (fun x => 1 / (((P : ℂ)^2 * t x))) ht
      (fun k : ℤ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (r : ℂ) / (P : ℂ))) hg1
          hg0
  apply Filter.Tendsto.congr' _ hN4
  filter_upwards [hret] with x hx
  exact (ls_residue_poisson P hP r (t x) hx).symm
private theorem ls_normalized_periodic {α : Type*} {l : Filter α} (P : ℕ) (hP : 0 < P) (c : ℤ → ℂ)
    (hper : Function.Periodic c ((P : ℤ))) (hbd : ∀ n, ‖c n‖ ≤ 1) (t : α → ℂ)
    (ht : Filter.Tendsto (fun x => (1 / (((P : ℂ) ^ 2 * t x))).re) l Filter.atTop) :
    Filter.Tendsto (fun x => (((P : ℂ)^2 * t x) ^ ((1/2 : ℂ))) * ∑' (n : ℤ), c n * Complex.exp
        (-(Real.pi : ℂ) * t x * (n : ℂ)^2)) l (nhds (∑ r ∈ Finset.range P, c ((r : ℤ)))) := by
  have hev0 := ht.eventually_gt_atTop 0
  have hret : ∀ᶠ x in l, 0 < (t x).re := by
    filter_upwards [hev0] with x hx
    set Y : ℂ := (P:ℂ)^2 * t x with hY
    have h1Y : (1 / Y) ≠ 0 := by
      intro h
      rw [h] at hx
      simp at hx
    have hY0 : Y ≠ 0 := by
      intro h
      rw [h] at h1Y
      simp at h1Y
    have hYre : 0 < Y.re := by
      have hinv : (1 / Y).re = Y.re / Complex.normSq Y := by
        rw [one_div, Complex.inv_re]
      have hns : 0 < Complex.normSq Y := Complex.normSq_pos.mpr hY0
      have hpos := mul_pos hx hns
      rwa [hinv, div_mul_cancel₀ _ (ne_of_gt hns)] at hpos
    have hYre2 : Y.re = ((P:ℝ)^2) * (t x).re := by
      simp [hY, pow_two, Complex.mul_re, Complex.natCast_re, Complex.mul_im]
    rw [hYre2] at hYre
    exact (pos_of_mul_pos_right hYre (sq_nonneg _))
  have hcr : ∀ (r m : ℤ), c (m * (P:ℤ) + r) = c r := by
    intro r m
    have h := (hper.int_mul m) r
    simpa [add_comm] using h
  have hcast : ∀ (m r : ℤ), (((m * (P:ℤ) + r : ℤ)) : ℂ) = (m:ℂ) * (P:ℂ) + (r:ℂ) := by
    intro m r
    push_cast
    ring
  have hsplit : ∀ᶠ x in l, (∑' (n : ℤ), c n * Complex.exp (-(Real.pi : ℂ) * t x * (n : ℂ)^2))
      = ∑ r ∈ Finset.range P, c ((r:ℤ)) *
          (∑' (m : ℤ), Complex.exp (-(Real.pi : ℂ) * t x *
              (((m : ℂ) * (P : ℂ) + ((r:ℤ) : ℂ))^2))) := by
    filter_upwards [hret] with x hx
    have hsumm : Summable (fun n : ℤ => c n * Complex.exp (-(Real.pi : ℂ) * t x * (n : ℂ)^2)) :=
      summable_mul_cexp_neg_pi_mul_sq c hbd (t x) hx
    have h1 := tsum_int_eq_sum_range_tsum_mul_add
        (fun n : ℤ => c n * Complex.exp (-(Real.pi : ℂ) * t x * (n : ℂ)^2)) hsumm P hP
    rw [h1]
    apply Finset.sum_congr rfl
    intro r hr
    have hinner : (∑' (m : ℤ), c (m * (P:ℤ) + ((r:ℕ) : ℤ)) * Complex.exp
        (-(Real.pi : ℂ) * t x * (((m * (P:ℤ) + ((r:ℕ):ℤ) : ℤ)) : ℂ)^2))
        = c ((r:ℤ)) * (∑' (m : ℤ), Complex.exp
            (-(Real.pi : ℂ) * t x * (((m : ℂ) * (P : ℂ) + ((r:ℤ) : ℂ))^2))) := by
      have hterm : ∀ m : ℤ, c (m * (P:ℤ) + ((r:ℕ) : ℤ)) * Complex.exp
          (-(Real.pi : ℂ) * t x * (((m * (P:ℤ) + ((r:ℕ):ℤ) : ℤ)) : ℂ)^2)
          = c ((r:ℤ)) * Complex.exp (-(Real.pi : ℂ) * t x *
              (((m : ℂ) * (P : ℂ) + ((r:ℤ) : ℂ))^2)) := by
        intro m
        have e1 : c (m * (P:ℤ) + ((r:ℕ) : ℤ)) = c ((r:ℤ)) := by
          have := hcr ((r:ℤ)) m
          simpa using this
        have e2 : ((((m * (P:ℤ) + ((r:ℕ):ℤ) : ℤ)) : ℂ)) = ((m : ℂ) * (P : ℂ) + ((r:ℤ) : ℂ)) := by
          have := hcast m ((r:ℤ))
          simp
        rw [e1, e2]
      rw [tsum_congr hterm, tsum_mul_left]
    simpa using hinner
  have hlim : Filter.Tendsto (fun x => ∑ r ∈ Finset.range P, c ((r:ℤ)) *
      ((((P : ℂ)^2 * t x) ^ ((1/2 : ℂ))) * ∑' (m : ℤ), Complex.exp
          (-(Real.pi : ℂ) * t x * (((m : ℂ) * (P : ℂ) + ((r:ℤ) : ℂ))^2)))) l
              (nhds (∑ r ∈ Finset.range P, c ((r:ℤ)))) := by
    apply tendsto_finsetSum
    intro r hr
    have h5 := ls_normalized_residue P hP ((r:ℤ)) t ht
    have hc := Filter.Tendsto.const_mul (c ((r:ℤ))) h5
    simpa [mul_one] using hc
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [hret, hsplit] with x hx hs
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

private theorem ls_a_ne (p q : ℕ) (s : ℝ) (hs : 0 < s) :
    ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) : ℂ) ≠ 0 := by
  have hre : ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) : ℂ).re = s⁻¹ := by
    simp [Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.I_re, Complex.I_im, Complex.natCast_im, Complex.natCast_re,
      Complex.ofReal_re, Complex.inv_re]
  intro h
  have h0 : ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) : ℂ).re = 0 := by
    rw [h]; simp
  rw [hre] at h0
  exact (inv_ne_zero (ne_of_gt hs)) h0

private theorem ls_w_ne (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (s : ℝ) (hs : 0 < s) :
    ((4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ)) : ℂ) ≠ 0 := by
  have hre : ((4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ)) : ℂ).re
      = 4 * (q : ℝ) ^ 2 * s / (p : ℝ) ^ 2 := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.add_re, Complex.I_re, Complex.I_im,
      Complex.natCast_re, Complex.ofReal_re]
    field_simp
  have hpos : (0:ℝ) < 4 * (q : ℝ) ^ 2 * s / (p : ℝ) ^ 2 := by
    have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have hpR : (p:ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    positivity
  intro h
  have h0 : ((4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ)) : ℂ).re =
      0 := by
    rw [h]; simp
  rw [hre] at h0
  linarith

private theorem ls_inv_w_re (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (s : ℝ) (hs : 0 < s) :
    (0:ℝ) < (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) /
        (p : ℂ))).re := by
  have hw := ls_w_ne p q hp hq s hs
  have hre : ((4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ)) : ℂ).re
      = 4 * (q : ℝ) ^ 2 * s / (p : ℝ) ^ 2 := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.add_re, Complex.I_re, Complex.I_im,
      Complex.natCast_re, Complex.ofReal_re]
    field_simp
  rw [one_div, Complex.inv_re]
  apply div_pos _ (Complex.normSq_pos.mpr hw)
  rw [hre]
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hpR : (p:ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  positivity

private theorem ls_exp_id (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (s : ℝ) (hs : 0 < s) (n : ℤ) :
    -(Real.pi : ℂ) / ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ))) * (n : ℂ)^2
    = -(Real.pi : ℂ) * Complex.I * ((n : ℂ)^2 * (p:ℂ) / (2 * (q:ℂ)))
      + (-(Real.pi : ℂ) * (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) /
          (p : ℂ))) * (n : ℂ)^2) := by
  have hkey := ls_key_inv p q hp hq s hs
  have ha := ls_a_ne p q s hs
  have hw := ls_w_ne p q hp hq s hs
  have : (1:ℂ) / ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)))
      = Complex.I * (p : ℂ) / (2 * (q : ℂ))
        + 1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ)) := hkey
  have hrewrite : -(Real.pi : ℂ) / ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)))
      = -(Real.pi:ℂ) * (Complex.I * (p : ℂ) / (2 * (q : ℂ)))
        + (-(Real.pi:ℂ) * (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) /
            (p : ℂ)))) := by
    have h1 : -(Real.pi : ℂ) / ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)))
        = -(Real.pi:ℂ) * ((1:ℂ) / ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)))) := by
      ring
    rw [h1, hkey]
    ring
  rw [hrewrite]
  ring

private theorem ls_inv_re5 (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (s : ℝ) (hs : 0 < s) :
    (1 / ((((2 * q : ℕ)) : ℂ)^2 * (1 /
        (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ))))).re = s /
            (p : ℝ) ^ 2 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have hw := ls_w_ne p q hp hq s hs
  have h2q : (((2 * q : ℕ)) : ℂ) = 2 * (q : ℂ) := by norm_cast
  have hre := ls_w_re p q hp s
  rw [h2q]
  have hstep : (1:ℂ) / ((2 * (q:ℂ))^2 *
      (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ))))
      = (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ)) /
          (2 * (q:ℂ))^2 := by
    field_simp
  rw [hstep]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

private theorem ls_aY (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (s : ℝ) (hs : 0 < s) :
    ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ))) *
        ((((2 * q : ℕ)) : ℂ)^2 * (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I *
            (q : ℂ) / (p : ℂ))))
    = (((2 * (p:ℝ) * (q:ℝ) / s : ℝ)) : ℂ) * (-Complex.I) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have hw := ls_w_ne p q hp hq s hs
  have h2q : (((2 * q : ℕ)) : ℂ) = 2 * (q : ℂ) := by norm_cast
  have hR : ((((2 * (p:ℝ) * (q:ℝ) / s : ℝ))) : ℂ) = 2 * (p:ℂ) * (q:ℂ) / (s:ℂ) := by
    push_cast
    ring
  rw [h2q, hR]
  field_simp
  have hden : ((s:ℂ) * (q:ℂ) * 4 + 2 * Complex.I * (p:ℂ)) ≠ 0 := by
    intro h
    apply hw
    have e : (4 * (q:ℂ)^2 * (s:ℂ) / (p:ℂ)^2 + 2 * Complex.I * (q:ℂ) / (p:ℂ))
        = (q:ℂ) * ((s:ℂ) * (q:ℂ) * 4 + 2 * Complex.I * (p:ℂ)) / (p:ℂ)^2 := by
      field_simp
    rw [e, h]
    simp
  rw [div_eq_iff hden]
  linear_combination 2 * (p:ℂ) * Complex.I_sq

private theorem ls_twisted (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (s : ℝ) (hs : 0 < s) :
    ∑' (n : ℤ), Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (q : ℂ) / (p : ℂ))) *
        Complex.exp (-(Real.pi : ℂ) * ((s : ℂ))⁻¹ * (n : ℂ)^2)
    = 1 / ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) ^ ((1/2 : ℂ))) * ∑' (n : ℤ),
        Complex.exp (-(Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (p : ℂ) / (2 * (q : ℂ)))) *
            Complex.exp (-(Real.pi : ℂ) * (1 /
                (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ))) *
                    (n : ℂ)^2) := by
  have hare : (0:ℝ) < ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ))).re := by
    rw [ls_a_re p q s]
    exact inv_pos.mpr hs
  have hP := Complex.tsum_exp_neg_mul_int_sq
      (a := ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)))) hare
  have hL : ∀ n : ℤ, Complex.exp (-(Real.pi : ℂ) *
      ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ))) * (n : ℂ)^2)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (q : ℂ) / (p : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((s : ℂ))⁻¹ * (n : ℂ)^2) := by
    intro n
    rw [← Complex.exp_add]
    congr 1
    ring
  have hR : ∀ n : ℤ, Complex.exp (-(Real.pi : ℂ) /
      ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ))) * (n : ℂ)^2)
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (p : ℂ) / (2 * (q : ℂ)))) *
          Complex.exp (-(Real.pi : ℂ) * (1 /
              (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ))) *
                  (n : ℂ)^2) := by
    intro n
    rw [← Complex.exp_add]
    congr 1
    exact ls_exp_id p q hp hq s hs n
  rw [tsum_congr hL, tsum_congr hR] at hP
  exact hP

private theorem cpow_mul_of_arg {x y z : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (harg : x.arg + y.arg ∈ Set.Ioc (-Real.pi) Real.pi) :
    (x * y) ^ z = x ^ z * y ^ z := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hx hy),
    Complex.cpow_def_of_ne_zero hx, Complex.cpow_def_of_ne_zero hy,
    Complex.log_mul hx hy harg, ← Complex.exp_add]
  congr 1
  ring

private theorem ls_sqrt_const (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (s : ℝ) (hs : 0 < s) :
    ((((p : ℂ)^2 * ((s : ℂ))⁻¹) ^ ((1/2 : ℂ))))
    = ((((Real.sqrt (p : ℝ) : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I / 4) /
        ((Real.sqrt (2 * (q : ℝ)) : ℂ))))
      * ((((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) ^ ((1/2 : ℂ))))
        * (((((2 * q : ℕ)) : ℂ)^2 * (1 /
            (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ)))) ^
                ((1/2 : ℂ)))) := by
  have ha := ls_a_ne p q s hs
  have hw := ls_w_ne p q hp hq s hs
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hRpos : (0:ℝ) < 2 * (p:ℝ) * (q:ℝ) / s :=
    div_pos (mul_pos (mul_pos two_pos hpR) hqR) hs
  have hRnn : (0:ℝ) ≤ 2 * (p:ℝ) * (q:ℝ) / s := le_of_lt hRpos
  have hR1nn : (0:ℝ) ≤ (p:ℝ)^2 / s :=
    div_nonneg (sq_nonneg _) (le_of_lt hs)
  have hRne : ((((2 * (p:ℝ) * (q:ℝ) / s : ℝ))) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hRpos)
  have hnegI : (-Complex.I) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have h12 : ((1/2 : ℂ)) = ((((1/2 : ℝ))) : ℂ) := by simp
  have hbase : ((p:ℂ)^2 * (s:ℂ)⁻¹) = ((((p:ℝ)^2 / s : ℝ)) : ℂ) := by
    push_cast
    ring
  have hare_pos : (0:ℝ) < ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ))).re := by
    rw [ls_a_re p q s]
    exact inv_pos.mpr hs
  have hC2re : (((((2 * q : ℕ)) : ℂ)^2)).re = ((((2 * q : ℕ)) : ℝ))^2 := by
    rw [pow_two, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  have hC2im : (((((2 * q : ℕ)) : ℂ)^2)).im = 0 := by
    rw [pow_two, Complex.mul_im, Complex.natCast_re, Complex.natCast_im]
    ring
  have hC2pos : (0:ℝ) < ((((2 * q : ℕ)) : ℝ))^2 :=
    pow_pos (by exact_mod_cast (by omega : 0 < 2 * q)) 2
  have hYre_pos : (0:ℝ) < (((((2 * q : ℕ)) : ℂ)^2 *
      (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ))))).re := by
    rw [Complex.mul_re, hC2re, hC2im, zero_mul, sub_zero]
    exact mul_pos hC2pos (ls_inv_w_re p q hp hq s hs)
  have haA : |(((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)))).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hare_pos)
  have haY : |(((((2 * q : ℕ)) : ℂ)^2 *
      (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ))))).arg| <
          Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hYre_pos)
  have hargAY : ((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ))).arg
      + (((((2 * q : ℕ)) : ℂ)^2 * (1 /
          (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ))))).arg
      ∈ Set.Ioc (-Real.pi) Real.pi := by
    have h1 := abs_lt.mp haA
    have h2 := abs_lt.mp haY
    refine ⟨?_, ?_⟩ <;> linarith
  have hargR : ((((2 * (p:ℝ) * (q:ℝ) / s : ℝ))) : ℂ).arg + (-Complex.I).arg
      ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hRnn, Complex.arg_neg_I]
    refine ⟨?_, ?_⟩ <;> linarith [Real.pi_pos]
  have hofR : (((((2 * (p:ℝ) * (q:ℝ) / s : ℝ))) : ℂ) ^ ((1/2:ℂ)))
      = ((((Real.sqrt (2 * (p:ℝ) * (q:ℝ) / s) : ℝ))) : ℂ) := by
    rw [h12, ← Complex.ofReal_cpow hRnn, ← Real.sqrt_eq_rpow]
  have hLHS : ((((p:ℂ)^2 * (s:ℂ)⁻¹) ^ ((1/2:ℂ)))) = ((((Real.sqrt ((p:ℝ)^2 / s) : ℝ))) : ℂ) := by
    rw [hbase, h12, ← Complex.ofReal_cpow hR1nn, ← Real.sqrt_eq_rpow]
  have hEN : Complex.exp ((Real.pi : ℂ) * Complex.I / 4)
      * ((-Complex.I) ^ ((1/2:ℂ))) = 1 := by
    rw [Complex.cpow_def_of_ne_zero hnegI, Complex.log_neg_I, ← Complex.exp_add]
    have hexp : ((Real.pi : ℂ) * Complex.I / 4) + (-(((Real.pi:ℂ)) / 2) * Complex.I * (1/2)) =
        0 := by
      ring
    rw [hexp, Complex.exp_zero]
  have hCne : (((((2 * q : ℕ)) : ℂ)^2)) ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast (by omega : (2 * q : ℕ) ≠ 0))
  have hY : (((((2 * q : ℕ)) : ℂ)^2 *
      (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ))))) ≠
          0 := by
    apply mul_ne_zero hCne
    rw [one_div]
    exact inv_ne_zero hw
  have hAY : (((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) ^ ((1/2 : ℂ))))
      * ((((((2 * q : ℕ)) : ℂ)^2 * (1 /
          (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ)))) ^
              ((1/2 : ℂ))))
      = ((((Real.sqrt (2 * (p:ℝ) * (q:ℝ) / s) : ℝ))) : ℂ) * ((-Complex.I) ^ ((1/2:ℂ))) := by
    rw [← cpow_mul_of_arg ha hY hargAY, ls_aY p q hp hq s hs,
      cpow_mul_of_arg hRne hnegI hargR, hofR]
  have hreal : Real.sqrt (p:ℝ) * Real.sqrt (2 * (p:ℝ) * (q:ℝ) / s) / Real.sqrt (2 * (q:ℝ))
      = Real.sqrt ((p:ℝ)^2 / s) := by
    have e1 : Real.sqrt (p:ℝ) * Real.sqrt (2 * (p:ℝ) * (q:ℝ) / s)
        = Real.sqrt ((p:ℝ) * (2 * (p:ℝ) * (q:ℝ) / s)) :=
      (Real.sqrt_mul (le_of_lt hpR) _).symm
    have e2 : Real.sqrt ((p:ℝ) * (2 * (p:ℝ) * (q:ℝ) / s)) / Real.sqrt (2 * (q:ℝ))
        = Real.sqrt (((p:ℝ) * (2 * (p:ℝ) * (q:ℝ) / s)) / (2 * (q:ℝ))) :=
      (Real.sqrt_div (mul_nonneg (le_of_lt hpR) (le_of_lt hRpos)) _).symm
    rw [e1, e2]
    congr 1
    field_simp
  have hC : ((Real.sqrt (p:ℝ) : ℂ)) * ((((Real.sqrt (2 * (p:ℝ) * (q:ℝ) / s) : ℝ))) : ℂ) /
      ((Real.sqrt (2 * (q:ℝ)) : ℂ))
      = ((((Real.sqrt ((p:ℝ)^2 / s) : ℝ))) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_div]
    exact congrArg Complex.ofReal hreal
  have hring : (((Real.sqrt (p:ℝ) : ℂ)) * Complex.exp ((Real.pi:ℂ) * Complex.I / 4) /
      ((Real.sqrt (2 * (q:ℝ)) : ℂ)))
      * (((((Real.sqrt (2 * (p:ℝ) * (q:ℝ) / s) : ℝ))) : ℂ) * ((-Complex.I) ^ ((1/2:ℂ))))
      = (((Real.sqrt (p:ℝ) : ℂ)) * ((((Real.sqrt (2 * (p:ℝ) * (q:ℝ) / s) : ℝ))) : ℂ) /
          ((Real.sqrt (2 * (q:ℝ)) : ℂ)))
        * (Complex.exp ((Real.pi:ℂ) * Complex.I / 4) * ((-Complex.I) ^ ((1/2:ℂ)))) := by
      ring
  rw [hAY, hring, hEN, hC, hLHS, mul_one]

/-- **Landsberg–Schaar relation.** For all positive integers $p$ and $q$,
$$
\frac{1}{\sqrt{p}} \sum_{n=0}^{p-1} \exp\left(\frac{2 \pi i n^2 q}{p}\right) =
\frac{e^{\pi i / 4}}{\sqrt{2q}} \sum_{n=0}^{2q-1} \exp\left(-\frac{\pi i n^2 p}{2q}\right).
$$

Source: https://en.wikipedia.org/wiki/Landsberg%E2%80%93Schaar_relation (landsberg-schaar-s1);
proves `Wanted` entry `landsberg_schaar`.
-/
theorem landsberg_schaar (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
  (1 / (Real.sqrt (p : ℝ) : ℂ)) * ∑ n ∈ Finset.range p, Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (q : ℂ) / (p : ℂ))) =
    (Complex.exp ((Real.pi : ℂ) * Complex.I / 4) / (Real.sqrt (2 * (q : ℝ)) : ℂ)) * ∑ n ∈
      Finset.range (2 * q), Complex.exp
      (-(Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (p : ℂ) / (2 * (q : ℂ)))) := by
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hpp : (0:ℝ) < (p:ℝ)^2 := pow_pos hpR 2
  have hsp : Filter.Tendsto (fun s : ℝ => s / (p:ℝ)^2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hpp Filter.tendsto_id
  have ht1 : Filter.Tendsto (fun s : ℝ => (1 / (((p:ℂ)^2 * ((s:ℂ))⁻¹))).re) Filter.atTop
      Filter.atTop := by
    apply Filter.Tendsto.congr' _ hsp
    filter_upwards [Filter.eventually_gt_atTop 0] with s hs
    exact (ls_inv_re1 p hp s hs).symm
  have ht2 : Filter.Tendsto (fun s : ℝ =>
      (1 / (((((2 * q : ℕ)) : ℂ)^2 * (1 /
          (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ)))))).re)
              Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.congr' _ hsp
    filter_upwards [Filter.eventually_gt_atTop 0] with s hs
    exact (ls_inv_re5 p q hp hq s hs).symm
  have hA := ls_normalized_periodic p (by omega)
    (fun n : ℤ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((n : ℂ) ^ 2 * (q : ℂ) / (p : ℂ))))
    (fun n => ls_c1_periodic p q hp n) (ls_c1_norm p q)
    (fun s : ℝ => ((s : ℂ))⁻¹) ht1
  have hA' : Filter.Tendsto (fun s : ℝ => ((((p : ℂ)^2 * ((s : ℂ))⁻¹) ^ ((1/2 : ℂ)))) * ∑' (n : ℤ),
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (q : ℂ) / (p : ℂ))) * Complex.exp
          (-(Real.pi : ℂ) * ((s : ℂ))⁻¹ * (n : ℂ)^2)) Filter.atTop
              (nhds (∑ r ∈ Finset.range p, Complex.exp
                  (2 * (Real.pi : ℂ) * Complex.I *
                      (((((r : ℕ) : ℤ)) : ℂ) ^ 2 * (q : ℂ) / (p : ℂ))))) := hA
  have hB := ls_normalized_periodic (2 * q) (by omega)
    (fun n : ℤ => Complex.exp (-(Real.pi : ℂ) * Complex.I *
      ((n : ℂ) ^ 2 * (p : ℂ) / (2 * (q : ℂ)))))
    (fun n => ls_c2_periodic p q hq n) (ls_c2_norm p q)
    (fun s : ℝ => 1 / ((4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 +
      2 * Complex.I * (q : ℂ) / (p : ℂ)))) ht2
  have hB' : Filter.Tendsto (fun s : ℝ =>
      (((((2 * q : ℕ)) : ℂ)^2 * (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I *
          (q : ℂ) / (p : ℂ)))) ^ ((1/2 : ℂ))) * ∑' (n : ℤ), Complex.exp
              (-(Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (p : ℂ) / (2 * (q : ℂ)))) * Complex.exp
                  (-(Real.pi : ℂ) * (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I *
                      (q : ℂ) / (p : ℂ))) * (n : ℂ)^2)) Filter.atTop
                          (nhds (∑ r ∈ Finset.range (2 * q), Complex.exp
                              (-(Real.pi : ℂ) * Complex.I * (((((r : ℕ) : ℤ)) : ℂ) ^ 2 * (p : ℂ) /
                                  (2 * (q : ℂ)))))) := hB
  have hAeq : (fun s : ℝ => ((((p : ℂ)^2 * ((s : ℂ))⁻¹) ^ ((1/2 : ℂ)))) * ∑' (n : ℤ), Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (q : ℂ) / (p : ℂ))) * Complex.exp
          (-(Real.pi : ℂ) * ((s : ℂ))⁻¹ * (n : ℂ)^2)) =ᶠ[Filter.atTop]
              (fun s : ℝ => ((((Real.sqrt (p : ℝ) : ℂ)) * Complex.exp
                  ((Real.pi : ℂ) * Complex.I / 4) / ((Real.sqrt (2 * (q : ℝ)) : ℂ)))) *
                      ((((((2 * q : ℕ)) : ℂ)^2 * (1 /
                          (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) /
                              (p : ℂ)))) ^ ((1/2 : ℂ))) * ∑' (n : ℤ), Complex.exp
                                  (-(Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (p : ℂ) /
                                      (2 * (q : ℂ)))) * Complex.exp (-(Real.pi : ℂ) *
                                          (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 *
                                              Complex.I * (q : ℂ) / (p : ℂ))) * (n : ℂ)^2))) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with s hs
    rw [ls_twisted p q hp hq s hs, ls_sqrt_const p q hp hq s hs]
    have hane : (((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) ^ ((1/2 : ℂ)))) ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]
      left
      exact ls_a_ne p q s hs
    have hcancel : (((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) ^ ((1/2 : ℂ)))) *
        (1 / (((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) ^ ((1/2 : ℂ))))) = 1 :=
            mul_one_div_cancel hane
    have e : (((((Real.sqrt (p : ℝ) : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I / 4) /
        ((Real.sqrt (2 * (q : ℝ)) : ℂ)))) *
            ((((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) ^ ((1/2 : ℂ)))) *
                (((((2 * q : ℕ)) : ℂ)^2 * (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 *
                    Complex.I * (q : ℂ) / (p : ℂ)))) ^ ((1/2 : ℂ))))) *
                        ((1 / (((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) ^ ((1/2 : ℂ))))) *
                            ∑' (n : ℤ), Complex.exp (-(Real.pi : ℂ) * Complex.I *
                                ((n : ℂ) ^ 2 * (p : ℂ) / (2 * (q : ℂ)))) * Complex.exp
                                    (-(Real.pi : ℂ) * (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2
                                        + 2 * Complex.I * (q : ℂ) / (p : ℂ))) * (n : ℂ)^2)) =
                                            (((((Real.sqrt (p : ℝ) : ℂ)) * Complex.exp
                                                ((Real.pi : ℂ) * Complex.I / 4) /
                                                    ((Real.sqrt (2 * (q : ℝ)) : ℂ)))) *
                                                        ((((((2 * q : ℕ)) : ℂ)^2 * (1 /
                                                            (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2
                                                                + 2 * Complex.I * (q : ℂ) / (p :
                                                                    ℂ)))) ^ ((1/2 : ℂ))) *
                        ∑' (n : ℤ), Complex.exp
                          (-(Real.pi : ℂ) * Complex.I *
                            ((n : ℂ) ^ 2 * (p : ℂ) / (2 * (q : ℂ)))) *
                          Complex.exp (-(Real.pi : ℂ) *
                            (1 / (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 +
                              2 * Complex.I * (q : ℂ) / (p : ℂ))) * (n : ℂ)^2))) *
                        ((((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) / (p : ℂ)) ^
                            ((1/2 : ℂ)))) *
                          (1 / (((((s : ℂ))⁻¹ - 2 * Complex.I * (q : ℂ) /
                            (p : ℂ)) ^ ((1/2 : ℂ)))))) := by
      ring
    rw [e, hcancel, mul_one]
  have hAK : Filter.Tendsto (fun s : ℝ =>
      ((((Real.sqrt (p : ℝ) : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I / 4) /
          ((Real.sqrt (2 * (q : ℝ)) : ℂ)))) *
              ((((((2 * q : ℕ)) : ℂ)^2 * (1 /
                  (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ) / (p : ℂ)))) ^
                      ((1/2 : ℂ))) * ∑' (n : ℤ), Complex.exp
                          (-(Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (p : ℂ) / (2 * (q : ℂ)))) *
                              Complex.exp (-(Real.pi : ℂ) * (1 /
                                  (4 * (q : ℂ) ^ 2 * (s : ℂ) / (p : ℂ) ^ 2 + 2 * Complex.I * (q : ℂ)
                                      / (p : ℂ))) * (n : ℂ)^2))) Filter.atTop
                                          (nhds (((((Real.sqrt (p : ℝ) : ℂ)) * Complex.exp
                                              ((Real.pi : ℂ) * Complex.I / 4) /
                                                  ((Real.sqrt (2 * (q : ℝ)) : ℂ)))) *
                                                      (∑ r ∈ Finset.range (2 * q), Complex.exp
                                                          (-(Real.pi : ℂ) * Complex.I * (((((r : ℕ)
                                                              : ℤ)) : ℂ) ^ 2 * (p : ℂ) / (2 *
                                                                  (q : ℂ))))))) :=
    Filter.Tendsto.const_mul _ hB'
  have hSeq : (∑ r ∈ Finset.range p, Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (((((r : ℕ) : ℤ)) : ℂ) ^ 2 * (q : ℂ) / (p : ℂ)))) =
          (((((Real.sqrt (p : ℝ) : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I / 4) /
              ((Real.sqrt (2 * (q : ℝ)) : ℂ)))) *
                  (∑ r ∈ Finset.range (2 * q), Complex.exp
                      (-(Real.pi : ℂ) * Complex.I * (((((r : ℕ) : ℤ)) : ℂ) ^ 2 * (p : ℂ) /
                          (2 * (q : ℂ)))))) :=
    tendsto_nhds_unique hA' (Filter.Tendsto.congr' hAeq.symm hAK)
  have hS1 : (∑ n ∈ Finset.range p, Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (q : ℂ) / (p : ℂ)))) =
          (∑ r ∈ Finset.range p, Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I *
                  (((((r : ℕ) : ℤ)) : ℂ) ^ 2 * (q : ℂ) / (p : ℂ)))) := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Int.cast_natCast]
  have hS2 : (∑ n ∈ Finset.range (2 * q), Complex.exp
      (-(Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (p : ℂ) / (2 * (q : ℂ))))) =
          (∑ r ∈ Finset.range (2 * q), Complex.exp
              (-(Real.pi : ℂ) * Complex.I * (((((r : ℕ) : ℤ)) : ℂ) ^ 2 * (p : ℂ) /
                  (2 * (q : ℂ))))) := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Int.cast_natCast]
  rw [hS1, hS2, hSeq]
  have hsp0 : ((Real.sqrt (p : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hpR)
  have hsq0 : ((Real.sqrt (2 * (q : ℝ)) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (mul_pos two_pos hqR))
  have e2 : (1 / (Real.sqrt (p : ℝ) : ℂ)) *
      ((((Real.sqrt (p : ℝ) : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I / 4) /
          ((Real.sqrt (2 * (q : ℝ)) : ℂ)))) =
              (Complex.exp ((Real.pi : ℂ) * Complex.I / 4) / (Real.sqrt (2 * (q : ℝ)) : ℂ)) := by
    field_simp
  have ef : (1 / (Real.sqrt (p : ℝ) : ℂ)) *
      (((((Real.sqrt (p : ℝ) : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I / 4) /
          ((Real.sqrt (2 * (q : ℝ)) : ℂ)))) *
              (∑ r ∈ Finset.range (2 * q), Complex.exp
                  (-(Real.pi : ℂ) * Complex.I * (((((r : ℕ) : ℤ)) : ℂ) ^ 2 * (p : ℂ) /
                      (2 * (q : ℂ)))))) = (((1 / (Real.sqrt (p : ℝ) : ℂ)) *
                          ((((Real.sqrt (p : ℝ) : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I / 4)
                              / ((Real.sqrt (2 * (q : ℝ)) : ℂ))))) *
                                  (∑ r ∈ Finset.range (2 * q), Complex.exp
                                      (-(Real.pi : ℂ) * Complex.I * (((((r : ℕ) : ℤ)) : ℂ) ^ 2 *
                                          (p : ℂ) / (2 * (q : ℂ)))))) := by
    ring
  rw [ef, e2]

end MetaMathlibExt
end
