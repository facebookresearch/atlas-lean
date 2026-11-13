/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































import Mathlib
import Code.Ising.Pressure

open scoped BigOperators
open Finset

namespace StatMech

namespace Ising










theorem holder_logSumExp_step {ι : Type*} [Fintype ι] (c d : ι → ℝ) (x y a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (∑ i, Real.exp ((a * x + b * y) * c i + d i)) ≤
      (∑ i, Real.exp (x * c i + d i)) ^ a * (∑ i, Real.exp (y * c i + d i)) ^ b := by
  
  have hpq : Real.HolderConjugate (1 / a) (1 / b) := by
    refine ⟨?_, by positivity, by positivity⟩
    show (1 / a)⁻¹ + (1 / b)⁻¹ = (1 : ℝ)⁻¹
    rw [one_div, one_div, inv_inv, inv_inv, inv_one, hab]
  
  set f : ι → ℝ := fun i => Real.exp (x * c i + d i) ^ a with hf
  set g : ι → ℝ := fun i => Real.exp (y * c i + d i) ^ b with hg
  have hfnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ f i := fun i _ => by positivity
  have hgnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ g i := fun i _ => by positivity
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (s := (Finset.univ : Finset ι)) hpq hfnn hgnn
  
  have hfp : ∀ i, f i ^ (1 / a) = Real.exp (x * c i + d i) := fun i => by
    simp only [hf]
    rw [← Real.rpow_mul (Real.exp_pos _).le, mul_one_div, div_self ha.ne', Real.rpow_one]
  have hgq : ∀ i, g i ^ (1 / b) = Real.exp (y * c i + d i) := fun i => by
    simp only [hg]
    rw [← Real.rpow_mul (Real.exp_pos _).le, mul_one_div, div_self hb.ne', Real.rpow_one]
  
  have hfg : ∀ i, f i * g i = Real.exp ((a * x + b * y) * c i + d i) := fun i => by
    simp only [hf, hg]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _),
      ← Real.exp_add, Real.log_exp, Real.log_exp]
    congr 1
    have hd : d i = a * d i + b * d i := by rw [← add_mul, hab, one_mul]
    nlinarith [hd]
  simp only [hfp, hgq, one_div_one_div] at hH
  rw [Finset.sum_congr rfl (fun i _ => hfg i)] at hH
  exact hH












theorem cumulant_convexOn {ι : Type*} [Fintype ι] [Nonempty ι] (c d : ι → ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (∑ i, Real.exp (t * c i + d i))) := by
  refine ⟨convex_univ, ?_⟩
  rintro x - y - a b ha hb hab
  simp only [smul_eq_mul]
  have hSx_pos : 0 < ∑ i, Real.exp (x * c i + d i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hSy_pos : 0 < ∑ i, Real.exp (y * c i + d i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hSc_pos : 0 < ∑ i, Real.exp ((a * x + b * y) * c i + d i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  
  have hRHS : a * Real.log (∑ i, Real.exp (x * c i + d i))
      + b * Real.log (∑ i, Real.exp (y * c i + d i))
      = Real.log ((∑ i, Real.exp (x * c i + d i)) ^ a
          * (∑ i, Real.exp (y * c i + d i)) ^ b) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hSx_pos,
      Real.log_rpow hSy_pos]
  rw [hRHS]
  apply Real.log_le_log hSc_pos
  
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by rw [← hab, ← ha0]; ring
    subst hb1
    rw [← ha0]
    simp only [Real.rpow_zero, Real.rpow_one, one_mul, zero_mul, zero_add, le_refl]
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have ha1 : a = 1 := by rw [← hab, ← hb0]; ring
    subst ha1
    rw [← hb0]
    simp only [Real.rpow_zero, Real.rpow_one, mul_one, zero_mul, add_zero, one_mul, le_refl]
  exact holder_logSumExp_step c d x y a b ha0 hb0 hab












theorem logZ_convexOn_param {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (Z 1 (fun s => t * E s))) := by
  have hconv := cumulant_convexOn (ι := Ω) (fun s => -E s) (fun _ => 0)
  refine (hconv.congr ?_)
  intro t _
  simp only
  congr 1
  unfold Z
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  ring



variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]









theorem isingLogZ_convexOn_field (β : ℝ) :
    ConvexOn ℝ Set.univ (fun h : ℝ => Real.log (isingZ G β h)) := by
  have hconv := cumulant_convexOn (ι := ConfigSpace V)
    (fun s => β * ∑ x, spin s x) (fun s => β * ∑ e ∈ G.edgeFinset, bond s e)
  refine (hconv.congr ?_)
  intro h _
  simp only
  congr 1
  unfold isingZ isingWeight hamiltonian
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  ring









theorem isingLogZ_convexOn_beta (h : ℝ) :
    ConvexOn ℝ Set.univ (fun β : ℝ => Real.log (isingZ G β h)) := by
  have hconv := cumulant_convexOn (ι := ConfigSpace V)
    (fun s => - hamiltonian G h s) (fun _ => 0)
  refine (hconv.congr ?_)
  intro β _
  simp only
  congr 1
  unfold isingZ isingWeight
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  ring

end Ising

end StatMech
