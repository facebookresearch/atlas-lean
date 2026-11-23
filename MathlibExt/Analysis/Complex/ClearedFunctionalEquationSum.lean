/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_clearedFE_sum_smul_
of_forall_clearedFE_of_forall_rational.lean`
and
`P2M/Sol/S_LanglandsTunnell_RankinSelberg_forall_clearedFE_sum_smul_
of_forall_clearedFE_of_forall_rational.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

set_option autoImplicit false

open Polynomial

private theorem eq_of_eqOn_halfplane (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ
  g) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → f s = g s) : ∀ s : ℂ, f s = g s := by
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz : ((σ + 1 : ℝ) : ℂ) ∈ {s : ℂ | σ < s.re} := by
    change σ < ((σ + 1 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith
  have hfg : f =ᶠ[nhds ((σ + 1 : ℝ) : ℂ)] g :=
    Filter.eventually_of_mem (hU.mem_nhds hz) (fun s hs => h s hs)
  have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hf.differentiableOn.analyticOnNhd isOpen_univ) (hg.differentiableOn.analyticOnNhd isOpen_univ)
    isPreconnected_univ (Set.mem_univ _) hfg
  exact fun s => this (Set.mem_univ s)

private theorem differentiable_cpow_mul (N : ℕ) (hN : 1 < N) (c : ℂ) : Differentiable ℂ fun s : ℂ =>
  (N : ℂ) ^ (c * s) :=
  (differentiable_id.const_mul c).const_cpow (Or.inl (by exact_mod_cast (by omega : N ≠ 0)))

private theorem differentiable_cpow_neg (N : ℕ) (hN : 1 < N) : Differentiable ℂ fun s : ℂ => (N : ℂ)
  ^ (-s) := by
  have : (fun s : ℂ => (N : ℂ) ^ (-s)) = fun s : ℂ => (N : ℂ) ^ ((-1 : ℂ) * s) := by
    funext s; rw [neg_one_mul]
  rw [this]; exact differentiable_cpow_mul N hN (-1)

private theorem differentiable_cpow_self (N : ℕ) (hN : 1 < N) : Differentiable ℂ fun s : ℂ => (N :
  ℂ) ^ s := by
  have : (fun s : ℂ => (N : ℂ) ^ s) = fun s : ℂ => (N : ℂ) ^ ((1 : ℂ) * s) := by
    funext s; rw [one_mul]
  rw [this]; exact differentiable_cpow_mul N hN 1

private theorem differentiable_eval_comp (p : Polynomial ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ fun s => p.eval (g s) :=
  (Polynomial.differentiable p).comp hg

private theorem exists_forall_eval_ne_zero_of_lt_norm (D : Polynomial ℂ) (hD : D ≠ 0) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → D.eval z ≠ 0 := by
  classical
  refine ⟨∑ w ∈ D.roots.toFinset, ‖w‖, fun z hz hz0 => ?_⟩
  have hmem : z ∈ D.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hD]; exact hz0
  have : ‖z‖ ≤ ∑ w ∈ D.roots.toFinset, ‖w‖ :=
    Finset.single_le_sum (f := fun w : ℂ => ‖w‖) (fun _ _ => norm_nonneg _) hmem
  linarith

private theorem exists_forall_eval_ne_zero_of_norm_lt (D : Polynomial ℂ) (hD : D ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ < ε → D.eval z ≠ 0 := by
  classical
  let S := (D.roots.toFinset).erase 0
  by_cases hS : S.Nonempty
  · refine ⟨S.inf' hS (fun w => ‖w‖), ?_, fun z hz0 hz hz' => ?_⟩
    · obtain ⟨w, hw, hweq⟩ := Finset.exists_mem_eq_inf' hS (fun w => ‖w‖)
      rw [hweq]; exact norm_pos_iff.2 (Finset.ne_of_mem_erase hw)
    · have hmem : z ∈ S := by
        rw [Finset.mem_erase, Multiset.mem_toFinset, Polynomial.mem_roots hD]; exact ⟨hz0, hz'⟩
      exact absurd (Finset.inf'_le (fun w => ‖w‖) hmem) (not_le.2 hz)
  · refine ⟨1, one_pos, fun z hz0 _ hz' => hS ⟨z, ?_⟩⟩
    rw [Finset.mem_erase, Multiset.mem_toFinset, Polynomial.mem_roots hD]; exact ⟨hz0, hz'⟩

private theorem norm_cpow_neg_lt (N : ℕ) (hN : 1 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ‖(N : ℂ) ^ (-s)‖ < ε := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  refine ⟨-Real.logb N ε, fun s hs => ?_⟩
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  calc (N : ℝ) ^ (-s.re) < (N : ℝ) ^ (Real.logb N ε) := Real.rpow_lt_rpow_of_exponent_lt hN1 (by
    linarith)
    _ = ε := Real.rpow_logb (by linarith) hN1.ne' hε

private theorem lt_norm_cpow (N : ℕ) (hN : 1 < N) (R : ℝ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → R < ‖(N : ℂ) ^ s‖ := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  by_cases hR : 0 < R
  · refine ⟨Real.logb N R, fun s hs => ?_⟩
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    calc R = (N : ℝ) ^ (Real.logb N R) := (Real.rpow_logb (by linarith) hN1.ne' hR).symm
      _ < (N : ℝ) ^ s.re := Real.rpow_lt_rpow_of_exponent_lt hN1 hs
  · refine ⟨0, fun s _ => lt_of_le_of_lt (not_lt.1 hR) ?_⟩
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < N)) _

private theorem differentiable_sum' {ι : Type*} [Fintype ι] (F : ι → ℂ → ℂ) (h : ∀ j, Differentiable
  ℂ (F j)) :
    Differentiable ℂ fun s => ∑ j, F j s := by
  classical
  have key : ∀ (u : Finset ι), Differentiable ℂ fun s => ∑ j ∈ u, F j s := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact differentiable_const 0
    | insert a u ha ih =>
      have : (fun s => ∑ j ∈ insert a u, F j s) = fun s => F a s + ∑ j ∈ u, F j s := by
        funext s; rw [Finset.sum_insert ha]
      rw [this]; exact (h a).add ih
  exact key Finset.univ

/-- If each term of a finite family satisfies a cleared functional equation
with rational-function factors, and the weighted sums of the two sides satisfy
cleared functional equations with common factors, then the summed identity
satisfies the same cleared functional equation. The half-plane identities are
extended to all complex parameters by analyticity, and the polynomial factors
are cancelled after specializing where they do not vanish. -/
public theorem forall_clearedFE_sum_smul_of_forall_clearedFE_of_forall_rational
    (N : ℕ) (hN : 1 < N) (C : ℂ) (r : ℤ)
    {ι : Type*} [Fintype ι] (κ : ι → ℂ) (A B : ι → ℂ → ℂ)
    (hj : ∀ j : ι, ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧
      (∀ s : ℂ, σ < s.re → A j s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N :
        ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σd < s.re → B j s * Qd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval
        ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^
          (-s))) *
            Q.eval ((N : ℂ) ^ s) =
          ((Polynomial.C C).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) *
            ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s)))) :
    ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ), Q ≠ 0 → Qd ≠ 0 →
      (∀ s : ℂ, σ < s.re →
        (∑ j, κ j * A j s) * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^
          (-s))) →
      (∀ s : ℂ, σd < s.re →
        (∑ j, κ j * B j s) * Qd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ)
          ^ (-s))) →
      ∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^
          (-s))) *
            Q.eval ((N : ℂ) ^ s) =
          ((Polynomial.C C).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) *
            ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s)) := by
  classical
  intro P Pd Q Qd m md σ σd hQ hQd hA hB
  choose Pj Pdj Qj Qdj mj mdj σj σdj hQj hQdj hAj hBj hFEj using hj
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hpow0 : ∀ z : ℂ, (N : ℂ) ^ z ≠ 0 := fun z => Complex.cpow_ne_zero_iff.2 (Or.inl hN0)
  have dX := differentiable_cpow_neg N hN
  have dY := differentiable_cpow_self N hN
  have dM : ∀ c : ℂ, Differentiable ℂ fun s : ℂ => (N : ℂ) ^ (c * s) := differentiable_cpow_mul N hN
  have dMneg : ∀ c : ℂ, Differentiable ℂ fun s : ℂ => (N : ℂ) ^ (c * -s) := by
    intro c
    have : (fun s : ℂ => (N : ℂ) ^ (c * -s)) = fun s : ℂ => (N : ℂ) ^ ((-c) * s) := by
      funext s; rw [mul_neg, neg_mul]
    rw [this]; exact dM (-c)
  have dPX : ∀ p : Polynomial ℂ, Differentiable ℂ fun s : ℂ => p.eval ((N : ℂ) ^ (-s)) :=
    fun p => differentiable_eval_comp p dX
  have dPY : ∀ p : Polynomial ℂ, Differentiable ℂ fun s : ℂ => p.eval ((N : ℂ) ^ s) :=
    fun p => differentiable_eval_comp p dY
  let D : Polynomial ℂ := ∏ j, Qj j
  let Dd : Polynomial ℂ := ∏ j, Qdj j
  let Dj : ι → Polynomial ℂ := fun j => ∏ i ∈ Finset.univ.erase j, Qj i
  let Ddj : ι → Polynomial ℂ := fun j => ∏ i ∈ Finset.univ.erase j, Qdj i
  have hD : ∀ j, D = Qj j * Dj j := fun j => (Finset.mul_prod_erase Finset.univ Qj (Finset.mem_univ
    j)).symm
  have hDd : ∀ j, Dd = Qdj j * Ddj j := fun j => (Finset.mul_prod_erase Finset.univ Qdj
    (Finset.mem_univ j)).symm
  have hDne : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hQj j
  have hDdne : Dd ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hQdj j
  let σA : ℝ := |σ| + ∑ j, |σj j|
  let σB : ℝ := |σd| + ∑ j, |σdj j|
  have hσA : ∀ s : ℂ, σA < s.re → σ < s.re ∧ ∀ j, σj j < s.re := by
    intro s hs
    have h0 : ∀ j, |σj j| ≤ ∑ i, |σj i| := fun j =>
      Finset.single_le_sum (f := fun i => |σj i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    refine ⟨by linarith [le_abs_self σ, Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg
      (σj i))], fun j => ?_⟩
    linarith [le_abs_self (σj j), h0 j, abs_nonneg σ]
  have hσB : ∀ s : ℂ, σB < s.re → σd < s.re ∧ ∀ j, σdj j < s.re := by
    intro s hs
    have h0 : ∀ j, |σdj j| ≤ ∑ i, |σdj i| := fun j =>
      Finset.single_le_sum (f := fun i => |σdj i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    refine ⟨by linarith [le_abs_self σd, Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
      abs_nonneg (σdj i))], fun j => ?_⟩
    linarith [le_abs_self (σdj j), h0 j, abs_nonneg σd]
  have IA : ∀ s : ℂ, (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) * D.eval ((N : ℂ) ^ (-s)) =
      Q.eval ((N : ℂ) ^ (-s)) *
        ∑ j, κ j * ((N : ℂ) ^ ((mj j : ℂ) * s) * (Pj j).eval ((N : ℂ) ^ (-s)) * (Dj j).eval ((N : ℂ)
          ^ (-s))) := by
    refine eq_of_eqOn_halfplane _ _ (((dM _).mul (dPX P)).mul (dPX D))
      ((dPX Q).mul (differentiable_sum' _ fun j => (((dM _).mul (dPX _)).mul (dPX _)).const_mul _))
        σA ?_
    intro s hs
    obtain ⟨hsσ, hsj⟩ := hσA s hs
    rw [← hA s hsσ, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hAj j s (hsj j), hD j, Polynomial.eval_mul]
    ring
  have IB : ∀ s : ℂ, (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) * Dd.eval ((N : ℂ) ^ (-s))
    =
      Qd.eval ((N : ℂ) ^ (-s)) *
        ∑ j, κ j * ((N : ℂ) ^ ((mdj j : ℂ) * s) * (Pdj j).eval ((N : ℂ) ^ (-s)) * (Ddj j).eval ((N :
          ℂ) ^ (-s))) := by
    refine eq_of_eqOn_halfplane _ _ (((dM _).mul (dPX Pd)).mul (dPX Dd))
      ((dPX Qd).mul (differentiable_sum' _ fun j => (((dM _).mul (dPX _)).mul (dPX _)).const_mul _))
        σB ?_
    intro s hs
    obtain ⟨hsσ, hsj⟩ := hσB s hs
    rw [← hB s hsσ, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hBj j s (hsj j), hDd j, Polynomial.eval_mul]
    ring
  have I6 : ∀ s : ℂ,
      (((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^
        (-s))) *
          Q.eval ((N : ℂ) ^ s)) * (D.eval ((N : ℂ) ^ s) * Dd.eval ((N : ℂ) ^ (-s))) =
      (((Polynomial.C C).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) *
          ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s))) *
        (D.eval ((N : ℂ) ^ s) * Dd.eval ((N : ℂ) ^ (-s))) := by
    intro s
    have IAs := IA (-s)
    rw [neg_neg] at IAs
    have IBs := IB s
    have FE : ∀ j, (N : ℂ) ^ ((mdj j : ℂ) * s) * (Pdj j).eval ((N : ℂ) ^ (-s)) * (Qj j).eval ((N :
      ℂ) ^ s) =
        C * (N : ℂ) ^ ((r : ℂ) * s) * ((N : ℂ) ^ ((mj j : ℂ) * (-s)) * (Pj j).eval ((N : ℂ) ^ s)) *
          (Qdj j).eval ((N : ℂ) ^ (-s)) := by
      intro j
      have h := hFEj j s
      rw [Polynomial.eval_one, one_mul, Polynomial.eval_C] at h
      exact h
    rw [Polynomial.eval_one, one_mul, Polynomial.eval_C]
    have step : (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) * Dd.eval ((N : ℂ) ^ (-s)) *
      D.eval ((N : ℂ) ^ s) =
        Qd.eval ((N : ℂ) ^ (-s)) * (C * (N : ℂ) ^ ((r : ℂ) * s)) * Dd.eval ((N : ℂ) ^ (-s)) *
          ∑ j, κ j * ((N : ℂ) ^ ((mj j : ℂ) * (-s)) * (Pj j).eval ((N : ℂ) ^ s) * (Dj j).eval ((N :
            ℂ) ^ s)) := by
      rw [IBs, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h1 : D.eval ((N : ℂ) ^ s) = (Qj j).eval ((N : ℂ) ^ s) * (Dj j).eval ((N : ℂ) ^ s) := by
        rw [hD j, Polynomial.eval_mul]
      have h2 : Dd.eval ((N : ℂ) ^ (-s)) = (Qdj j).eval ((N : ℂ) ^ (-s)) * (Ddj j).eval ((N : ℂ) ^
        (-s)) := by
        rw [hDd j, Polynomial.eval_mul]
      calc Qd.eval ((N : ℂ) ^ (-s)) * (κ j * ((N : ℂ) ^ ((mdj j : ℂ) * s) * (Pdj j).eval ((N : ℂ) ^
        (-s)) *
              (Ddj j).eval ((N : ℂ) ^ (-s)))) * D.eval ((N : ℂ) ^ s)
          = Qd.eval ((N : ℂ) ^ (-s)) * κ j * (Ddj j).eval ((N : ℂ) ^ (-s)) *
              ((N : ℂ) ^ ((mdj j : ℂ) * s) * (Pdj j).eval ((N : ℂ) ^ (-s)) * (Qj j).eval ((N : ℂ) ^
                s)) *
              (Dj j).eval ((N : ℂ) ^ s) := by rw [h1]; ring
        _ = Qd.eval ((N : ℂ) ^ (-s)) * κ j * (Ddj j).eval ((N : ℂ) ^ (-s)) *
              (C * (N : ℂ) ^ ((r : ℂ) * s) * ((N : ℂ) ^ ((mj j : ℂ) * (-s)) * (Pj j).eval ((N : ℂ) ^
                s)) *
                (Qdj j).eval ((N : ℂ) ^ (-s))) *
              (Dj j).eval ((N : ℂ) ^ s) := by rw [FE j]
        _ = Qd.eval ((N : ℂ) ^ (-s)) * (C * (N : ℂ) ^ ((r : ℂ) * s)) *
              ((Qdj j).eval ((N : ℂ) ^ (-s)) * (Ddj j).eval ((N : ℂ) ^ (-s))) *
              (κ j * ((N : ℂ) ^ ((mj j : ℂ) * (-s)) * (Pj j).eval ((N : ℂ) ^ s) * (Dj j).eval ((N :
                ℂ) ^ s))) := by
            ring
        _ = Qd.eval ((N : ℂ) ^ (-s)) * (C * (N : ℂ) ^ ((r : ℂ) * s)) * Dd.eval ((N : ℂ) ^ (-s)) *
              (κ j * ((N : ℂ) ^ ((mj j : ℂ) * (-s)) * (Pj j).eval ((N : ℂ) ^ s) * (Dj j).eval ((N :
                ℂ) ^ s))) := by
            rw [h2]
    calc (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ s) *
          (D.eval ((N : ℂ) ^ s) * Dd.eval ((N : ℂ) ^ (-s)))
        = Q.eval ((N : ℂ) ^ s) *
          ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) * Dd.eval ((N : ℂ) ^ (-s)) * D.eval
            ((N : ℂ) ^ s)) := by
          ring
      _ = Q.eval ((N : ℂ) ^ s) * (Qd.eval ((N : ℂ) ^ (-s)) * (C * (N : ℂ) ^ ((r : ℂ) * s)) * Dd.eval
        ((N : ℂ) ^ (-s)) *
          ∑ j, κ j * ((N : ℂ) ^ ((mj j : ℂ) * (-s)) * (Pj j).eval ((N : ℂ) ^ s) * (Dj j).eval ((N :
            ℂ) ^ s))) := by rw [step]
      _ = C * (N : ℂ) ^ ((r : ℂ) * s) * Qd.eval ((N : ℂ) ^ (-s)) * Dd.eval ((N : ℂ) ^ (-s)) *
          (Q.eval ((N : ℂ) ^ s) *
            ∑ j, κ j * ((N : ℂ) ^ ((mj j : ℂ) * (-s)) * (Pj j).eval ((N : ℂ) ^ s) * (Dj j).eval ((N
              : ℂ) ^ s))) := by ring
      _ = C * (N : ℂ) ^ ((r : ℂ) * s) * Qd.eval ((N : ℂ) ^ (-s)) * Dd.eval ((N : ℂ) ^ (-s)) *
          ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s) * D.eval ((N : ℂ) ^ s)) := by rw [←
            IAs]
      _ = C * (N : ℂ) ^ ((r : ℂ) * s) * ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) *
          Qd.eval ((N : ℂ) ^ (-s)) * (D.eval ((N : ℂ) ^ s) * Dd.eval ((N : ℂ) ^ (-s))) := by ring
  obtain ⟨R, hR⟩ := exists_forall_eval_ne_zero_of_lt_norm D hDne
  obtain ⟨ε, hε, hεD⟩ := exists_forall_eval_ne_zero_of_norm_lt Dd hDdne
  obtain ⟨σ₁, hσ₁⟩ := lt_norm_cpow N hN R
  obtain ⟨σ₂, hσ₂⟩ := norm_cpow_neg_lt N hN ε hε
  refine eq_of_eqOn_halfplane _ _
    ((((dPY 1).mul ((dM _).mul (dPX Pd))).mul (dPY Q)))
    ((((dPY (Polynomial.C C)).mul (dM _)).mul ((dMneg _).mul (dPY P))).mul (dPX Qd)) (max σ₁ σ₂) ?_
  intro s hs
  have h1 : D.eval ((N : ℂ) ^ s) ≠ 0 := hR _ (hσ₁ s (lt_of_le_of_lt (le_max_left _ _) hs))
  have h2 : Dd.eval ((N : ℂ) ^ (-s)) ≠ 0 := hεD _ (hpow0 _) (hσ₂ s (lt_of_le_of_lt (le_max_right _
    _) hs))
  exact mul_right_cancel₀ (mul_ne_zero h1 h2) (I6 s)
