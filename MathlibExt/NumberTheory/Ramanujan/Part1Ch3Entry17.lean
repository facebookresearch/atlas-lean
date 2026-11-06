/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry17

-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry17

open Filter Metric
private theorem iteratedDeriv_eventuallyEq_aux {f g : ℝ → ℝ} {x : ℝ} {n : ℕ}
    (h : f =ᶠ[nhds x] g) : iteratedDeriv n f x = iteratedDeriv n g x := by
  have key : ∀ m : ℕ, (deriv^[m] f =ᶠ[nhds x] deriv^[m] g) := by
    intro m
    induction m with
    | zero => simpa using h
    | succ k ih =>
      rw [Filter.eventuallyEq_iff_exists_mem] at ih ⊢
      obtain ⟨U, hUmem, hUeq⟩ := ih
      obtain ⟨V, hVU, hVopen, hxV⟩ := _root_.mem_nhds_iff.mp hUmem
      refine ⟨V, hVopen.mem_nhds hxV, ?_⟩
      intro y hy
      have h1 : deriv^[k] f =ᶠ[nhds y] deriv^[k] g := by
        apply Filter.eventually_of_mem (hVopen.mem_nhds hy)
        intro z hz
        exact hUeq (hVU hz)
      have e1 : deriv^[k+1] f y = deriv (deriv^[k] f) y := by
        have h1 : deriv^[k+1] f y = deriv^[1+k] f y := by rw [add_comm 1 k]
        rw [h1, Function.iterate_add_apply, Function.iterate_one]
      have e2 : deriv^[k+1] g y = deriv (deriv^[k] g) y := by
        have h1 : deriv^[k+1] g y = deriv^[1+k] g y := by rw [add_comm 1 k]
        rw [h1, Function.iterate_add_apply, Function.iterate_one]
      rw [e1, e2]
      exact h1.deriv_eq
  have hmn := key n
  have e1 : iteratedDeriv n f x = deriv^[n] f x := by rw [iteratedDeriv_eq_iterate]
  have e2 : iteratedDeriv n g x = deriv^[n] g x := by rw [iteratedDeriv_eq_iterate]
  rw [e1, e2]
  exact hmn.self_of_nhds

private theorem iteratedDeriv_deriv_eq_aux {f : ℝ → ℝ} {x : ℝ} {m : ℕ} (_hm : 1 ≤ m) :
    iteratedDeriv (m - 1) (deriv f) x = iteratedDeriv m f x := by
  have e1 : iteratedDeriv (m - 1) (deriv f) x = deriv^[m - 1] (deriv f) x := by
    rw [iteratedDeriv_eq_iterate]
  have e2 : iteratedDeriv m f x = deriv^[m] f x := by rw [iteratedDeriv_eq_iterate]
  rw [e1, e2]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hB : deriv^[k + 1] f x = deriv^[k] (deriv f) x := by
    have h0 := congrFun (Function.iterate_add_apply deriv k 1 f) x
    simpa using h0
  exact hB.symm

private theorem key_ode_eventually
    {R C : ℝ} {x : ℝ → ℝ}
    (hRpos : 0 < R)
    (hx_an : AnalyticAt ℝ x 0)
    (hball : ∀ h : ℝ, |h| < R → 0 < x h ∧ x h * Real.log (x h) = C + h) :
    ∀ᶠ h in nhds (0:ℝ), (deriv x h) ^ 2 + (x h + C + h) * deriv (deriv x) h = 0 := by
  have hev_an : ∀ᶠ h in nhds (0:ℝ), AnalyticAt ℝ x h := hx_an.eventually_analyticAt
  have hball_mem : Metric.ball (0:ℝ) R ∈ nhds (0:ℝ) := Metric.ball_mem_nhds 0 hRpos
  have hev_ball : ∀ᶠ h in nhds (0:ℝ), h ∈ Metric.ball (0:ℝ) R :=
    Filter.eventually_of_mem hball_mem (fun h hh => hh)
  have hev : ∀ᶠ h in nhds (0:ℝ), AnalyticAt ℝ x h ∧ h ∈ Metric.ball (0:ℝ) R :=
    hev_an.and hev_ball
  filter_upwards [hev] with h hh
  obtain ⟨hxh_an, hmem⟩ := hh
  have hdist : dist h 0 < R := Metric.mem_ball.mp hmem
  have habs : |h| < R := by
    have e : dist h (0:ℝ) = |h| := by simp [dist_eq_norm, Real.norm_eq_abs, sub_zero]
    rw [e] at hdist
    exact hdist
  obtain ⟨hpos, hlog⟩ := hball h habs
  have hEq1_ev : (fun h' => (1 + Real.log (x h')) * deriv x h')
      =ᶠ[nhds h] (fun _ => (1:ℝ)) := by
    have hev_an_h : ∀ᶠ h' in nhds h, AnalyticAt ℝ x h' := hxh_an.eventually_analyticAt
    have hball_nhds : Metric.ball (0:ℝ) R ∈ nhds h :=
      Metric.isOpen_ball.mem_nhds hmem
    have hev_ball_h : ∀ᶠ h' in nhds h, h' ∈ Metric.ball (0:ℝ) R :=
      Filter.eventually_of_mem hball_nhds (fun h' hh' => hh')
    have hev2 := hev_an_h.and hev_ball_h
    filter_upwards [hev2] with h' hh'
    obtain ⟨hxh'_an, hmem'⟩ := hh'
    have hdist' : dist h' 0 < R := Metric.mem_ball.mp hmem'
    have habs' : |h'| < R := by
      have e : dist h' (0:ℝ) = |h'| := by simp [dist_eq_norm, Real.norm_eq_abs, sub_zero]
      rw [e] at hdist'
      exact hdist'
    obtain ⟨hpos', hlog'⟩ := hball h' habs'
    have hx_d : HasDerivAt x (deriv x h') h' :=
      (hxh'_an.hasStrictDerivAt).hasDerivAt
    have hne : x h' ≠ 0 := ne_of_gt hpos'
    have hf : HasDerivAt (fun y => y * Real.log y) (Real.log (x h') + 1) (x h') :=
      Real.hasDerivAt_mul_log hne
    have hcomp : HasDerivAt ((fun y => y * Real.log y) ∘ x)
        ((Real.log (x h') + 1) * deriv x h') h' :=
      HasDerivAt.comp h' hf hx_d
    have hball_nhds' : Metric.ball (0:ℝ) R ∈ nhds h' :=
      Metric.isOpen_ball.mem_nhds hmem'
    have heq_ev : ((fun y => y * Real.log y) ∘ x) =ᶠ[nhds h']
        (fun h'' => C + h'') := by
      apply Filter.eventually_of_mem hball_nhds'
      intro h'' hhm
      have hdd : dist h'' 0 < R := Metric.mem_ball.mp hhm
      have haa : |h''| < R := by
        have e : dist h'' (0:ℝ) = |h''| := by simp [dist_eq_norm, Real.norm_eq_abs, sub_zero]
        rw [e] at hdd
        exact hdd
      obtain ⟨_, hlg⟩ := hball h'' haa
      simp only [Function.comp_apply]
      exact hlg
    have hbase : HasDerivAt (fun h'' : ℝ => C + h'') 1 h' :=
      (hasDerivAt_id h').const_add C
    have hconst : HasDerivAt ((fun y => y * Real.log y) ∘ x) 1 h' :=
      hbase.congr_of_eventuallyEq heq_ev
    have hunique := HasDerivAt.unique hcomp hconst
    show (1 + Real.log (x h')) * deriv x h' = 1
    have : (Real.log (x h') + 1) * deriv x h' = 1 := hunique
    linarith [this]
  have hx_d : HasDerivAt x (deriv x h) h := (hxh_an.hasStrictDerivAt).hasDerivAt
  have hx_dd : HasDerivAt (deriv x) (deriv (deriv x) h) h :=
    ((hxh_an.deriv).hasStrictDerivAt).hasDerivAt
  have hne : x h ≠ 0 := ne_of_gt hpos
  have hlog_d : HasDerivAt (fun h' => Real.log (x h')) ((deriv x h) / x h) h :=
    hx_d.log hne
  have hU_d : HasDerivAt (fun h' => 1 + Real.log (x h')) ((deriv x h) / x h) h :=
    HasDerivAt.const_add 1 hlog_d
  have hprod : HasDerivAt (fun h' => (1 + Real.log (x h')) * deriv x h')
      ((deriv x h / x h) * deriv x h + (1 + Real.log (x h)) * deriv (deriv x) h) h :=
    hU_d.mul hx_dd
  have hzero : HasDerivAt (fun h' => (1 + Real.log (x h')) * deriv x h') 0 h := by
    have h1 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 h := hasDerivAt_const h 1
    exact h1.congr_of_eventuallyEq hEq1_ev
  have hunique2 := HasDerivAt.unique hprod hzero
  have hU_val : (deriv x h / x h) * deriv x h + (1 + Real.log (x h)) * deriv (deriv x) h = 0 :=
    hunique2
  have hH : (deriv x h) ^ 2 + (x h + C + h) * deriv (deriv x) h = 0 := by
    have h1 : x h * ((deriv x h / x h) * deriv x h +
        (1 + Real.log (x h)) * deriv (deriv x) h) = 0 := by rw [hU_val]; ring
    have h2 : x h * ((deriv x h / x h) * deriv x h) = (deriv x h) ^ 2 := by
      field_simp
    have h3 : x h * ((1 + Real.log (x h)) * deriv (deriv x) h)
        = (x h + C + h) * deriv (deriv x) h := by
      have hxl : x h * Real.log (x h) = C + h := hlog
      have hxx : x h * (1 + Real.log (x h)) = x h + C + h := by linear_combination hxl
      calc x h * ((1 + Real.log (x h)) * deriv (deriv x) h)
          = (x h * (1 + Real.log (x h))) * deriv (deriv x) h := by ring
        _ = (x h + C + h) * deriv (deriv x) h := by rw [hxx]
    have h4 : x h * ((deriv x h / x h) * deriv x h +
        (1 + Real.log (x h)) * deriv (deriv x) h)
        = (deriv x h) ^ 2 + (x h + C + h) * deriv (deriv x) h := by
      rw [mul_add, h2, h3]
    rw [h4] at h1
    exact h1
  exact hH

private theorem expand_test
    {R C : ℝ} {x : ℝ → ℝ}
    (hx_an : AnalyticAt ℝ x 0)
    (hevH : ∀ᶠ h in nhds (0:ℝ), (deriv x h) ^ 2 + (x h + C + h) * deriv (deriv x) h = 0)
    {n : ℕ} :
    ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * iteratedDeriv (i + 1) x 0 *
      iteratedDeriv (n - i + 1) x 0)
    + ∑ j ∈ Finset.range (n + 1), ((n.choose j : ℝ) * iteratedDeriv j
      (fun h => x h + C + h) 0 * iteratedDeriv (n - j + 2) x 0) = 0 := by
  set H : ℝ → ℝ := fun h => (deriv x h) * (deriv x h) +
    (x h + C + h) * deriv (deriv x) h with hHdef
  have hevH' : H =ᶠ[nhds (0:ℝ)] 0 := by
    filter_upwards [hevH] with h hh
    simp only [hHdef, Pi.zero_apply]
    have : (deriv x h) * (deriv x h) = (deriv x h) ^ 2 := by ring
    rw [this]
    exact hh
  have hH0 : iteratedDeriv n H 0 = 0 := by
    have h1 := iteratedDeriv_eventuallyEq_aux (n := n) (x := (0:ℝ)) hevH'
    have h2 : iteratedDeriv n (0 : ℝ → ℝ) 0 = 0 := by
      have : (0 : ℝ → ℝ) = fun _ => (0:ℝ) := rfl
      rw [this]
      rw [iteratedDeriv_const]
      simp
    rw [h1]
    exact h2
  have hcu : ContDiffAt ℝ (n : WithTop ℕ∞) (deriv x) 0 := hx_an.deriv.contDiffAt
  have hcv : ContDiffAt ℝ (n : WithTop ℕ∞) (deriv (deriv x)) 0 :=
    (hx_an.deriv.deriv).contDiffAt
  have haw : AnalyticAt ℝ (fun h => x h + C + h) 0 := by
    have h1 : (fun h : ℝ => x h + C + h) = (x + (fun _ => C) + id) := by
      funext h
      simp [Pi.add_apply, id]
    rw [h1]
    exact ((hx_an.add analyticAt_const).add analyticAt_id)
  have hcw : ContDiffAt ℝ (n : WithTop ℕ∞) (fun h => x h + C + h) 0 := haw.contDiffAt
  have hUU : ContDiffAt ℝ (n : WithTop ℕ∞) ((deriv x) * (deriv x)) 0 :=
    hcu.mul hcu
  have hWV : ContDiffAt ℝ (n : WithTop ℕ∞)
      ((fun h => x h + C + h) * deriv (deriv x)) 0 := hcw.mul hcv
  have hHfun : H = ((deriv x) * (deriv x)) + ((fun h => x h + C + h) * deriv (deriv x)) := by
    funext h
    simp [hHdef, Pi.add_apply, Pi.mul_apply]
  have hexpand : iteratedDeriv n H 0 =
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        iteratedDeriv i (deriv x) 0 * iteratedDeriv (n - i) (deriv x) 0)
      + (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        iteratedDeriv j (fun h => x h + C + h) 0 *
          iteratedDeriv (n - j) (deriv (deriv x)) 0) := by
    rw [hHfun]
    rw [iteratedDeriv_add hUU hWV]
    congr 1
    · exact iteratedDeriv_mul hcu hcu
    · exact iteratedDeriv_mul hcw hcv
  rw [hexpand] at hH0
  have c1 : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * iteratedDeriv i (deriv x) 0 * iteratedDeriv (n - i) (deriv x) 0
      = (n.choose i : ℝ) * iteratedDeriv (i + 1) x 0 * iteratedDeriv (n - i + 1) x 0 := by
    intro i _
    have e1 : iteratedDeriv i (deriv x) 0 = iteratedDeriv (i + 1) x 0 := by
      have h := iteratedDeriv_deriv_eq_aux (f := x) (x := (0:ℝ)) (m := i + 1) (by omega)
      simpa using h
    have e2 : iteratedDeriv (n - i) (deriv x) 0 = iteratedDeriv (n - i + 1) x 0 := by
      have h := iteratedDeriv_deriv_eq_aux (f := x) (x := (0:ℝ)) (m := n - i + 1) (by omega)
      simpa using h
    rw [e1, e2]
  have c2 : ∀ j ∈ Finset.range (n + 1),
      (n.choose j : ℝ) * iteratedDeriv j (fun h => x h + C + h) 0 *
        iteratedDeriv (n - j) (deriv (deriv x)) 0
      = (n.choose j : ℝ) * iteratedDeriv j (fun h => x h + C + h) 0 *
        iteratedDeriv (n - j + 2) x 0 := by
    intro j _
    have e : iteratedDeriv (n - j) (deriv (deriv x)) 0 = iteratedDeriv (n - j + 2) x 0 := by
      have h1 := iteratedDeriv_deriv_eq_aux (f := deriv x) (x := (0:ℝ)) (m := n - j + 1) (by omega)
      have h2 := iteratedDeriv_deriv_eq_aux (f := x) (x := (0:ℝ)) (m := n - j + 2) (by omega)
      have e1 : iteratedDeriv (n - j) (deriv (deriv x)) 0 =
          iteratedDeriv (n - j + 1) (deriv x) 0 := by
        have : n - j + 1 - 1 = n - j := by omega
        rw [← this]
        exact h1
      have e2 : iteratedDeriv (n - j + 1) (deriv x) 0 = iteratedDeriv (n - j + 2) x 0 := by
        have : n - j + 2 - 1 = n - j + 1 := by omega
        rw [← this]
        exact h2
      rw [e1, e2]
    rw [e]
  rw [Finset.sum_congr rfl c1, Finset.sum_congr rfl c2] at hH0
  exact hH0

private theorem range_succ_Icc {F : ℕ → ℝ} {n : ℕ} :
    (∑ i ∈ Finset.range (n + 1), F (i + 1)) = ∑ k ∈ Finset.Icc 1 (n + 1), F k := by
  induction n with
  | zero =>
    simp [Finset.range_one, Finset.Icc_self]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hmem : 1 ≤ m + 1 + 1 := by omega
    rw [Finset.sum_Icc_succ_top hmem]
    rw [ih]

private theorem comb_identity {X : ℕ → ℝ} {n : ℕ} :
    (n : ℝ) * (X 1 * X (n + 1))
    + (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (X (i + 1) * X (n - i + 1)))
    + (∑ j ∈ Finset.Icc 2 n, (n.choose j : ℝ) * (X j * X (n + 2 - j)))
    = ∑ k ∈ Finset.Icc 1 (n + 1), (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k))) := by
  have hS : (∑ k ∈ Finset.Icc 1 (n + 1), (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k))))
      = ∑ i ∈ Finset.range (n + 1), (((n + 1).choose (i + 1) : ℝ) * (X (i + 1) * X (n + 2 - (i + 1)))) := by
    rw [← range_succ_Icc]
  rw [hS]
  have hint : (∑ j ∈ Finset.Icc 2 n, (n.choose j : ℝ) * (X j * X (n + 2 - j)))
      = ∑ i ∈ Finset.range (n + 1),
        (if 2 ≤ i + 1 ∧ i + 1 ≤ n then (n.choose (i + 1) : ℝ) * (X (i + 1) * X (n + 2 - (i + 1))) else 0) := by
    have hsub : Finset.Icc 2 n ⊆ Finset.Icc 1 (n + 1) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    have hside : ∀ k ∈ Finset.Icc 1 (n + 1), k ∉ Finset.Icc 2 n →
        (if 2 ≤ k ∧ k ≤ n then (n.choose k : ℝ) * (X k * X (n + 2 - k)) else 0) = 0 := by
      intro k _ hnk
      have hnc : ¬ (2 ≤ k ∧ k ≤ n) := by
        simpa [Finset.mem_Icc] using hnk
      rw [ite_eq_right hnc]
    have hss := Finset.sum_subset hsub (f :=
      fun k => if 2 ≤ k ∧ k ≤ n then (n.choose k : ℝ) * (X k * X (n + 2 - k)) else 0) hside
    have hsub_ite : (∑ j ∈ Finset.Icc 2 n,
          (if 2 ≤ j ∧ j ≤ n then (n.choose j : ℝ) * (X j * X (n + 2 - j)) else 0))
        = ∑ j ∈ Finset.Icc 2 n, (n.choose j : ℝ) * (X j * X (n + 2 - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjc : (2 ≤ j ∧ j ≤ n) := Finset.mem_Icc.mp hj
      rw [ite_eq_left hjc]
    rw [← hsub_ite, hss, ← range_succ_Icc]
  rw [hint]
  have hextra : (n : ℝ) * (X 1 * X (n + 1))
      = ∑ i ∈ Finset.range (n + 1), (if i = 0 then (n : ℝ) * (X 1 * X (n + 1)) else 0) := by
    rw [Finset.sum_ite_eq']
    simp [Finset.mem_range]
  rw [hextra]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := by
    have := Finset.mem_range.mp hi
    omega
  by_cases hi0 : i = 0
  · subst hi0
    have hif : ¬ (2 ≤ 0 + 1 ∧ 0 + 1 ≤ n) := by omega
    rw [ite_eq_left rfl, ite_eq_right hif]
    simp only [add_zero, zero_add]
    have h1 : (n.choose 0 : ℝ) = 1 := by simp
    have h2 : ((n + 1).choose 1 : ℝ) = (n : ℝ) + 1 := by
      rw [Nat.choose_one_right]
      push_cast
      ring
    have hn1 : n + 2 - (0 + 1) = n + 1 := by omega
    have hn2 : n - 0 + 1 = n + 1 := by omega
    rw [hn1, hn2, h1, h2]
    ring
  · by_cases hin : i + 1 = n + 1
    · have hin' : i = n := by omega
      have hif : ¬ (2 ≤ i + 1 ∧ i + 1 ≤ n) := by omega
      rw [ite_eq_right hi0, ite_eq_right hif, hin']
      simp only [add_zero, zero_add]
      have h1 : (n.choose n : ℝ) = 1 := by simp [Nat.choose_self]
      have h2 : ((n + 1).choose (n + 1) : ℝ) = 1 := by simp [Nat.choose_self]
      have e1 : n - n + 1 = 1 := by omega
      have e2 : n + 2 - (n + 1) = 1 := by omega
      rw [e1, e2, h1, h2]
    · have hn1 : i + 1 ≤ n := by omega
      have hif : (2 ≤ i + 1 ∧ i + 1 ≤ n) := by omega
      rw [ite_eq_right hi0, ite_eq_left hif]
      simp only [zero_add]
      have hpas : ((n + 1).choose (i + 1) : ℝ)
          = (n.choose i : ℝ) + (n.choose (i + 1) : ℝ) := by
        have hnat : (n + 1).choose (i + 1) = n.choose i + n.choose (i + 1) :=
          Nat.choose_succ_succ n i
        exact_mod_cast hnat
      have e1 : n - i + 1 = n + 2 - (i + 1) := by omega
      rw [e1, hpas]
      ring

private theorem w_zero {x : ℝ → ℝ} {C a : ℝ}
    (hx0 : x 0 = a) :
    iteratedDeriv 0 (fun h => x h + C + h) 0 = a + C := by
  rw [iteratedDeriv_zero]
  simp [hx0]

private theorem w_one {x : ℝ → ℝ} {C : ℝ}
    (hx_an : AnalyticAt ℝ x 0) :
    iteratedDeriv 1 (fun h => x h + C + h) 0 = iteratedDeriv 1 x 0 + 1 := by
  have hcx : ContDiffAt ℝ (1 : WithTop ℕ∞) x 0 := hx_an.contDiffAt
  have hcc : ContDiffAt ℝ (1 : WithTop ℕ∞) (fun _ : ℝ => C) 0 :=
    analyticAt_const.contDiffAt
  have hci : ContDiffAt ℝ (1 : WithTop ℕ∞) (id : ℝ → ℝ) 0 :=
    analyticAt_id.contDiffAt
  have hF : ContDiffAt ℝ (1 : WithTop ℕ∞) (fun h : ℝ => x h + C) 0 := by
    have e : (fun h : ℝ => x h + C) = (x + fun _ => C) := rfl
    rw [e]
    exact hcx.add hcc
  have hEq : (fun h : ℝ => x h + C + h) = ((fun h : ℝ => x h + C) + id) := rfl
  rw [hEq]
  have hAdd := iteratedDeriv_add (f := (fun h : ℝ => x h + C)) (g := id) hF hci
  rw [hAdd]
  have hF2 : iteratedDeriv 1 (fun h : ℝ => x h + C) 0 = iteratedDeriv 1 x 0 := by
    have e : (fun h : ℝ => x h + C) = (x + fun _ => C) := rfl
    rw [e]
    rw [iteratedDeriv_add hcx hcc]
    rw [iteratedDeriv_const]
    simp
  rw [hF2]
  rw [iteratedDeriv_id]
  simp

private theorem w_ge2 {x : ℝ → ℝ} {C : ℝ} {j : ℕ}
    (hx_an : AnalyticAt ℝ x 0) (hj : 2 ≤ j) :
    iteratedDeriv j (fun h => x h + C + h) 0 = iteratedDeriv j x 0 := by
  have hcx : ContDiffAt ℝ (j : WithTop ℕ∞) x 0 := hx_an.contDiffAt
  have hcc : ContDiffAt ℝ (j : WithTop ℕ∞) (fun _ : ℝ => C) 0 :=
    analyticAt_const.contDiffAt
  have hci : ContDiffAt ℝ (j : WithTop ℕ∞) (id : ℝ → ℝ) 0 :=
    analyticAt_id.contDiffAt
  have hF : ContDiffAt ℝ (j : WithTop ℕ∞) (fun h : ℝ => x h + C) 0 := by
    have e : (fun h : ℝ => x h + C) = (x + fun _ => C) := rfl
    rw [e]
    exact hcx.add hcc
  have hEq : (fun h : ℝ => x h + C + h) = ((fun h : ℝ => x h + C) + id) := rfl
  rw [hEq]
  have hAdd := iteratedDeriv_add (f := (fun h : ℝ => x h + C)) (g := id) hF hci
  rw [hAdd]
  have hF2 : iteratedDeriv j (fun h : ℝ => x h + C) 0 = iteratedDeriv j x 0 := by
    have e : (fun h : ℝ => x h + C) = (x + fun _ => C) := rfl
    rw [e]
    rw [iteratedDeriv_add hcx hcc]
    have hc0 : iteratedDeriv j (fun _ : ℝ => C) 0 = 0 := by
      rw [iteratedDeriv_const]
      simp [ne_of_gt (by omega : 0 < j)]
    rw [hc0, add_zero]
  rw [hF2]
  have hi0 : iteratedDeriv j (id : ℝ → ℝ) 0 = 0 := by
    rw [iteratedDeriv_id]
    simp [ne_of_gt (by omega : 0 < j), ne_of_gt (by omega : 1 < j)]
  rw [hi0, add_zero]

private theorem rest_eq (G : ℕ → ℝ) {m : ℕ} :
    (∑ i ∈ Finset.range m, G (i + 2)) = ∑ j ∈ Finset.Icc 2 (m + 1), G j := by
  apply Finset.sum_bij (fun i _ => i + 2)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [Finset.mem_Icc]
    omega
  · intro i hi j hj h
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨j - 2, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i _
    rfl

private theorem final_from_E {a A : ℝ} {n : ℕ} {X : ℕ → ℝ}
    (hA : A ≠ 0)
    (hE : a * A * (X (n + 2)) + (n : ℝ) * (X (n + 1))
      + (∑ k ∈ Finset.Icc 1 (n + 1), (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k)))) = 0) :
    (-a) ^ (n + 1) * (X (n + 2))
      = A⁻¹ * (n : ℝ) * ((-a) ^ n * (X (n + 1)))
        + A⁻¹ * ∑ k ∈ Finset.Icc 1 (n + 1),
          (((n + 1).choose k : ℝ) * (((-a) ^ (k - 1) * X k) * ((-a) ^ (n + 1 - k) * X (n + 2 - k)))) := by
  have hsum : (∑ k ∈ Finset.Icc 1 (n + 1),
        (((n + 1).choose k : ℝ) * (((-a) ^ (k - 1) * X k) * ((-a) ^ (n + 1 - k) * X (n + 2 - k)))))
      = (-a) ^ n * (∑ k ∈ Finset.Icc 1 (n + 1), (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkk : k ≤ n + 1 := (Finset.mem_Icc.mp hk).2
    have hexp : (k - 1) + (n + 1 - k) = n := by omega
    have hpow : (-a : ℝ) ^ (k - 1) * (-a) ^ (n + 1 - k) = (-a) ^ n := by
      rw [← pow_add, hexp]
    calc ((n + 1).choose k : ℝ) * (((-a) ^ (k - 1) * X k) * ((-a) ^ (n + 1 - k) * X (n + 2 - k)))
        = ((-a) ^ (k - 1) * (-a) ^ (n + 1 - k)) * (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k))) := by ring
      _ = (-a) ^ n * (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k))) := by rw [hpow]
  rw [hsum]
  have hpow_succ : (-a : ℝ) ^ (n + 1) = (-a) ^ n * (-a) := pow_succ _ _
  have hE' : (-a) * A * (X (n + 2)) = (n : ℝ) * (X (n + 1))
      + (∑ k ∈ Finset.Icc 1 (n + 1), (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k)))) := by
    have h1 : a * A * (X (n + 2)) = -((n : ℝ) * (X (n + 1))
        + (∑ k ∈ Finset.Icc 1 (n + 1), (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k))))) := by
      linarith [hE]
    have h2 : (-a) * A * (X (n + 2)) = -(a * A * (X (n + 2))) := by ring
    rw [h2, h1, neg_neg]
  have hcancel : (-a : ℝ) * (X (n + 2)) = A⁻¹ * ((n : ℝ) * (X (n + 1))
      + (∑ k ∈ Finset.Icc 1 (n + 1), (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k))))) := by
    rw [eq_inv_mul_iff_mul_eq₀ hA]
    have h3 : A * ((-a) * (X (n + 2))) = (-a) * A * (X (n + 2)) := by ring
    rw [h3]
    exact hE'
  calc (-a) ^ (n + 1) * (X (n + 2))
      = (-a) ^ n * ((-a) * (X (n + 2))) := by rw [hpow_succ]; ring
    _ = (-a) ^ n * (A⁻¹ * ((n : ℝ) * (X (n + 1))
        + (∑ k ∈ Finset.Icc 1 (n + 1), (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k)))))) := by rw [hcancel]
    _ = A⁻¹ * (n : ℝ) * ((-a) ^ n * (X (n + 1)))
        + A⁻¹ * ((-a) ^ n * (∑ k ∈ Finset.Icc 1 (n + 1), (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k))))) := by ring

private theorem recurrence_generic {a R C A : ℝ} {x : ℝ → ℝ}
    (hRpos : 0 < R)
    (hx_an : AnalyticAt ℝ x 0)
    (hx0 : x 0 = a)
    (hA_ne : A ≠ 0)
    (hCA : a + C = a * A)
    (hball : ∀ h : ℝ, |h| < R → 0 < x h ∧ x h * Real.log (x h) = C + h)
    (r : ℕ) (hr : 2 ≤ r) :
    (-a) ^ (r - 1) * iteratedDeriv r x 0
      = A⁻¹ * ((r : ℝ) - 2) * ((-a) ^ (r - 2) * iteratedDeriv (r - 1) x 0)
        + A⁻¹ * ∑ k ∈ Finset.Icc 1 (r - 1), ((r - 1).choose k : ℝ) *
          (((-a) ^ (k - 1) * iteratedDeriv k x 0) * ((-a) ^ (r - k - 1) * iteratedDeriv (r - k) x 0)) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  have er1 : n + 2 - 1 = n + 1 := by omega
  have er2 : n + 2 - 2 = n := by omega
  have hRcast : (((n + 2 : ℕ)) : ℝ) - 2 = (n : ℝ) := by push_cast; ring
  have hevH : ∀ᶠ h in nhds (0:ℝ), (deriv x h) ^ 2 + (x h + C + h) * deriv (deriv x) h = 0 :=
    key_ode_eventually hRpos hx_an hball
  have hexpand := expand_test (R := R) (C := C) (x := x) hx_an hevH (n := n)
  have hsum_exp : (∑ k ∈ Finset.Icc 1 (n + 2 - 1), (((n + 2 - 1).choose k : ℝ) *
        (((-a) ^ (k - 1) * iteratedDeriv k x 0) * ((-a) ^ (n + 2 - k - 1) * iteratedDeriv (n + 2 - k) x 0))))
      = ∑ k ∈ Finset.Icc 1 (n + 1), (((n + 1).choose k : ℝ) *
        (((-a) ^ (k - 1) * iteratedDeriv k x 0) * ((-a) ^ (n + 1 - k) * iteratedDeriv (n + 2 - k) x 0))) := by
    rw [er1]
    apply Finset.sum_congr rfl
    intro k hk
    have e2 : ∀ k, n + 2 - k - 1 = n + 1 - k := by intro k; omega
    rw [e2 k]
  rw [hsum_exp, er1, er2, hRcast]
  set X : ℕ → ℝ := fun k => iteratedDeriv k x 0 with hXdef
  set W : ℕ → ℝ := fun j => iteratedDeriv j (fun h => x h + C + h) 0 with hWdef
  have hXr : iteratedDeriv (n + 2) x 0 = X (n + 2) := rfl
  have hXr1 : iteratedDeriv (n + 1) x 0 = X (n + 1) := rfl
  have hW0 : W 0 = a + C := by
    simp only [hWdef]
    exact w_zero hx0
  have hW1 : W 1 = X 1 + 1 := by
    simp only [hWdef, hXdef]
    exact w_one hx_an
  have hWge : ∀ j, 2 ≤ j → W j = X j := by
    intro j hj
    simp only [hWdef, hXdef]
    exact w_ge2 hx_an hj
  have hexpand_XW : (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * X (i + 1) * X (n - i + 1)))
      + (∑ j ∈ Finset.range (n + 1), ((n.choose j : ℝ) * W j * X (n - j + 2))) = 0 := by
    have h := hexpand
    simp only [hXdef, hWdef] at h ⊢
    exact h
  by_cases hn0 : n = 0
  · subst hn0
    have hS1 : (∑ i ∈ Finset.range 1, ((Nat.choose 0 i : ℝ) * (X (i + 1) * X (0 - i + 1))))
        = X 1 * X 1 := by simp [hXdef]
    have hS2 : (∑ j ∈ Finset.range 1, ((Nat.choose 0 j : ℝ) * W j * X (0 - j + 2)))
        = (a + C) * X 2 := by
      simp only [Finset.sum_range_one]
      simp [hW0]
    have h0 := hexpand_XW
    simp only [Nat.zero_add] at h0
    have hE : a * A * (X 2) + ((0 : ℕ) : ℝ) * (X 1)
        + (∑ k ∈ Finset.Icc 1 1, (((1).choose k : ℝ) * (X k * X (2 - k)))) = 0 := by
      have hIcc : (∑ k ∈ Finset.Icc 1 1, (((1).choose k : ℝ) * (X k * X (2 - k)))) = X 1 * X 1 := by
        simp [Finset.Icc_self]
      rw [hIcc]
      simp only [Nat.cast_zero, zero_mul, add_zero]
      have hW0' : W 0 = a + C := hW0
      have hex0 := hexpand_XW
      simp only [Nat.zero_add, Finset.sum_range_one] at hex0
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at hex0
      have e1 : (0 - 0 + 1 : ℕ) = 1 := by omega
      have e2 : (0 - 0 + 2 : ℕ) = 2 := by omega
      simp only [e1, e2] at hex0
      rw [hW0, hCA] at hex0
      linear_combination hex0
    have hfin := final_from_E (a := a) (A := A) (n := 0) (X := X) hA_ne hE
    simpa [hXdef] using hfin
  · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    have hn1 : n = m + 1 := hm
    set f : ℕ → ℝ := fun j => ((n.choose j : ℝ) * W j * X (n - j + 2)) with hfdef
    have hS2_eq : (∑ j ∈ Finset.range (n + 1), f j)
        = (∑ i ∈ Finset.range m, f (i + 2)) + f 1 + f 0 := by
      have h1 : (∑ j ∈ Finset.range (m + 2), f j)
          = (∑ j ∈ Finset.range (m + 1), f (j + 1)) + f 0 :=
        Finset.sum_range_succ' f (m + 1)
      have h2 : (∑ j ∈ Finset.range (m + 1), f (j + 1))
          = (∑ j ∈ Finset.range m, f (j + 1 + 1)) + f (0 + 1) :=
        Finset.sum_range_succ' (fun j => f (j + 1)) m
      have hn_eq : n + 1 = m + 2 := by omega
      have hcongr : (∑ j ∈ Finset.range m, f (j + 1 + 1))
          = ∑ i ∈ Finset.range m, f (i + 2) := by
        apply Finset.sum_congr rfl
        intro j _
        rfl
      rw [hn_eq, h1, h2, hcongr]
    have hf0 : f 0 = (a + C) * X (n + 2) := by
      simp only [hfdef]
      have c0 : ((n.choose 0 : ℕ) : ℝ) = 1 := by simp
      have e : n - 0 + 2 = n + 2 := by omega
      rw [c0, e, hW0]
      ring
    have hf1 : f 1 = (n : ℝ) * (X 1 + 1) * X (n + 1) := by
      simp only [hfdef]
      have c1 : ((n.choose 1 : ℕ) : ℝ) = (n : ℝ) := by simp [Nat.choose_one_right]
      have e : n - 1 + 2 = n + 1 := by omega
      rw [c1, e, hW1]
    have hrest : (∑ i ∈ Finset.range m, f (i + 2))
        = ∑ j ∈ Finset.Icc 2 n, ((n.choose j : ℝ) * (X j * X (n + 2 - j))) := by
      have hstep : (∑ i ∈ Finset.range m, f (i + 2))
          = ∑ i ∈ Finset.range m, ((n.choose (i + 2) : ℝ) * (X (i + 2) * X (n + 2 - (i + 2)))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi_le : i + 2 ≤ n := by
          have := Finset.mem_range.mp hi
          omega
        simp only [hfdef]
        rw [hWge (i + 2) (by omega)]
        have e : n - (i + 2) + 2 = n + 2 - (i + 2) := by omega
        rw [e]
        ring
      rw [hstep]
      have hbb := rest_eq (G := fun j => ((n.choose j : ℝ) * (X j * X (n + 2 - j)))) (m := m)
      have hn_eq : m + 1 = n := by omega
      rw [hn_eq] at hbb
      exact hbb
    have hcomb := comb_identity (X := X) (n := n)
    have hE : a * A * (X (n + 2)) + (n : ℝ) * (X (n + 1))
        + (∑ k ∈ Finset.Icc 1 (n + 1), (((n + 1).choose k : ℝ) * (X k * X (n + 2 - k)))) = 0 := by
      have h0 := hexpand_XW
      rw [hS2_eq, hf0, hf1, hrest] at h0
      have hf1exp : (n : ℝ) * (X 1 + 1) * X (n + 1)
          = (n : ℝ) * (X (n + 1)) + (n : ℝ) * (X 1 * X (n + 1)) := by ring
      rw [hf1exp, hCA] at h0
      have hS1congr : (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * X (i + 1) * X (n - i + 1)))
          = ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * (X (i + 1) * X (n - i + 1))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hS1congr] at h0
      linear_combination h0 - hcomb
    exact final_from_E (a := a) (A := A) (n := n) (X := X) hA_ne hE

/-- **Taylor coefficients of the solution of $x^x = a^a e^h$ (Chapter 3, Entry 17).** For every
real number $a > 1/e$ there exist a real number $R > 0$ and a function
$x : \mathbb{R} \to \mathbb{R}$, analytic at $0$, with $x(0) = a$, such that $x(h) > 0$ and
$x(h)^{x(h)} = a^a e^h$ for all real $h$ with $|h| < R$, and such that the numbers
$A_k = (-a)^{k-1} x^{(k)}(0)$ for $k \ge 1$ satisfy, for every integer $r \ge 2$,
$$A_r = \frac{(r - 2)\, A_{r-1} + \sum_{k=1}^{r-1} \binom{r-1}{k} A_k A_{r-k}}{1 + \log a}.$$

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, corrected Entry 17, formulas
    (17.1)--(17.7), printed pp. 81--83 / PDF pp. 91--93.
Proves `Wanted` entry `ramanujan_part1_ch3_entry17`.
-/
theorem ramanujan_part1_ch3_entry17 :
    ∀ (a : ℝ), 1 / Real.exp 1 < a →
        ∃ (R : ℝ) (x : ℝ → ℝ), 0 < R ∧ AnalyticAt ℝ x (0 : ℝ) ∧ x 0 = a ∧
            (∀ h : ℝ, |h| < R → 0 < x h ∧ x h ^ x h = a ^ a * Real.exp h) ∧ ∀ r : ℕ, 2 ≤ r →
                (-a) ^ (r - 1) * iteratedDeriv r x 0 = (1 + Real.log a)⁻¹ * ((r : ℝ) - 2) *
                    ((-a) ^ (r - 2) * iteratedDeriv (r - 1) x 0) + (1 + Real.log a)⁻¹ *
                        ∑ k ∈ Finset.Icc 1 (r - 1), (Nat.choose (r - 1) k : ℝ) *
                            ((-a) ^ (k - 1) * iteratedDeriv k x 0) *
                                ((-a) ^ (r - k - 1) * iteratedDeriv (r - k) x 0) := by
  intro a ha
  have ha_pos : 0 < a := lt_trans (by positivity) ha
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have h1exp : (1 : ℝ) / Real.exp 1 = Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
  have hlog : (-1 : ℝ) < Real.log a := by
    have h1 : Real.exp (-1) < a := by rw [← h1exp]; exact ha
    have h2 : Real.log (Real.exp (-1)) < Real.log a :=
      Real.log_lt_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hLa_pos : (0:ℝ) < 1 + Real.log a := by linarith
  have hA_ne : (1 + Real.log a) ≠ 0 := ne_of_gt hLa_pos
  have hderiv_ne : deriv (fun y => y * Real.log y) a ≠ 0 := by
    have hhd : HasDerivAt (fun y => y * Real.log y) (Real.log a + 1) a :=
      Real.hasDerivAt_mul_log ha_ne
    have hder : deriv (fun y => y * Real.log y) a = Real.log a + 1 := hhd.deriv
    rw [hder]
    have : Real.log a + 1 = 1 + Real.log a := by ring
    rw [this]
    exact ne_of_gt hLa_pos
  have hf_an : AnalyticAt ℝ (fun y => y * Real.log y) a := by
    apply AnalyticAt.mul analyticAt_id
    apply AnalyticAt.log analyticAt_id ha_pos
  have hStrict : HasStrictDerivAt (fun y => y * Real.log y)
      (deriv (fun y => y * Real.log y) a) a := hf_an.hasStrictDerivAt
  have hFderiv : HasStrictFDerivAt (fun y => y * Real.log y) _ a :=
    hStrict.hasStrictFDerivAt_equiv hderiv_ne
  have hg_an : AnalyticAt ℝ (hStrict.localInverse _ _ _ hderiv_ne)
      ((fun y => y * Real.log y) a) :=
    hf_an.analyticAt_localInverse hderiv_ne
  have hg0 : hStrict.localInverse _ _ _ hderiv_ne ((fun y => y * Real.log y) a) = a :=
    hFderiv.localInverse_apply_image
  have hevR := hStrict.eventually_right_inverse hderiv_ne
  set x : ℝ → ℝ := fun h => hStrict.localInverse _ _ _ hderiv_ne
    ((fun y => y * Real.log y) a + h) with hx_def
  have hinner : AnalyticAt ℝ (fun h : ℝ => (fun y => y * Real.log y) a + h) (0:ℝ) := by
    have h1 : AnalyticAt ℝ (fun _ : ℝ => (fun y => y * Real.log y) a) (0:ℝ) :=
      analyticAt_const
    have h2 : AnalyticAt ℝ (fun h : ℝ => h) (0:ℝ) := analyticAt_id
    have h3 : AnalyticAt ℝ ((fun _ : ℝ => (fun y => y * Real.log y) a) +
      (fun h : ℝ => h)) (0:ℝ) := h1.add h2
    have heq : ((fun _ : ℝ => (fun y => y * Real.log y) a) + (fun h : ℝ => h)) =
        (fun h : ℝ => (fun y => y * Real.log y) a + h) := by
      funext h; rfl
    rwa [heq] at h3
  have hinner0 : (fun h : ℝ => (fun y => y * Real.log y) a + h) (0:ℝ) =
      (fun y => y * Real.log y) a := by simp
  have hg_an' : AnalyticAt ℝ (hStrict.localInverse _ _ _ hderiv_ne)
      ((fun h : ℝ => (fun y => y * Real.log y) a + h) (0:ℝ)) := by rwa [hinner0]
  have hcomp := hg_an'.comp hinner
  have hx_an : AnalyticAt ℝ x 0 := by
    have heq : x = (hStrict.localInverse _ _ _ hderiv_ne) ∘
        (fun h : ℝ => (fun y => y * Real.log y) a + h) := rfl
    rw [heq]
    exact hcomp
  have hx0 : x 0 = a := by
    have : x 0 = hStrict.localInverse _ _ _ hderiv_ne
      ((fun y => y * Real.log y) a + 0) := rfl
    rw [this, add_zero]
    exact hg0
  have hx_cont : ContinuousAt x 0 := hx_an.continuousAt
  have hev_pos : ∀ᶠ h in nhds (0:ℝ), 0 < x h := by
    have h0pos : 0 < x 0 := by rw [hx0]; exact ha_pos
    exact hx_cont.eventually (eventually_gt_nhds h0pos)
  have hev_inv : ∀ᶠ h in nhds (0:ℝ), (fun y => y * Real.log y) (x h) =
      (fun y => y * Real.log y) a + h := by
    have htend0 : Filter.Tendsto (fun h : ℝ => (fun y => y * Real.log y) a + h)
        (nhds (0:ℝ)) (nhds ((fun y => y * Real.log y) a + 0)) :=
      tendsto_const_nhds.add Filter.tendsto_id
    have htend : Filter.Tendsto (fun h : ℝ => (fun y => y * Real.log y) a + h)
        (nhds (0:ℝ)) (nhds ((fun y => y * Real.log y) a)) := by
      simpa using htend0
    have hev2 := htend.eventually hevR
    simpa [hx_def] using hev2
  rw [Metric.eventually_nhds_iff_ball] at hev_pos hev_inv
  obtain ⟨R1, hR1, hball1⟩ := hev_pos
  obtain ⟨R2, hR2, hball2⟩ := hev_inv
  have hRpos : 0 < min R1 R2 := lt_min hR1 hR2
  have hball_log : ∀ h : ℝ, |h| < min R1 R2 →
      0 < x h ∧ x h * Real.log (x h) = (a * Real.log a) + h := by
    intro h hh
    have hdist1 : dist h 0 < R1 := by
      have e : dist h (0:ℝ) = |h| := by simp [dist_eq_norm, Real.norm_eq_abs, sub_zero]
      rw [e]
      exact lt_of_lt_of_le hh (min_le_left _ _)
    have hdist2 : dist h 0 < R2 := by
      have e : dist h (0:ℝ) = |h| := by simp [dist_eq_norm, Real.norm_eq_abs, sub_zero]
      rw [e]
      exact lt_of_lt_of_le hh (min_le_right _ _)
    have hm1 : h ∈ Metric.ball (0:ℝ) R1 := Metric.mem_ball.mpr hdist1
    have hm2 : h ∈ Metric.ball (0:ℝ) R2 := Metric.mem_ball.mpr hdist2
    have hpos : 0 < x h := hball1 h hm1
    have hfinv : (fun y => y * Real.log y) (x h) =
        (fun y => y * Real.log y) a + h := hball2 h hm2
    refine ⟨hpos, ?_⟩
    simpa using hfinv
  have hball_all : ∀ h : ℝ, |h| < min R1 R2 →
      0 < x h ∧ x h ^ x h = a ^ a * Real.exp h := by
    intro h hh
    obtain ⟨hpos, hlog_eq⟩ := hball_log h hh
    refine ⟨hpos, ?_⟩
    have hrpow_x : (x h : ℝ) ^ (x h : ℝ) = Real.exp (x h * Real.log (x h)) := by
      rw [Real.rpow_def_of_pos hpos, mul_comm]
    have hrpow_a : (a : ℝ) ^ (a : ℝ) = Real.exp (a * Real.log a) := by
      rw [Real.rpow_def_of_pos ha_pos, mul_comm]
    rw [hrpow_x, hrpow_a, hlog_eq, Real.exp_add]
  have hCA : a + (a * Real.log a) = a * (1 + Real.log a) := by ring
  have hRec : ∀ r : ℕ, 2 ≤ r →
      (-a) ^ (r - 1) * iteratedDeriv r x 0 = (1 + Real.log a)⁻¹ * ((r : ℝ) - 2) *
          ((-a) ^ (r - 2) * iteratedDeriv (r - 1) x 0) + (1 + Real.log a)⁻¹ *
              ∑ k ∈ Finset.Icc 1 (r - 1), (Nat.choose (r - 1) k : ℝ) *
                  ((-a) ^ (k - 1) * iteratedDeriv k x 0) *
                      ((-a) ^ (r - k - 1) * iteratedDeriv (r - k) x 0) := by
    intro r hr
    have h := recurrence_generic (a := a) (R := min R1 R2) (C := a * Real.log a)
      (A := 1 + Real.log a) (x := x) hRpos hx_an hx0 hA_ne hCA hball_log r hr
    have hsum : (∑ k ∈ Finset.Icc 1 (r - 1), ((r - 1).choose k : ℝ) *
        (((-a) ^ (k - 1) * iteratedDeriv k x 0) * ((-a) ^ (r - k - 1) * iteratedDeriv (r - k) x 0)))
        = ∑ k ∈ Finset.Icc 1 (r - 1), ((r - 1).choose k : ℝ) *
          ((-a) ^ (k - 1) * iteratedDeriv k x 0) *
          ((-a) ^ (r - k - 1) * iteratedDeriv (r - k) x 0) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsum] at h
    exact h
  exact ⟨min R1 R2, x, hRpos, hx_an, hx0, hball_all, hRec⟩

end Entry17

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
