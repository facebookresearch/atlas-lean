/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.PSeriesComplex

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry10Zeta4
public import MathlibExt.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry2Faulhaber

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

-- Compatibility alias preserving the Entry2 API; forwards to Entry 10.
abbrev chapter7BernoulliStar (z : ℂ) : ℂ := Entry10Zeta4.chapter7BernoulliStar z

def chapter7Entry2Value (r : ℂ) : ℂ :=
  (Complex.cpow 2 (r + 1) - 1) * chapter7BernoulliStar (r + 1) *
    Complex.sin ((Real.pi : ℂ) * r / 2) / (r + 1)

def chapter7Eta (s : ℂ) : ℂ :=
  if s = 1 then (Real.log 2 : ℂ)
  else (1 - Complex.cpow 2 (1 - s)) * riemannZeta s

def chapter7NatCpow (n : ℕ) (r : ℂ) : ℂ :=
  Complex.cpow (n : ℂ) r

def chapter7EtaTerm (s : ℂ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j / chapter7NatCpow (j + 1) s

def chapter7EtaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ range N, chapter7EtaTerm s j

-- Helper: Differentiable -> Meromorphic.
private lemma meromorphic_of_differentiable {f : ℂ → ℂ} (h : Differentiable ℂ f) :
    Meromorphic f :=
  fun x => (h.analyticAt x).meromorphicAt

-- Helper: cpow with constant base 2 of (1 - s), in exact syntactic form.
private lemma diff_cpow_two_one_sub :
    Differentiable ℂ (fun s : ℂ => Complex.cpow 2 (1 - s)) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hexp : (fun s : ℂ => Complex.cpow 2 (1 - s))
      = fun s => Complex.exp (Complex.log 2 * (1 - s)) := by
    ext s
    exact Complex.cpow_def_of_ne_zero h2 (1 - s)
  rw [hexp]
  fun_prop

private lemma meromorphic_cpow_two_one_sub :
    Meromorphic (fun s : ℂ => Complex.cpow 2 (1 - s)) :=
  meromorphic_of_differentiable diff_cpow_two_one_sub

-- Zeta is meromorphic on all of ℂ (removable-singularity completion at 1).
private lemma meromorphic_riemannZeta : Meromorphic riemannZeta :=
  meromorphicOn_univ.mp meromorphicOn_riemannZeta

-- Eta is meromorphic on all of ℂ (the factor `1 - 2 ^ (1 - s)` removes the pole).
private lemma meromorphic_chapter7Eta : Meromorphic chapter7Eta := by
  have hg : Meromorphic (fun s : ℂ => (1 - Complex.cpow 2 (1 - s)) * riemannZeta s) :=
    ((meromorphic_of_differentiable (differentiable_const 1)).sub
      meromorphic_cpow_two_one_sub).mul meromorphic_riemannZeta
  intro x
  by_cases hx : x = 1
  · subst hx
    apply MeromorphicAt.congr (f := fun s : ℂ => (1 - Complex.cpow 2 (1 - s)) * riemannZeta s)
    · exact hg 1
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : s ≠ 1 := hs
      unfold chapter7Eta
      simp [hs']
  · apply MeromorphicAt.congr (f := fun s : ℂ => (1 - Complex.cpow 2 (1 - s)) * riemannZeta s)
    · exact hg x
    · have h1 : ({1}ᶜ : Set ℂ) ∈ 𝓝[≠] x :=
        mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hx)
      filter_upwards [h1, self_mem_nhdsWithin] with s hs1 hs2
      have hs1' : s ≠ 1 := hs1
      unfold chapter7Eta
      simp [hs1']

private lemma analyticOnNhd_neg_univ : AnalyticOnNhd ℂ (fun r : ℂ => -r) Set.univ := by
  have h : Differentiable ℂ (fun r : ℂ => -r) := by fun_prop
  exact (differentiableOn_univ.mpr h).analyticOnNhd isOpen_univ

private lemma meromorphic_eta_neg :
    MeromorphicOn (fun r : ℂ => chapter7Eta (-r)) Set.univ :=
  Meromorphic.comp_analyticOnNhd meromorphic_chapter7Eta analyticOnNhd_neg_univ

private lemma analyticOnNhd_add_one : AnalyticOnNhd ℂ (fun r : ℂ => r + 1) Set.univ := by
  have h : Differentiable ℂ (fun r : ℂ => r + 1) := by fun_prop
  exact (differentiableOn_univ.mpr h).analyticOnNhd isOpen_univ

private lemma analyticOnNhd_add_one_one : AnalyticOnNhd ℂ (fun r : ℂ => r + 1 + 1) Set.univ := by
  have h : Differentiable ℂ (fun r : ℂ => r + 1 + 1) := by fun_prop
  exact (differentiableOn_univ.mpr h).analyticOnNhd isOpen_univ

private lemma diff_cpow_two_add_one :
    Differentiable ℂ (fun r : ℂ => Complex.cpow 2 (r + 1)) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hexp : (fun r : ℂ => Complex.cpow 2 (r + 1))
      = fun r => Complex.exp (Complex.log 2 * (r + 1)) := by
    ext r
    exact Complex.cpow_def_of_ne_zero h2 (r + 1)
  rw [hexp]
  fun_prop

private lemma diff_cpow_twopi_add_one :
    Differentiable ℂ (fun r : ℂ => Complex.cpow (2 * (Real.pi : ℂ)) (r + 1)) := by
  have hb : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hexp : (fun r : ℂ => Complex.cpow (2 * (Real.pi : ℂ)) (r + 1))
      = fun r => Complex.exp (Complex.log (2 * (Real.pi : ℂ)) * (r + 1)) := by
    ext r
    exact Complex.cpow_def_of_ne_zero hb (r + 1)
  rw [hexp]
  fun_prop

private lemma diff_sin_pi_half :
    Differentiable ℂ (fun r : ℂ => Complex.sin ((Real.pi : ℂ) * r / 2)) := by
  fun_prop

private lemma meromorphic_entry2Value : Meromorphic chapter7Entry2Value := by
  have h2 : Meromorphic (fun r : ℂ => Complex.cpow 2 (r + 1)) :=
    meromorphic_of_differentiable diff_cpow_two_add_one
  have h1c : Meromorphic (fun _ : ℂ => (1 : ℂ)) := Meromorphic.const 1
  have hG : Meromorphic (fun r : ℂ => Complex.Gamma (r + 1 + 1)) := by
    have h : MeromorphicOn (Complex.Gamma ∘ (fun r : ℂ => r + 1 + 1)) Set.univ :=
      (meromorphicOn_univ.mp MeromorphicOn.Gamma).comp_analyticOnNhd
        analyticOnNhd_add_one_one
    rw [meromorphicOn_univ] at h
    exact h
  have hZ : Meromorphic (fun r : ℂ => riemannZeta (r + 1)) := by
    have h : MeromorphicOn (riemannZeta ∘ (fun r : ℂ => r + 1)) Set.univ :=
      meromorphic_riemannZeta.comp_analyticOnNhd analyticOnNhd_add_one
    rw [meromorphicOn_univ] at h
    exact h
  have hP : Meromorphic (fun r : ℂ => Complex.cpow (2 * (Real.pi : ℂ)) (r + 1)) :=
    meromorphic_of_differentiable diff_cpow_twopi_add_one
  have hS : Meromorphic (fun r : ℂ => Complex.sin ((Real.pi : ℂ) * r / 2)) :=
    meromorphic_of_differentiable diff_sin_pi_half
  have hD : Meromorphic (fun r : ℂ => r + 1) :=
    meromorphic_of_differentiable (by fun_prop)
  have hstar : Meromorphic (fun r : ℂ => chapter7BernoulliStar (r + 1)) := by
    have hnum : Meromorphic (fun r : ℂ => 2 * Complex.Gamma (r + 1 + 1) * riemannZeta (r + 1)) :=
      ((Meromorphic.const 2).mul hG).mul hZ
    have h := hnum.div hP
    unfold chapter7BernoulliStar Entry10Zeta4.chapter7BernoulliStar
    exact h
  unfold chapter7Entry2Value
  exact (((h2.sub h1c).mul hstar).mul hS).div hD

-- Pointwise identity at good points, via the Riemann zeta functional equation.
private lemma eta_eq_entry2_of_good (r : ℂ) (hr0 : r ≠ 0) (hr1 : -r ≠ 1)
    (hrs : ∀ n : ℕ, r + 1 ≠ -(n : ℂ)) :
    chapter7Eta (-r) = chapter7Entry2Value r := by
  have hs1 : r + 1 ≠ 1 := fun h => hr0 (by linear_combination h)
  have hs0 : r + 1 ≠ 0 := by
    have h0 := hrs 0
    simpa using h0
  have hfe := riemannZeta_one_sub (s := r + 1) hrs hs1
  have e1 : (1 : ℂ) - -r = r + 1 := by ring
  have e2 : (1 : ℂ) - (r + 1) = -r := by ring
  have htrig : Complex.cos ((Real.pi : ℂ) * (r + 1) / 2)
      = -Complex.sin ((Real.pi : ℂ) * r / 2) := by
    have harg : (Real.pi : ℂ) * (r + 1) / 2
        = (Real.pi : ℂ) * r / 2 + (Real.pi : ℂ) / 2 := by ring
    rw [harg, Complex.cos_add, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  have hGamma : Complex.Gamma (r + 1 + 1) = (r + 1) * Complex.Gamma (r + 1) :=
    Complex.Gamma_add_one (r + 1) hs0
  have hbase : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hcp : (2 * (Real.pi : ℂ)) ^ (-(r + 1))
      = ((2 * (Real.pi : ℂ)) ^ (r + 1))⁻¹ := Complex.cpow_neg _ _
  have hcp2 : Complex.cpow (2 * (Real.pi : ℂ)) (r + 1)
      = (2 * (Real.pi : ℂ)) ^ (r + 1) := rfl
  have hpow_ne : (2 * (Real.pi : ℂ)) ^ (r + 1) ≠ 0 := by
    intro hcon
    exact hbase (((Complex.cpow_eq_zero_iff _ _).mp hcon).1)
  unfold chapter7Eta chapter7Entry2Value chapter7BernoulliStar Entry10Zeta4.chapter7BernoulliStar
  split_ifs with h
  · exact absurd h hr1
  · rw [e1, ← e2, hfe, htrig, hGamma, hcp, hcp2]
    field_simp
    ring

-- The exceptional set for the functional equation.
private def chapter7Entry2BadSet : Set ℂ := {r : ℂ | ∃ n : ℕ, r = -(n : ℂ)}

private lemma bad_inter_ball_finite (x : ℂ) :
    (chapter7Entry2BadSet ∩ Metric.ball x 1).Finite := by
  have hsub : chapter7Entry2BadSet ∩ Metric.ball x 1
      ⊆ (fun n : ℕ => (-(n : ℂ) : ℂ)) '' {n : ℕ | (n : ℝ) < 1 + ‖x‖} := by
    rintro r ⟨hrbad, hmem⟩
    obtain ⟨n, rfl⟩ := hrbad
    have hdist : dist (-(n : ℂ) : ℂ) x < 1 := Metric.mem_ball.mp hmem
    rw [dist_eq_norm] at hdist
    have htri : (n : ℝ) ≤ ‖(-(n : ℂ) : ℂ) - x‖ + ‖x‖ := by
      have heq : (-(n : ℂ) : ℂ) = ((-(n : ℂ) : ℂ) - x) + x := by abel
      have h := norm_add_le ((-(n : ℂ) : ℂ) - x) x
      rw [← heq, norm_neg, Complex.norm_natCast] at h
      exact h
    have hmem' : n ∈ {n : ℕ | (n : ℝ) < 1 + ‖x‖} := by
      change (n : ℝ) < 1 + ‖x‖
      linarith
    exact ⟨n, hmem', rfl⟩
  have hnat : {n : ℕ | (n : ℝ) < 1 + ‖x‖}.Finite := by
    apply Set.Finite.subset
      (Finset.finite_toSet (Finset.range (Nat.ceil (1 + ‖x‖) + 1)))
    intro n hn
    have hn' : (n : ℝ) < 1 + ‖x‖ := hn
    simp only [Finset.mem_coe, Finset.mem_range]
    have h2 : (1 + ‖x‖ : ℝ) ≤ (Nat.ceil (1 + ‖x‖) : ℝ) := Nat.le_ceil _
    have h1 : (n : ℝ) < ((Nat.ceil (1 + ‖x‖) + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h1
  exact (hnat.image _).subset hsub

private lemma good_of_not_bad (r : ℂ) (hr : r ∉ chapter7Entry2BadSet) :
    r ≠ 0 ∧ -r ≠ 1 ∧ ∀ n : ℕ, r + 1 ≠ -(n : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    exact hr ⟨0, by simp [h0]⟩
  · intro h1
    apply hr
    refine ⟨1, ?_⟩
    have hr1 : r = (-1 : ℂ) := by linear_combination -h1
    simpa using hr1
  · intro n hn
    apply hr
    refine ⟨n + 1, ?_⟩
    push_cast
    linear_combination hn

private lemma eta_eq_entry2_codiscrete :
    (fun r : ℂ => chapter7Eta (-r)) =ᶠ[codiscrete ℂ] chapter7Entry2Value := by
  rw [eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE]
  intro x
  have hU : Metric.ball x 1 ∈ 𝓝[≠] x :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x one_pos)
  have hmem : Metric.ball x 1 \ (chapter7Entry2BadSet ∩ Metric.ball x 1) ∈ 𝓝[≠] x :=
    nhdsNE_of_nhdsNE_sdiff_finite hU (bad_inter_ball_finite x)
  filter_upwards [hmem] with r hr
  rw [Set.mem_sdiff] at hr
  obtain ⟨hrball, hrnot⟩ := hr
  rw [Set.mem_inter_iff] at hrnot
  have hrgood : r ∉ chapter7Entry2BadSet := fun hbad => hrnot ⟨hbad, hrball⟩
  obtain ⟨hr0, hr1, hrs⟩ := good_of_not_bad r hrgood
  exact eta_eq_entry2_of_good r hr0 hr1 hrs

private noncomputable def chapter7EtaChar : ZMod 2 → ℂ :=
  fun a => if a = 0 then -1 else 1

private lemma etaChar_sum : ∑ j : ZMod 2, chapter7EtaChar j = 0 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [chapter7EtaChar]

private lemma etaChar_cast_succ (j : ℕ) :
    chapter7EtaChar (↑(j + 1) : ZMod 2) = (-1 : ℂ) ^ j := by
  rcases Nat.even_or_odd j with hj | hj
  · have hodd : Odd (j + 1) := hj.add_one
    have hne : (↑(j + 1) : ZMod 2) ≠ 0 := by
      intro h0
      have hev : Even (j + 1) := ZMod.natCast_eq_zero_iff_even.mp h0
      exact (Nat.not_even_iff_odd.mpr hodd) hev
    unfold chapter7EtaChar
    rw [ite_eq_right hne, hj.neg_one_pow]
  · have hev : Even (j + 1) := hj.add_one
    have h0 : (↑(j + 1) : ZMod 2) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr hev
    unfold chapter7EtaChar
    rw [ite_eq_left h0, hj.neg_one_pow]

private noncomputable def chapter7EtaPair (n : ℕ) (s : ℂ) : ℂ :=
  chapter7EtaTerm s (2 * n) + chapter7EtaTerm s (2 * n + 1)

private lemma etaTerm_eq_mul_neg_cpow (s : ℂ) (j : ℕ) :
    chapter7EtaTerm s j = (-1 : ℂ) ^ j * (((j + 1 : ℕ) : ℂ) ^ (-s)) := by
  have hcpow : ∀ x : ℂ, Complex.cpow x s = x ^ s := fun x => rfl
  unfold chapter7EtaTerm chapter7NatCpow
  rw [hcpow, div_eq_mul_inv, ← Complex.cpow_neg]

private lemma etaPair_eq_sub (n : ℕ) (s : ℂ) :
    chapter7EtaPair n s
      = (((2 * n + 1 : ℕ) : ℂ) ^ (-s)) - (((2 * n + 2 : ℕ) : ℂ) ^ (-s)) := by
  unfold chapter7EtaPair
  rw [etaTerm_eq_mul_neg_cpow, etaTerm_eq_mul_neg_cpow]
  have hpow_even : (-1 : ℂ) ^ (2 * n) = 1 := by
    rw [pow_mul]
    norm_num
  have hpow_odd : (-1 : ℂ) ^ (2 * n + 1) = -1 := by
    rw [pow_succ, hpow_even, one_mul]
  have hcast : 2 * n + 1 + 1 = 2 * n + 2 := by omega
  rw [hpow_even, hpow_odd, hcast, one_mul, neg_one_mul]
  ring

private lemma diff_neg_cpow_of_ne_zero {c : ℂ} (hc : c ≠ 0) :
    Differentiable ℂ (fun s : ℂ => c ^ (-s)) := by
  have hneg : Differentiable ℂ (fun s : ℂ => -s) := by fun_prop
  exact hneg.const_cpow (Or.inl hc)

private lemma diff_etaTerm (j : ℕ) :
    Differentiable ℂ (fun s : ℂ => chapter7EtaTerm s j) := by
  have hc : (((j + 1 : ℕ) : ℂ) ≠ 0) := by
    exact_mod_cast Nat.succ_ne_zero j
  have hpow : Differentiable ℂ (fun s : ℂ => (((j + 1 : ℕ) : ℂ) ^ (-s))) :=
    diff_neg_cpow_of_ne_zero hc
  have hmul : Differentiable ℂ
      (fun s : ℂ => (-1 : ℂ) ^ j * ((((j + 1 : ℕ) : ℂ) ^ (-s)))) :=
    hpow.const_mul _
  have heq : (fun s : ℂ => chapter7EtaTerm s j)
      = (fun s : ℂ => (-1 : ℂ) ^ j * ((((j + 1 : ℕ) : ℂ) ^ (-s)))) := by
    ext s
    exact etaTerm_eq_mul_neg_cpow s j
  rw [heq]
  exact hmul

private lemma diff_etaPair (n : ℕ) : Differentiable ℂ (chapter7EtaPair n) := by
  unfold chapter7EtaPair
  exact (diff_etaTerm (2 * n)).add (diff_etaTerm (2 * n + 1))

private lemma etaPair_norm_le_aux_zero (n : ℕ) (δ M : ℝ)
    (hM : (0 : ℝ) ≤ M) :
    ‖chapter7EtaPair n 0‖ ≤ M / (((n + 1 : ℕ) : ℝ) ^ (δ + 1)) := by
  have hpair : chapter7EtaPair n 0 = 0 := by
    rw [etaPair_eq_sub]
    simp
  rw [hpair, norm_zero]
  have hpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) ^ (δ + 1)) := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast Nat.succ_pos n
  exact div_nonneg hM hpos.le

private lemma etaPair_deriv_bound (n : ℕ) (s : ℂ) (δ M : ℝ) (t : ℝ)
    (hδpos : 0 < δ) (hδ : δ ≤ s.re) (hM : ‖s‖ ≤ M) (hs0 : s ≠ 0)
    (ht1 : 2 * (n : ℝ) + 1 ≤ t) (_ht2 : t ≤ 2 * (n : ℝ) + 2) :
    ‖deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t‖
      ≤ M / ((((n + 1 : ℕ) : ℝ)) ^ (δ + 1)) := by
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have ht_pos : 0 < t := by linarith
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have h1t : (1 : ℝ) ≤ t := by linarith
  have hnpos : (0 : ℝ) < ((n : ℝ) + 1) := by linarith
  have hle_nt : (n : ℝ) + 1 ≤ t := by linarith
  have hc_ne : (-s) ≠ 0 := neg_ne_zero.mpr hs0
  have hderiv : deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t
      = (-s) * ((t : ℂ) ^ (-s - 1)) :=
    Complex.deriv_ofReal_cpow_const ht_ne hc_ne
  rw [hderiv, norm_mul, norm_neg]
  have hnorm : ‖((t : ℂ) ^ (-s - 1))‖ = t ^ ((-s - 1).re) :=
    Complex.norm_cpow_eq_rpow_re_of_pos ht_pos (-s - 1)
  rw [hnorm]
  have hre : (-s - 1).re = -s.re - 1 := by simp
  rw [hre]
  have hexp_le : -s.re - 1 ≤ -δ - 1 := by linarith
  have hstep1 : t ^ (-s.re - 1) ≤ t ^ (-δ - 1) :=
    Real.rpow_le_rpow_of_exponent_le h1t hexp_le
  have hexp_nonpos : -δ - 1 ≤ 0 := by linarith
  have hstep2 : t ^ (-δ - 1) ≤ ((n : ℝ) + 1) ^ (-δ - 1) :=
    Real.rpow_le_rpow_of_nonpos hnpos hle_nt hexp_nonpos
  have hpow_le : t ^ (-s.re - 1) ≤ ((n : ℝ) + 1) ^ (-δ - 1) :=
    le_trans hstep1 hstep2
  have hM_nonneg : (0 : ℝ) ≤ M := le_trans (norm_nonneg s) hM
  have hrpow_nonneg : (0 : ℝ) ≤ t ^ (-s.re - 1) :=
    Real.rpow_nonneg ht_pos.le _
  have hbase_nonneg : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-δ - 1) :=
    Real.rpow_nonneg hnpos.le _
  have hmul_le : ‖s‖ * (t ^ (-s.re - 1))
      ≤ M * (((n : ℝ) + 1) ^ (-δ - 1)) := by
    calc ‖s‖ * (t ^ (-s.re - 1))
        ≤ ‖s‖ * (((n : ℝ) + 1) ^ (-δ - 1)) :=
          mul_le_mul_of_nonneg_left hpow_le (norm_nonneg s)
      _ ≤ M * (((n : ℝ) + 1) ^ (-δ - 1)) :=
          mul_le_mul_of_nonneg_right hM hbase_nonneg
  have hexp_eq : -δ - 1 = -(δ + 1) := by ring
  have hrpow_eq : (((n : ℝ) + 1) ^ (-δ - 1))
      = ((((n : ℝ) + 1) ^ (δ + 1))⁻¹) := by
    rw [hexp_eq, Real.rpow_neg hnpos.le]
  have hcast_eq : ((n : ℝ) + 1) = (((n + 1 : ℕ) : ℝ)) := by push_cast; ring
  rw [hcast_eq] at hmul_le hrpow_eq
  rw [hrpow_eq] at hmul_le
  rw [div_eq_mul_inv]
  exact hmul_le

private lemma etaPair_norm_le (n : ℕ) (s : ℂ) (δ M : ℝ)
    (hδpos : 0 < δ) (hδ : δ ≤ s.re) (hM : ‖s‖ ≤ M) :
    ‖chapter7EtaPair n s‖ ≤ M / ((((n + 1 : ℕ) : ℝ)) ^ (δ + 1)) := by
  by_cases hs0 : s = 0
  · subst hs0
    have hM0 : (0 : ℝ) ≤ M := by
      calc (0 : ℝ) = ‖(0 : ℂ)‖ := by simp
        _ ≤ M := hM
    exact etaPair_norm_le_aux_zero n δ M hM0
  · set a : ℝ := 2 * (n : ℝ) + 1 with ha
    set b : ℝ := 2 * (n : ℝ) + 2 with hb
    set C : ℝ := M / ((((n + 1 : ℕ) : ℝ)) ^ (δ + 1)) with hC
    set f : ℝ → ℂ := fun y : ℝ => (y : ℂ) ^ (-s) with hf
    have hab : a ≤ b := by simp only [ha, hb]; linarith
    have hxs : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
    have hys : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
    have hconvex : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hf_diff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x := by
      intro x hx
      have hx1 : a ≤ x := (Set.mem_Icc.mp hx).1
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hx_pos : (0 : ℝ) < x := by simp only [ha] at hx1; linarith
      have hx_ne : x ≠ 0 := ne_of_gt hx_pos
      have hc_ne : (-s) ≠ 0 := neg_ne_zero.mpr hs0
      exact (hasDerivAt_ofReal_cpow_const hx_ne hc_ne).differentiableAt
    have hbound : ∀ x ∈ Set.Icc a b, ‖deriv f x‖ ≤ C := by
      intro x hx
      have hx1 : a ≤ x := (Set.mem_Icc.mp hx).1
      have hx2 : x ≤ b := (Set.mem_Icc.mp hx).2
      simp only [ha, hb] at hx1 hx2
      simp only [hf, hC]
      exact etaPair_deriv_bound n s δ M x hδpos hδ hM hs0 hx1 hx2
    have hmvt : ‖f b - f a‖ ≤ C * ‖b - a‖ :=
      hconvex.norm_image_sub_le_of_norm_deriv_le hf_diff hbound hxs hys
    have hba : ‖b - a‖ = 1 := by
      simp [ha, hb]
      norm_num
    rw [hba, mul_one] at hmvt
    have hcast1 : a = (((2 * n + 1 : ℕ)) : ℝ) := by
      simp only [ha]; push_cast; ring
    have hcast2 : b = (((2 * n + 2 : ℕ)) : ℝ) := by
      simp only [hb]; push_cast; ring
    have hfa : f a = (((2 * n + 1 : ℕ) : ℂ) ^ (-s)) := by
      simp only [hf]
      rw [hcast1, Complex.ofReal_natCast]
    have hfb : f b = (((2 * n + 2 : ℕ) : ℂ) ^ (-s)) := by
      simp only [hf]
      rw [hcast2, Complex.ofReal_natCast]
    have hpair : chapter7EtaPair n s = f a - f b := by
      rw [etaPair_eq_sub, hfa, hfb]
    rw [hpair, norm_sub_rev]
    simp only [hC] at hmvt ⊢
    exact hmvt

private lemma summable_pair_bound (δ M : ℝ) (hδ : 0 < δ) :
    Summable (fun n : ℕ => M / ((((n + 1 : ℕ) : ℝ)) ^ (δ + 1))) := by
  have hsumm : Summable (fun n : ℕ => 1 / |((n : ℝ) + 1)| ^ (δ + 1)) :=
    (Real.summable_one_div_nat_add_rpow 1 (δ + 1)).mpr (by linarith)
  have heq : (fun n : ℕ => M / ((((n + 1 : ℕ) : ℝ)) ^ (δ + 1)))
      = (fun n : ℕ => M * (1 / |((n : ℝ) + 1)| ^ (δ + 1))) := by
    ext n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have habs : |((n : ℝ) + 1)| = ((n : ℝ) + 1) := abs_of_pos hpos
    have hcast : ((((n + 1 : ℕ)) : ℝ)) = ((n : ℝ) + 1) := by push_cast; ring
    have habscast : |((n : ℝ) + 1)| = ((((n + 1 : ℕ)) : ℝ)) :=
      habs.trans hcast.symm
    rw [habscast, div_eq_mul_one_div]
  rw [heq]
  exact Summable.mul_left M hsumm

private lemma isOpen_etaPairSet (δ M : ℝ) :
    IsOpen {s : ℂ | δ < s.re ∧ ‖s‖ < M} := by
  have h1 : IsOpen {s : ℂ | δ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {s : ℂ | ‖s‖ < M} :=
    isOpen_lt continuous_norm continuous_const
  have heq : {s : ℂ | δ < s.re ∧ ‖s‖ < M}
      = {s : ℂ | δ < s.re} ∩ {s : ℂ | ‖s‖ < M} := rfl
  rw [heq]
  exact h1.inter h2

private lemma diffOn_etaPairTsum (δ M : ℝ) (hδ : 0 < δ) :
    DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, chapter7EtaPair n w)
      {s : ℂ | δ < s.re ∧ ‖s‖ < M} := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun n : ℕ => M / ((((n + 1 : ℕ) : ℝ)) ^ (δ + 1)))
    (summable_pair_bound δ M hδ)
  · intro n
    exact (diff_etaPair n).differentiableOn
  · exact isOpen_etaPairSet δ M
  · intro n w hw
    simp only [Set.mem_ofPred_eq] at hw
    obtain ⟨hδw, hMw⟩ := hw
    exact etaPair_norm_le n w δ M hδ hδw.le hMw.le

private noncomputable def chapter7EtaPairTsum (s : ℂ) : ℂ :=
  ∑' n : ℕ, chapter7EtaPair n s

private lemma analyticOnNhd_etaPairTsum :
    AnalyticOnNhd ℂ chapter7EtaPairTsum {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  have hs0' : (0 : ℝ) < s0.re := hs0
  set δ : ℝ := s0.re / 2 with hδ
  set M : ℝ := ‖s0‖ + 1 with hM
  have hδpos : 0 < δ := by simp only [hδ]; linarith
  have hs0U : s0 ∈ {s : ℂ | δ < s.re ∧ ‖s‖ < M} := by
    refine ⟨?_, ?_⟩
    · simp only [hδ]; linarith
    · simp only [hM]; linarith [norm_nonneg s0]
  have hU : IsOpen {s : ℂ | δ < s.re ∧ ‖s‖ < M} := isOpen_etaPairSet δ M
  have hd : DifferentiableOn ℂ chapter7EtaPairTsum
      {s : ℂ | δ < s.re ∧ ‖s‖ < M} :=
    diffOn_etaPairTsum δ M hδpos
  exact hd.analyticAt (hU.mem_nhds hs0U)

private lemma diff_etaLFunction :
    Differentiable ℂ (ZMod.LFunction chapter7EtaChar) := by
  have : NeZero 2 := ⟨by decide⟩
  exact ZMod.differentiable_LFunction_of_sum_zero etaChar_sum

private lemma LSeries_term_eq_etaTerm (s : ℂ) (n : ℕ) :
    LSeries.term (chapter7EtaChar ·) s (n + 1) = chapter7EtaTerm s n := by
  have hterm := LSeries.term_of_ne_zero (Nat.succ_ne_zero n)
    (chapter7EtaChar ·) s
  rw [hterm, etaChar_cast_succ]
  have hcpow : ∀ x : ℂ, Complex.cpow x s = x ^ s := fun x => rfl
  unfold chapter7EtaTerm chapter7NatCpow
  rw [hcpow]

private lemma LSeries_eq_etaTsum {s : ℂ} (hs : 1 < s.re) :
    LSeries (chapter7EtaChar ·) s = ∑' j : ℕ, chapter7EtaTerm s j := by
  have : NeZero 2 := ⟨by decide⟩
  have hsum : Summable (LSeries.term (chapter7EtaChar ·) s) :=
    ZMod.LSeriesSummable_of_one_lt_re chapter7EtaChar hs
  have h0 := hsum.tsum_eq_zero_add
  simp only [LSeries.term_zero, zero_add] at h0
  have hcon : (fun n : ℕ => LSeries.term (chapter7EtaChar ·) s (n + 1))
      = (fun j : ℕ => chapter7EtaTerm s j) := by
    ext n
    exact LSeries_term_eq_etaTerm s n
  rw [hcon] at h0
  exact h0

private lemma summable_etaTerm_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    Summable (fun j : ℕ => chapter7EtaTerm s j) := by
  have h2shift : Summable (fun n : ℕ => (1 : ℂ) / (((n + 1 : ℕ) : ℂ)) ^ s) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℂ) / ((n : ℂ)) ^ s) 1).mpr
      ((summable_one_div_nat_cpow).mpr hs)
    exact h
  have hGsum : Summable (fun j : ℕ => (1 : ℂ) / (((j : ℂ)) + 1) ^ s) := by
    have hGeq : (fun j : ℕ => (1 : ℂ) / (((j : ℂ)) + 1) ^ s)
        = (fun n : ℕ => (1 : ℂ) / (((n + 1 : ℕ) : ℂ)) ^ s) := by
      ext n
      simp only [Nat.cast_add, Nat.cast_one]
    rw [hGeq]
    exact h2shift
  apply Summable.of_norm_bounded
    (g := fun j : ℕ => ‖(1 : ℂ) / (((j : ℂ)) + 1) ^ s‖) hGsum.norm _
  intro j
  have hcpow_eq : ∀ x : ℂ, Complex.cpow x s = x ^ s := fun x => rfl
  have h1 : chapter7EtaTerm s j = (-1 : ℂ) ^ j * (1 / (((j : ℂ)) + 1) ^ s) := by
    change (-1 : ℂ) ^ j / Complex.cpow (((j + 1 : ℕ) : ℂ)) s = _
    rw [hcpow_eq, div_eq_mul_one_div]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [h1, norm_mul]
  simp

private lemma pairTsum_eq_etaTsum_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    chapter7EtaPairTsum s = ∑' j : ℕ, chapter7EtaTerm s j := by
  have hFsum := summable_etaTerm_of_one_lt_re hs
  have h2k : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    dsimp at h
    omega
  have h2k1 : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h
    dsimp at h
    omega
  have hFE : Summable (fun k : ℕ => chapter7EtaTerm s (2 * k)) :=
    hFsum.comp_injective h2k
  have hFO : Summable (fun k : ℕ => chapter7EtaTerm s (2 * k + 1)) :=
    hFsum.comp_injective h2k1
  have hPeq : (∑' n : ℕ, chapter7EtaPair n s)
      = (∑' k : ℕ, chapter7EtaTerm s (2 * k))
        + (∑' k : ℕ, chapter7EtaTerm s (2 * k + 1)) := by
    have h := hFE.tsum_add hFO
    have hcon : (fun n : ℕ => chapter7EtaPair n s)
        = (fun n : ℕ => chapter7EtaTerm s (2 * n)
          + chapter7EtaTerm s (2 * n + 1)) := rfl
    rw [hcon]
    exact h
  have hsplit := tsum_even_add_odd hFE hFO
  unfold chapter7EtaPairTsum
  rw [hPeq, hsplit]

private lemma pairTsum_eq_LFunction_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    chapter7EtaPairTsum s = ZMod.LFunction chapter7EtaChar s := by
  have : NeZero 2 := ⟨by decide⟩
  have h1 := pairTsum_eq_etaTsum_of_one_lt_re hs
  have h2 := ZMod.LFunction_eq_LSeries chapter7EtaChar hs
  have h3 := LSeries_eq_etaTsum hs
  exact h1.trans (h2.trans h3).symm

private lemma analyticOnNhd_LFunction_re_pos :
    AnalyticOnNhd ℂ (ZMod.LFunction chapter7EtaChar) {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact diff_etaLFunction.differentiableOn.analyticOnNhd hopen

private lemma eventuallyEq_pairTsum_LFunction :
    chapter7EtaPairTsum =ᶠ[𝓝 (2 : ℂ)] ZMod.LFunction chapter7EtaChar := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num
  have hnhds : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := hopen.mem_nhds hmem
  filter_upwards [hnhds] with s hs
  have hs' : (1 : ℝ) < s.re := hs
  exact pairTsum_eq_LFunction_of_one_lt_re hs'

private lemma pairTsum_eq_LFunction_re_pos :
    Set.EqOn chapter7EtaPairTsum (ZMod.LFunction chapter7EtaChar)
      {s : ℂ | 0 < s.re} := by
  have hpre : IsPreconnected {s : ℂ | 0 < s.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have h0mem : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by norm_num
  exact analyticOnNhd_etaPairTsum.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_LFunction_re_pos hpre h0mem eventuallyEq_pairTsum_LFunction

private lemma eta_tendsto_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    Tendsto (chapter7EtaPartialSum s) atTop (𝓝 (chapter7Eta s)) := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have h2shift : Summable (fun n : ℕ => (1 : ℂ) / (((n + 1 : ℕ) : ℂ)) ^ s) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℂ) / ((n : ℂ)) ^ s) 1).mpr
      ((summable_one_div_nat_cpow).mpr hs)
    exact h
  have hGsum : Summable (fun j : ℕ => (1 : ℂ) / (((j : ℂ)) + 1) ^ s) := by
    have hGeq : (fun j : ℕ => (1 : ℂ) / (((j : ℂ)) + 1) ^ s)
        = (fun n : ℕ => (1 : ℂ) / (((n + 1 : ℕ) : ℂ)) ^ s) := by
      ext n
      simp only [Nat.cast_add, Nat.cast_one]
    rw [hGeq]
    exact h2shift
  have hZ : riemannZeta s = ∑' n : ℕ, (1 : ℂ) / (((n : ℂ)) + 1) ^ s :=
    zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have h2k : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    dsimp at h
    omega
  have h2k1 : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h
    dsimp at h
    omega
  have hGE : Summable (fun k : ℕ => (1 : ℂ) / (((((2 * k : ℕ)) : ℂ)) + 1) ^ s) :=
    hGsum.comp_injective h2k
  have hGO : Summable (fun k : ℕ => (1 : ℂ) / (((((2 * k + 1 : ℕ)) : ℂ)) + 1) ^ s) :=
    hGsum.comp_injective h2k1
  have hpow_even : ∀ k : ℕ, (-1 : ℂ) ^ (2 * k) = 1 := by
    intro k
    rw [pow_mul]
    norm_num
  have hpow_odd : ∀ k : ℕ, (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    intro k
    rw [pow_succ, hpow_even k, one_mul]
  have hFEterm : ∀ k : ℕ, chapter7EtaTerm s (2 * k)
      = (1 : ℂ) / (((((2 * k : ℕ)) : ℂ)) + 1) ^ s := by
    intro k
    change (-1 : ℂ) ^ (2 * k) / Complex.cpow (((2 * k + 1 : ℕ) : ℂ)) s = _
    rw [hpow_even k]
    simp only [Nat.cast_add, Nat.cast_one]
    rfl
  have hFOterm : ∀ k : ℕ, chapter7EtaTerm s (2 * k + 1)
      = -((1 : ℂ) / (((((2 * k + 1 : ℕ)) : ℂ)) + 1) ^ s) := by
    intro k
    change (-1 : ℂ) ^ (2 * k + 1) / Complex.cpow (((2 * k + 1 + 1 : ℕ) : ℂ)) s = _
    rw [hpow_odd k]
    simp only [Nat.cast_add, Nat.cast_one, neg_div]
    rfl
  have hFE : Summable (fun k : ℕ => chapter7EtaTerm s (2 * k)) := by
    have hcon : (fun k : ℕ => chapter7EtaTerm s (2 * k))
        = (fun k : ℕ => (1 : ℂ) / (((((2 * k : ℕ)) : ℂ)) + 1) ^ s) := by
      ext k
      exact hFEterm k
    rw [hcon]
    exact hGE
  have hFO : Summable (fun k : ℕ => chapter7EtaTerm s (2 * k + 1)) := by
    have hcon : (fun k : ℕ => chapter7EtaTerm s (2 * k + 1))
        = (fun k : ℕ => -((1 : ℂ) / (((((2 * k + 1 : ℕ)) : ℂ)) + 1) ^ s)) := by
      ext k
      exact hFOterm k
    rw [hcon]
    exact hGO.neg
  have hFsum : Summable (fun j : ℕ => chapter7EtaTerm s j) := by
    apply Summable.of_norm_bounded (g := fun j : ℕ => ‖(1 : ℂ) / (((j : ℂ)) + 1) ^ s‖)
      hGsum.norm _
    intro j
    have hcpow_eq : ∀ x : ℂ, Complex.cpow x s = x ^ s := fun x => rfl
    have h1 : chapter7EtaTerm s j = (-1 : ℂ) ^ j * (1 / (((j : ℂ)) + 1) ^ s) := by
      change (-1 : ℂ) ^ j / Complex.cpow (((j + 1 : ℕ) : ℂ)) s = _
      rw [hcpow_eq, div_eq_mul_one_div]
      simp only [Nat.cast_add, Nat.cast_one]
    rw [h1, norm_mul, show ‖(-1 : ℂ) ^ j‖ = 1 by simp, one_mul]
  have h2s_ne : ((2 : ℂ)) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero h2]
    exact Complex.exp_ne_zero _
  have hsplit : ∀ k : ℕ, ((2 : ℂ) * ((((k : ℕ)) : ℂ) + 1)) ^ s
      = ((2 : ℂ)) ^ s * (((((k : ℕ)) : ℂ) + 1) ^ s) := by
    intro k
    have h := Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ))
      (b := (((k : ℕ)) : ℝ) + 1) (by norm_num) (by positivity) (r := s)
    have c1 : (((2 : ℝ)) : ℂ) = (2 : ℂ) := by norm_num
    have c2 : ((((((k : ℕ)) : ℝ) + 1 : ℝ)) : ℂ) = (((((k : ℕ)) : ℂ) + 1)) := by
      push_cast
      ring
    rw [c1, c2] at h
    exact h
  have hcast2 : ∀ k : ℕ, (((((2 * k + 1 : ℕ)) : ℂ)) + 1)
      = 2 * (((((k : ℕ)) : ℂ) + 1)) := by
    intro k
    push_cast
    ring
  have hodd : ∀ k : ℕ, (1 : ℂ) / (((((2 * k + 1 : ℕ)) : ℂ)) + 1) ^ s
      = (((2 : ℂ)) ^ s)⁻¹ * (1 / (((((k : ℕ)) : ℂ) + 1) ^ s)) := by
    intro k
    rw [hcast2 k, hsplit k, one_div, one_div, mul_inv]
  have hOval : ∑' k : ℕ, (1 : ℂ) / (((((2 * k + 1 : ℕ)) : ℂ)) + 1) ^ s
      = (((2 : ℂ)) ^ s)⁻¹ * riemannZeta s := by
    have hcon : (fun k : ℕ => (1 : ℂ) / (((((2 * k + 1 : ℕ)) : ℂ)) + 1) ^ s)
        = (fun k : ℕ => (((2 : ℂ)) ^ s)⁻¹ * (1 / (((((k : ℕ)) : ℂ) + 1) ^ s))) := by
      ext k
      exact hodd k
    rw [hcon, tsum_mul_left, ← hZ]
  have hEtsum : ∑' k : ℕ, chapter7EtaTerm s (2 * k)
      = ∑' k : ℕ, (1 : ℂ) / (((((2 * k : ℕ)) : ℂ)) + 1) ^ s :=
    tsum_congr hFEterm
  have hOtsum : ∑' k : ℕ, chapter7EtaTerm s (2 * k + 1)
      = -∑' k : ℕ, (1 : ℂ) / (((((2 * k + 1 : ℕ)) : ℂ)) + 1) ^ s := by
    rw [← tsum_neg]
    exact tsum_congr hFOterm
  have splitF := tsum_even_add_odd (f := fun j : ℕ => chapter7EtaTerm s j) hFE hFO
  have splitG := tsum_even_add_odd
    (f := fun j : ℕ => (1 : ℂ) / (((j : ℂ)) + 1) ^ s) hGE hGO
  rw [hEtsum, hOtsum, hOval] at splitF
  rw [← hZ, hOval] at splitG
  have h2sub : ((2 : ℂ)) ^ (1 - s) = 2 / ((2 : ℂ)) ^ s := by
    rw [Complex.cpow_sub 1 s h2, Complex.cpow_one]
  have hFval : ∑' j : ℕ, chapter7EtaTerm s j
      = (1 - ((2 : ℂ)) ^ (1 - s)) * riemannZeta s := by
    have hE : (∑' k : ℕ, (1 : ℂ) / (((((2 * k : ℕ)) : ℂ)) + 1) ^ s)
        = riemannZeta s - (((2 : ℂ)) ^ s)⁻¹ * riemannZeta s := by
      linear_combination splitG
    rw [← splitF, hE]
    rw [h2sub]
    ring
  have hHas : HasSum (fun j : ℕ => chapter7EtaTerm s j)
      ((1 - ((2 : ℂ)) ^ (1 - s)) * riemannZeta s) := by
    rw [← hFval]
    exact hFsum.hasSum
  have hTend : Tendsto (fun N : ℕ => ∑ j ∈ range N, chapter7EtaTerm s j) atTop
      (𝓝 ((1 - ((2 : ℂ)) ^ (1 - s)) * riemannZeta s)) :=
    hHas.tendsto_sum_nat
  have hEta : chapter7Eta s = (1 - ((2 : ℂ)) ^ (1 - s)) * riemannZeta s := by
    unfold chapter7Eta
    simp [hs1]
  rw [hEta]
  have hPS : chapter7EtaPartialSum s = (fun N : ℕ => ∑ j ∈ range N, chapter7EtaTerm s j) := rfl
  rw [hPS]
  exact hTend

private lemma etaTsum_eq_zeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (∑' j : ℕ, chapter7EtaTerm s j)
      = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hsum := summable_etaTerm_of_one_lt_re hs
  have htend := eta_tendsto_of_one_lt_re hs
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hEta : chapter7Eta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
    unfold chapter7Eta
    simp [hs1]
  have hPS : chapter7EtaPartialSum s
      = (fun N : ℕ => ∑ j ∈ range N, chapter7EtaTerm s j) := rfl
  rw [hPS, hEta] at htend
  have htend2 := hsum.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique htend2 htend

private lemma LFunction_eq_zeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    ZMod.LFunction chapter7EtaChar s
      = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have : NeZero 2 := ⟨by decide⟩
  have h1 := ZMod.LFunction_eq_LSeries chapter7EtaChar hs
  have h2 := LSeries_eq_etaTsum hs
  have h3 := etaTsum_eq_zeta_of_one_lt_re hs
  rw [h1, h2, h3]

private lemma analyticOnNhd_LFunction_compl_one :
    AnalyticOnNhd ℂ (ZMod.LFunction chapter7EtaChar) ({1}ᶜ : Set ℂ) :=
  diff_etaLFunction.differentiableOn.analyticOnNhd isOpen_compl_singleton

private lemma analyticOnNhd_zetaFactor_compl_one :
    AnalyticOnNhd ℂ (fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
      ({1}ᶜ : Set ℂ) := by
  have h1 : DifferentiableOn ℂ (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - s))
      ({1}ᶜ : Set ℂ) := by
    have hdiff : Differentiable ℂ (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - s)) :=
      (differentiable_const 1).sub diff_cpow_two_one_sub
    exact hdiff.differentiableOn
  have h2 : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    differentiableOn_riemannZeta
  exact (h1.mul h2).analyticOnNhd isOpen_compl_singleton

private lemma LFunction_eq_zeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction chapter7EtaChar s
      = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hpre : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h0mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hev : (ZMod.LFunction chapter7EtaChar)
      =ᶠ[𝓝 (2 : ℂ)] (fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num
    have hnhds : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := hopen.mem_nhds hmem
    filter_upwards [hnhds] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    exact LFunction_eq_zeta_of_one_lt_re hz'
  have heq := analyticOnNhd_LFunction_compl_one.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_zetaFactor_compl_one hpre h0mem hev
  exact heq hs

private lemma hasDerivAt_etaFactor_one :
    HasDerivAt (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - s)) (Complex.log 2) 1 := by
  have h1s : HasDerivAt (fun s : ℂ => 1 - s) (-1) 1 :=
    HasDerivAt.const_sub 1 (hasDerivAt_id 1)
  have h2 : HasDerivAt (fun s : ℂ => (2 : ℂ) ^ (1 - s))
      ((2 : ℂ) ^ ((1 : ℂ) - 1) * Complex.log 2 * (-1)) 1 :=
    h1s.const_cpow (Or.inl two_ne_zero)
  have hpow : (2 : ℂ) ^ ((1 : ℂ) - 1) = 1 := by simp
  have hf : HasDerivAt (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - s))
      (-((2 : ℂ) ^ ((1 : ℂ) - 1) * Complex.log 2 * (-1))) 1 :=
    HasDerivAt.const_sub 1 h2
  rw [hpow] at hf
  have heq : (-((1 : ℂ) * Complex.log 2 * (-1)) : ℂ) = Complex.log 2 := by ring
  rw [heq] at hf
  exact hf

private lemma tendsto_etaFactor_slope :
    Tendsto (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) / (s - 1))
      (𝓝[≠] 1) (𝓝 (Complex.log 2)) := by
  have hf1 : ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - 1)) = 0 := by simp
  have heq : (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) / (s - 1))
      = slope (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - s)) 1 := by
    ext s
    rw [slope_def_field]
    simp only [hf1, sub_zero]
  rw [heq]
  exact hasDerivAt_etaFactor_one.tendsto_slope

private lemma LFunction_one_eq_log :
    ZMod.LFunction chapter7EtaChar 1 = ((Real.log 2 : ℝ) : ℂ) := by
  have h1 := tendsto_etaFactor_slope
  have h2 := riemannZeta_residue_one
  have hprod : Tendsto
      (fun s : ℂ => (((1 : ℂ) - (2 : ℂ) ^ (1 - s)) / (s - 1))
        * ((s - 1) * riemannZeta s))
      (𝓝[≠] 1) (𝓝 (Complex.log 2 * 1)) := h1.mul h2
  rw [mul_one] at hprod
  have heq : (ZMod.LFunction chapter7EtaChar)
      =ᶠ[𝓝[≠] (1 : ℂ)]
        (fun s : ℂ => (((1 : ℂ) - (2 : ℂ) ^ (1 - s)) / (s - 1))
          * ((s - 1) * riemannZeta s)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s ≠ 1 := hs
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hfac : ZMod.LFunction chapter7EtaChar s
        = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s :=
      LFunction_eq_zeta_of_ne_one hs1
    rw [hfac]
    field_simp
  have hLim : Tendsto (ZMod.LFunction chapter7EtaChar) (𝓝[≠] 1)
      (𝓝 (Complex.log 2)) :=
    hprod.congr' heq.symm
  have hcont : Continuous (ZMod.LFunction chapter7EtaChar) :=
    diff_etaLFunction.continuous
  have hTend : Tendsto (ZMod.LFunction chapter7EtaChar) (𝓝[≠] 1)
      (𝓝 (ZMod.LFunction chapter7EtaChar 1)) :=
    (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hEq : ZMod.LFunction chapter7EtaChar 1 = Complex.log 2 :=
    tendsto_nhds_unique hTend hLim
  have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    have h2eq : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
    have h := Complex.ofReal_log (show (0 : ℝ) ≤ 2 by norm_num)
    rw [h2eq] at h
    exact h.symm
  rw [hEq, hlog]

private lemma LFunction_eq_eta (s : ℂ) :
    ZMod.LFunction chapter7EtaChar s = chapter7Eta s := by
  by_cases hs : s = 1
  · subst hs
    rw [LFunction_one_eq_log]
    unfold chapter7Eta
    simp
  · rw [LFunction_eq_zeta_of_ne_one hs]
    unfold chapter7Eta
    simp [hs]

private lemma pairTsum_eq_eta_of_pos_re {s : ℂ} (hs : 0 < s.re) :
    chapter7EtaPairTsum s = chapter7Eta s := by
  have h1 := pairTsum_eq_LFunction_re_pos hs
  have h2 := LFunction_eq_eta s
  rw [h1, h2]

private lemma summable_pair_of_pos_re {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => chapter7EtaPair n s) := by
  have hsum := summable_pair_bound s.re ‖s‖ hs
  exact Summable.of_norm_bounded hsum
    (fun n => etaPair_norm_le n s s.re ‖s‖ hs le_rfl le_rfl)

private lemma partialSum_even_eq (s : ℂ) (n : ℕ) :
    chapter7EtaPartialSum s (2 * n)
      = ∑ k ∈ Finset.range n, chapter7EtaPair k s := by
  induction n with
  | zero => simp [chapter7EtaPartialSum]
  | succ n ih =>
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    have hpair : chapter7EtaPair n s
        = chapter7EtaTerm s (2 * n) + chapter7EtaTerm s (2 * n + 1) := rfl
    unfold chapter7EtaPartialSum at ih ⊢
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, hpair]
    ring

private lemma etaTerm_norm_eq (s : ℂ) (j : ℕ) :
    ‖chapter7EtaTerm s j‖ = ((((j + 1 : ℕ)) : ℝ)) ^ (-s.re) := by
  rw [etaTerm_eq_mul_neg_cpow, norm_mul]
  have h1 : ‖(-1 : ℂ) ^ j‖ = 1 := by simp
  rw [h1, one_mul]
  have hpos : 0 < j + 1 := Nat.succ_pos j
  have hnorm := Complex.norm_natCast_cpow_of_pos hpos (-s)
  rw [hnorm]
  have hre : (-s).re = -s.re := by simp
  rw [hre]

private lemma tendsto_etaTerm_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun j : ℕ => chapter7EtaTerm s j) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have heq : (fun j : ℕ => ‖chapter7EtaTerm s j‖)
      = (fun j : ℕ => ((((j + 1 : ℕ)) : ℝ)) ^ (-s.re)) := by
    ext j
    exact etaTerm_norm_eq s j
  rw [heq]
  have htop : Tendsto (fun j : ℕ => ((((j + 1 : ℕ)) : ℝ))) atTop atTop := by
    have hbase : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hle : ∀ j : ℕ, (j : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ)) := by
      intro j
      have hcast : ((((j + 1 : ℕ)) : ℝ)) = (j : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith
    exact tendsto_atTop_mono hle hbase
  have hlim : Tendsto (fun x : ℝ => x ^ (-s.re)) atTop (𝓝 0) := by
    have hs' : 0 < s.re := hs
    have h := tendsto_rpow_neg_atTop hs'
    have heq2 : (-s.re) = -(s.re) := by ring
    rw [heq2]
    exact h
  exact hlim.comp htop

private lemma tendsto_partialSum_even {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => chapter7EtaPartialSum s (2 * n)) atTop
      (𝓝 (chapter7Eta s)) := by
  have hsum := summable_pair_of_pos_re hs
  have htend := hsum.hasSum.tendsto_sum_nat
  have heta' : (∑' n : ℕ, chapter7EtaPair n s) = chapter7Eta s :=
    pairTsum_eq_eta_of_pos_re hs
  rw [heta'] at htend
  have heq : (fun n : ℕ => chapter7EtaPartialSum s (2 * n))
      = (fun n : ℕ => ∑ k ∈ Finset.range n, chapter7EtaPair k s) := by
    ext n
    exact partialSum_even_eq s n
  rw [heq]
  exact htend

private lemma partialSum_odd_eq (s : ℂ) (n : ℕ) :
    chapter7EtaPartialSum s (2 * n + 1)
      = chapter7EtaPartialSum s (2 * n) + chapter7EtaTerm s (2 * n) := by
  unfold chapter7EtaPartialSum
  rw [Finset.sum_range_succ]

private lemma tendsto_partialSum_odd {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => chapter7EtaPartialSum s (2 * n + 1)) atTop
      (𝓝 (chapter7Eta s)) := by
  have heven := tendsto_partialSum_even hs
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hterm : Tendsto (fun n : ℕ => chapter7EtaTerm s (2 * n)) atTop (𝓝 0) :=
    (tendsto_etaTerm_zero hs).comp h2n
  have hadd := heven.add hterm
  rw [add_zero] at hadd
  have heq : (fun n : ℕ => chapter7EtaPartialSum s (2 * n + 1))
      = (fun n : ℕ => chapter7EtaPartialSum s (2 * n)
        + chapter7EtaTerm s (2 * n)) := by
    ext n
    exact partialSum_odd_eq s n
  rw [heq]
  exact hadd

private lemma eta_tendsto_of_pos_re {s : ℂ} (hs : 0 < s.re) :
    Tendsto (chapter7EtaPartialSum s) atTop (𝓝 (chapter7Eta s)) := by
  have heven := tendsto_partialSum_even hs
  have hodd := tendsto_partialSum_odd hs
  rw [tendsto_atTop_nhds]
  intro U hmem hopen
  obtain ⟨N1, hN1⟩ := (tendsto_atTop_nhds.mp heven) U hmem hopen
  obtain ⟨N2, hN2⟩ := (tendsto_atTop_nhds.mp hodd) U hmem hopen
  refine ⟨max (2 * N1) (2 * N2 + 1), fun N' hN' => ?_⟩
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' N'
  · have hk_ge : N1 ≤ k := by
      have hle : 2 * N1 ≤ N' := le_trans (le_max_left _ _) hN'
      omega
    rw [hk]
    exact hN1 k hk_ge
  · have hk_ge : N2 ≤ k := by
      have hle : 2 * N2 + 1 ≤ N' := le_trans (le_max_right _ _) hN'
      omega
    rw [hk]
    exact hN2 k hk_ge

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7.

Proves `Wanted` entry `ramanujan_part1_ch7_entry2_faulhaber`.
-/
theorem ramanujan_part1_ch7_entry2_faulhaber :
    (∀ s : ℂ, 0 < s.re →
      Tendsto (chapter7EtaPartialSum s) atTop (𝓝 (chapter7Eta s))) ∧
      MeromorphicOn (fun r : ℂ => chapter7Eta (-r)) Set.univ ∧
      MeromorphicOn chapter7Entry2Value Set.univ ∧
      (fun r : ℂ => chapter7Eta (-r)) =ᶠ[codiscrete ℂ] chapter7Entry2Value := by
  refine ⟨?_, meromorphic_eta_neg, meromorphicOn_univ.mpr meromorphic_entry2Value,
    eta_eq_entry2_codiscrete⟩
  intro s hs
  exact eta_tendsto_of_pos_re hs

end
end Entry2Faulhaber
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
