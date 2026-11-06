/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry2Corollary2HarmonicSeries

-- Retained only because the frozen target
-- `ramanujan_part1_ch3_entry2_corollary2_harmonic_series` is stated with it.
-- Every proof below is carried out with Mathlib's `_root_.harmonic` instead.
def harmonic (n : ℕ) : ℚ :=
  (Finset.range n).sum fun k => (1 : ℚ) / ((k + 1 : ℕ) : ℚ)

/-- **Agreement of two definitions of the harmonic numbers.** For every natural number $n$, the
rational number $\sum_{k=0}^{n-1} \frac{1}{k+1}$ equals Mathlib's harmonic number
$H_n = \sum_{k=0}^{n-1} (k+1)^{-1}$. -/
theorem harmonic_eq_mathlib_harmonic (n : ℕ) :
    harmonic n = _root_.harmonic n := by
  unfold harmonic _root_.harmonic
  apply Finset.sum_congr rfl
  intro k _
  rw [one_div]

/-- Aux facts about Mathlib's `_root_.harmonic`, proved from Mathlib's
`harmonic_succ` / `harmonic_zero`, so the whole proof uses the standard API. -/
private lemma harmonic_succ_aux (n : ℕ) :
    _root_.harmonic (n + 1) = _root_.harmonic n + 1 / ((n + 1 : ℕ) : ℚ) := by
  rw [_root_.harmonic_succ, one_div]

private lemma harmonic_nonneg_aux (n : ℕ) : 0 ≤ _root_.harmonic n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [_root_.harmonic_succ]
    exact add_nonneg ih (by positivity)

private lemma harmonic_le_aux (n : ℕ) : _root_.harmonic n ≤ (n : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ_aux]
    have h1 : (1 : ℚ) / ((n + 1 : ℕ) : ℚ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have h : (1 : ℕ) ≤ n + 1 := Nat.le_add_left 1 n
      exact_mod_cast h
    have h2 : ((n : ℕ) : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
    linarith

private lemma hnormH_aux (j : ℕ) :
    ‖(((_root_.harmonic (j + 1) : ℚ)) : ℂ)‖ ≤ ((j + 1 : ℕ) : ℝ) := by
  rw [Complex.norm_ratCast]
  have hnn : (0 : ℝ) ≤ ((_root_.harmonic (j + 1) : ℚ) : ℝ) := by
    have h0 : (0 : ℚ) ≤ _root_.harmonic (j + 1) := harmonic_nonneg_aux _
    exact_mod_cast h0
  rw [abs_of_nonneg hnn]
  have hle : ((_root_.harmonic (j + 1) : ℚ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    have h1 : _root_.harmonic (j + 1) ≤ (((j + 1 : ℕ)) : ℚ) := harmonic_le_aux _
    exact_mod_cast h1
  linarith

private lemma summable_harm_aux (x : ℂ) : Summable (fun j : ℕ =>
    (_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ)) := by
  have hbase : Summable (fun j : ℕ => (‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ))) := by
    have h := Real.summable_pow_div_factorial ‖x‖
    have h2 : (fun j : ℕ => (‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ)))
        = (fun j : ℕ => ‖x‖ * (‖x‖ ^ j / (Nat.factorial j : ℝ))) := by
      funext j
      rw [pow_succ']
      ring
    rw [h2]
    exact h.mul_left _
  refine Summable.of_norm_bounded hbase fun j => ?_
  have hfact_pos : (0 : ℝ) < (Nat.factorial (j + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 1)
  have hnorm : ‖(_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ)‖
      = ‖(((_root_.harmonic (j + 1) : ℚ)) : ℂ)‖ * ‖x‖ ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
  rw [hnorm]
  have hfac_eq : ((Nat.factorial (j + 1) : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) * (Nat.factorial j : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  calc ‖(((_root_.harmonic (j + 1) : ℚ)) : ℂ)‖ * ‖x‖ ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)
      ≤ ((j + 1 : ℕ) : ℝ) * ‖x‖ ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hfact_pos)
        exact mul_le_mul_of_nonneg_right (hnormH_aux j) (pow_nonneg (norm_nonneg _) _)
    _ = ‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ) := by
        rw [hfac_eq]
        field_simp

private lemma summable_alt_aux (x : ℂ) :
    Summable (fun j : ℕ =>
        ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)))) := by
  have hbase : Summable (fun j : ℕ => (‖x‖ ^ (j + 1) / (Nat.factorial (j + 1) : ℝ))) := by
    have h := Real.summable_pow_div_factorial ‖x‖
    have h2 := (summable_nat_add_iff (1 : ℕ)).mpr h
    simpa [add_comm] using h2
  refine Summable.of_norm_bounded hbase fun j => ?_
  have hfact_pos : (0 : ℝ) < (Nat.factorial (j + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 1)
  have e1 : ‖(-1 : ℂ) ^ j‖ = 1 := by simp
  have e2 : ‖x ^ (j + 1)‖ = ‖x‖ ^ (j + 1) := norm_pow _ _
  have e3 : ‖((Nat.factorial (j + 1) : ℂ))‖ = (Nat.factorial (j + 1) : ℝ) :=
    Complex.norm_natCast _
  have e4 : ‖(((j + 1 : ℕ)) : ℂ)‖ = ((j + 1 : ℕ) : ℝ) := Complex.norm_natCast _
  have hnorm : ‖(-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ))‖
      = ‖x‖ ^ (j + 1) / ((Nat.factorial (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
    rw [norm_div, norm_mul, e1, e2, norm_mul, e3, e4, one_mul]
  rw [hnorm]
  apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _) hfact_pos ?_
  have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    have h : (1 : ℕ) ≤ j + 1 := Nat.le_add_left 1 j
    exact_mod_cast h
  calc (Nat.factorial (j + 1) : ℝ) = (Nat.factorial (j + 1) : ℝ) * 1 := by ring
    _ ≤ (Nat.factorial (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left h1 (le_of_lt hfact_pos)

private lemma exp_hasSum_aux (x : ℂ) :
    HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℂ)) (Complex.exp x) := by
  have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) (𝔸 := ℂ) x
  have h2 : (fun n : ℕ => ((NormedSpace.expSeries ℂ ℂ n) fun _ => x))
      = (fun n : ℕ => x ^ n / (Nat.factorial n : ℂ)) := by
    funext n
    exact NormedSpace.expSeries_apply_eq_div x n
  rw [h2] at h
  rwa [← Complex.exp_eq_exp_ℂ] at h

private noncomputable def cauchyF (x : ℂ) (k : ℕ) : ℂ := x ^ k / (Nat.factorial k : ℂ)

private noncomputable def cauchyG (x : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n - 1) * x ^ n / (((n : ℕ) : ℂ) * (Nat.factorial n : ℂ))

private noncomputable def cauchyH (x : ℂ) (n : ℕ) : ℂ :=
  ((_root_.harmonic n : ℚ) : ℂ) * x ^ n / (Nat.factorial n : ℂ)

private lemma cauchyG_zero_aux (x : ℂ) : cauchyG x 0 = 0 := by
  unfold cauchyG
  simp

private lemma cauchyG_succ_aux (x : ℂ) (j : ℕ) :
    cauchyG x (j + 1)
      = (-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)) := by
  unfold cauchyG
  have h1 : (j + 1 - 1) = j := Nat.add_sub_cancel j 1
  rw [h1, mul_comm ((((j + 1 : ℕ))) : ℂ) _]

private lemma cauchyF_norm_aux (x : ℂ) : Summable (fun k => ‖cauchyF x k‖) := by
  have h := Real.summable_pow_div_factorial ‖x‖
  have heq : (fun k => ‖cauchyF x k‖) = (fun k : ℕ => ‖x‖ ^ k / (Nat.factorial k : ℝ)) := by
    funext k
    unfold cauchyF
    rw [norm_div, norm_pow, Complex.norm_natCast]
  rw [heq]
  exact h

private lemma cauchyG_norm_aux (x : ℂ) : Summable (fun n => ‖cauchyG x n‖) := by
  have hbase := Real.summable_pow_div_factorial ‖x‖
  have heq : (fun n => ‖cauchyG x n‖)
      = (fun n : ℕ => ‖x‖ ^ n / (((n : ℕ) : ℝ) * (Nat.factorial n : ℝ))) := by
    funext n
    unfold cauchyG
    have e1 : ‖(-1 : ℂ) ^ (n - 1)‖ = 1 := by simp
    have e2 : ‖x ^ n‖ = ‖x‖ ^ n := norm_pow _ _
    have e3 : ‖(((n : ℕ)) : ℂ)‖ = ((n : ℕ) : ℝ) := Complex.norm_natCast _
    have e4 : ‖((Nat.factorial n : ℂ))‖ = (Nat.factorial n : ℝ) := Complex.norm_natCast _
    rw [norm_div, norm_mul, e1, e2, norm_mul, e3, e4, one_mul]
  rw [heq]
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hbase
  intro n
  by_cases hn : n = 0
  · subst hn
    simp
  · have hnpos : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by
      have h : (1 : ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast h
    have hfact_pos : (0 : ℝ) < (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      (by exact_mod_cast Nat.factorial_pos n) ?_
    calc (Nat.factorial n : ℝ) = (Nat.factorial n : ℝ) * 1 := by ring
      _ ≤ (Nat.factorial n : ℝ) * ((n : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_left hnpos (le_of_lt hfact_pos)
      _ = ((n : ℕ) : ℝ) * (Nat.factorial n : ℝ) := by ring

private lemma choose_ratio_aux (N k : ℕ) :
    ((Nat.choose N k : ℕ) : ℂ) / ((k + 1 : ℕ) : ℂ) =
    ((Nat.choose (N + 1) (k + 1) : ℕ) : ℂ) / ((N + 1 : ℕ) : ℂ) := by
  have hN1 : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hnat : (N + 1) * Nat.choose N k = Nat.choose (N + 1) (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq N k
  have hcast : ((N + 1 : ℕ) : ℂ) * ((Nat.choose N k : ℕ) : ℂ)
      = ((Nat.choose (N + 1) (k + 1) : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ) := by
    exact_mod_cast hnat
  field_simp
  linear_combination hcast

private lemma alt_choose_sum_aux (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ k * ((Nat.choose (N + 1) (k + 1) : ℕ) : ℂ) = 1 := by
  have h := add_pow (-1 : ℂ) (1 : ℂ) (N + 1)
  have hsim : ∑ m ∈ Finset.range (N + 2), (-1 : ℂ) ^ m * ((Nat.choose (N + 1) m : ℕ) : ℂ)
      = ((-1 : ℂ) + 1) ^ (N + 1) := by
    have h2 : ∑ m ∈ Finset.range (N + 1 + 1),
          (-1 : ℂ) ^ m * (1 : ℂ) ^ (N + 1 - m) * ((Nat.choose (N + 1) m : ℕ) : ℂ)
        = ∑ m ∈ Finset.range (N + 2), (-1 : ℂ) ^ m * ((Nat.choose (N + 1) m : ℕ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro m _
      simp
    rw [← h2]
    rw [← h]
  have hzero : ((-1 : ℂ) + 1) ^ (N + 1) = 0 := by
    have h00 : (-1 : ℂ) + 1 = 0 := by ring
    rw [h00]
    exact zero_pow (Nat.succ_ne_zero N)
  rw [hzero] at hsim
  have hsplit := Finset.sum_range_succ'
    (fun m => (-1 : ℂ) ^ m * ((Nat.choose (N + 1) m : ℕ) : ℂ)) (N + 1)
  rw [hsim] at hsplit
  have h0 : (-1 : ℂ) ^ 0 * ((Nat.choose (N + 1) 0 : ℕ) : ℂ) = 1 := by simp
  rw [h0] at hsplit
  have hneg : ∑ k ∈ Finset.range (N + 1),
      (-1 : ℂ) ^ (k + 1) * ((Nat.choose (N + 1) (k + 1) : ℕ) : ℂ) = -1 := by
    have hsym : (∑ k ∈ Finset.range (N + 1),
      (-1 : ℂ) ^ (k + 1) * ((Nat.choose (N + 1) (k + 1) : ℕ) : ℂ)) + 1 = 0 := hsplit.symm
    exact eq_neg_of_add_eq_zero_left hsym
  have hrel : ∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ k * ((Nat.choose (N + 1) (k + 1) : ℕ) : ℂ)
      = - (∑ k ∈ Finset.range (N + 1),
        (-1 : ℂ) ^ (k + 1) * ((Nat.choose (N + 1) (k + 1) : ℕ) : ℂ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  rw [hrel, hneg, neg_neg]

private lemma alt_T_aux (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ k * (((Nat.choose N k : ℕ) : ℂ) / (((k + 1 : ℕ)) : ℂ))
      = 1 / (((N + 1 : ℕ)) : ℂ) := by
  have hterm : ∀ k ∈ Finset.range (N + 1),
      (-1 : ℂ) ^ k * (((Nat.choose N k : ℕ) : ℂ) / (((k + 1 : ℕ)) : ℂ))
      = (1 / (((N + 1 : ℕ)) : ℂ)) * ((-1 : ℂ) ^ k * ((Nat.choose (N + 1) (k + 1) : ℕ) : ℂ)) := by
    intro k _
    rw [choose_ratio_aux N k]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, alt_choose_sum_aux, mul_one]

private lemma harm_eq_aux (N : ℕ) : (((_root_.harmonic N : ℚ)) : ℂ)
    = ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k *
        (((Nat.choose N (k + 1) : ℕ) : ℂ) / (((k + 1 : ℕ)) : ℂ)) := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    have hHs : (((_root_.harmonic (N + 1) : ℚ)) : ℂ)
        = (((_root_.harmonic N : ℚ)) : ℂ) + 1 / (((N + 1 : ℕ)) : ℂ) := by
      have h := harmonic_succ_aux N
      have hcast : (((_root_.harmonic (N + 1) : ℚ)) : ℂ)
          = (((_root_.harmonic N : ℚ)) : ℂ) + ((1 / ((N + 1 : ℕ) : ℚ) : ℚ) : ℂ) := by
        exact_mod_cast h
      rw [hcast]
      congr 1
      push_cast
      ring
    rw [hHs, ih]
    have hsplit : ∀ k ∈ Finset.range (N + 1),
        (-1 : ℂ) ^ k * (((Nat.choose (N + 1) (k + 1) : ℕ) : ℂ) / (((k + 1 : ℕ)) : ℂ))
        = (-1 : ℂ) ^ k * (((Nat.choose N k : ℕ) : ℂ) / (((k + 1 : ℕ)) : ℂ))
          + (-1 : ℂ) ^ k * (((Nat.choose N (k + 1) : ℕ) : ℂ) / (((k + 1 : ℕ)) : ℂ)) := by
      intro k _
      have hcc : ((Nat.choose (N + 1) (k + 1) : ℕ) : ℂ)
          = ((Nat.choose N k : ℕ) : ℂ) + ((Nat.choose N (k + 1) : ℕ) : ℂ) := by
        have hnat : Nat.choose (N + 1) (k + 1) = Nat.choose N k + Nat.choose N (k + 1) :=
          Nat.choose_succ_succ N k
        exact_mod_cast hnat
      rw [hcc, add_div, mul_add]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have hsecond : ∑ k ∈ Finset.range (N + 1),
          (-1 : ℂ) ^ k * (((Nat.choose N (k + 1) : ℕ) : ℂ) / (((k + 1 : ℕ)) : ℂ))
        = ∑ k ∈ Finset.range N,
          (-1 : ℂ) ^ k * (((Nat.choose N (k + 1) : ℕ) : ℂ) / (((k + 1 : ℕ)) : ℂ)) := by
      rw [Finset.sum_range_succ]
      have hlast : (-1 : ℂ) ^ N * (((Nat.choose N (N + 1) : ℕ) : ℂ) / (((N + 1 : ℕ)) : ℂ)) = 0 := by
        have hch : Nat.choose N (N + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self N)
        rw [hch]
        simp
      rw [hlast, add_zero]
    rw [hsecond, alt_T_aux]
    ring

private lemma key_eq_aux (x : ℂ) (N k : ℕ) (hk : k < N) :
    x ^ k * x ^ (N - k) / ((Nat.factorial k : ℂ) * (Nat.factorial (N - k) : ℂ))
      = x ^ N * ((Nat.choose N k : ℕ) : ℂ) / (Nat.factorial N : ℂ) := by
  have hkN : k ≤ N := Nat.le_of_lt hk
  have hC : ((Nat.choose N k : ℕ) : ℂ) * (Nat.factorial k : ℂ) * (Nat.factorial (N - k) : ℂ)
      = (Nat.factorial N : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkN
  have hpow : x ^ k * x ^ (N - k) = x ^ N := by
    rw [← pow_add, Nat.add_sub_cancel' hkN]
  have hfactN : ((Nat.factorial N : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  have hden : ((Nat.factorial k : ℂ) * (Nat.factorial (N - k) : ℂ)) ≠ 0 := by
    apply mul_ne_zero <;> exact_mod_cast Nat.factorial_ne_zero _
  rw [div_eq_div_iff hden hfactN]
  linear_combination (Nat.factorial N : ℂ) * hpow - x ^ N * hC

private lemma term_eq_aux (x : ℂ) (N k : ℕ) (hk : k < N) :
    cauchyF x k * cauchyG x (N - k) = (x ^ N / (Nat.factorial N : ℂ)) *
      ((-1 : ℂ) ^ (N - 1 - k) * (((Nat.choose N k : ℕ) : ℂ) / (((N - k : ℕ)) : ℂ))) := by
  have hexp : N - k - 1 = N - 1 - k := by omega
  have hfactor_lhs : cauchyF x k * cauchyG x (N - k)
      = (((-1 : ℂ) ^ (N - 1 - k)) / (((N - k : ℕ)) : ℂ)) *
        (x ^ k * x ^ (N - k) / ((Nat.factorial k : ℂ) * (Nat.factorial (N - k) : ℂ))) := by
    unfold cauchyF cauchyG
    rw [hexp]
    ring
  have hfactor_rhs : (x ^ N / (Nat.factorial N : ℂ)) *
      ((-1 : ℂ) ^ (N - 1 - k) * (((Nat.choose N k : ℕ) : ℂ) / (((N - k : ℕ)) : ℂ)))
      = (((-1 : ℂ) ^ (N - 1 - k)) / (((N - k : ℕ)) : ℂ)) *
        (x ^ N * ((Nat.choose N k : ℕ) : ℂ) / (Nat.factorial N : ℂ)) := by
    ring
  rw [hfactor_lhs, hfactor_rhs, key_eq_aux x N k hk]

private lemma bracket_eq_aux (N k : ℕ) (hk : k < N) :
    (-1 : ℂ) ^ (N - 1 - k) * (((Nat.choose N k : ℕ) : ℂ) / (((N - k : ℕ)) : ℂ))
    = (-1 : ℂ) ^ (N - 1 - k)
      * (((Nat.choose N ((N - 1 - k) + 1) : ℕ) : ℂ) / ((((N - 1 - k) + 1 : ℕ)) : ℂ)) := by
  have h1 : N - 1 - k + 1 = N - k := by omega
  have hkN : k ≤ N := Nat.le_of_lt hk
  rw [h1, Nat.choose_symm hkN]

private lemma conv_eq_aux (x : ℂ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), cauchyF x k * cauchyG x (N - k) = cauchyH x N := by
  rw [Finset.sum_range_succ]
  have hlast : cauchyF x N * cauchyG x (N - N) = 0 := by
    rw [Nat.sub_self]
    simp [cauchyG_zero_aux x]
  rw [hlast, add_zero]
  have hterm : ∀ k ∈ Finset.range N,
      cauchyF x k * cauchyG x (N - k)
        = (x ^ N / (Nat.factorial N : ℂ)) *
          ((-1 : ℂ) ^ (N - 1 - k)
            * (((Nat.choose N ((N - 1 - k) + 1) : ℕ) : ℂ) / ((((N - 1 - k) + 1 : ℕ)) : ℂ))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [term_eq_aux x N k hk, bracket_eq_aux N k hk]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hrefl := Finset.sum_range_reflect
    (fun j => (-1 : ℂ) ^ j * (((Nat.choose N (j + 1) : ℕ) : ℂ) / (((j + 1 : ℕ)) : ℂ))) N
  rw [hrefl, ← harm_eq_aux]
  unfold cauchyH
  ring

private theorem corollary2_core_aux (x : ℂ) :
    Summable (fun j : ℕ => (_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) /
      (Nat.factorial (j + 1) : ℂ)) ∧
    Summable (fun j : ℕ =>
        ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)))) ∧
    (∑' j : ℕ, (_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ)) =
      Complex.exp x *
          (∑' j : ℕ,
              ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) *
                  ((j + 1 : ℕ) : ℂ)))) := by
  have hS1 : Summable
      (fun j : ℕ => (_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ)) :=
    summable_harm_aux x
  have hS2 : Summable (fun j : ℕ =>
      ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)))) :=
    summable_alt_aux x
  refine ⟨hS1, hS2, ?_⟩
  have hCauchy := hasSum_sum_range_mul_of_summable_norm
    (cauchyF_norm_aux x) (cauchyG_norm_aux x)
  have hFtsum : (∑' n : ℕ, cauchyF x n) = Complex.exp x := by
    have h : HasSum (fun n : ℕ => cauchyF x n) (Complex.exp x) := by
      change HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℂ)) (Complex.exp x)
      exact exp_hasSum_aux x
    exact HasSum.tsum_eq h
  have hGsumm : Summable (fun n : ℕ => cauchyG x n) :=
    Summable.of_norm (cauchyG_norm_aux x)
  have hGtsum : (∑' n : ℕ, cauchyG x n)
      = (∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1)
        / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)))) := by
    have h0 : cauchyG x 0 = 0 := cauchyG_zero_aux x
    have hshift : (fun j : ℕ => cauchyG x (j + 1))
        = (fun j : ℕ => ((-1 : ℂ) ^ j * x ^ (j + 1)
          / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)))) := by
      funext j
      exact cauchyG_succ_aux x j
    have h := Summable.tsum_eq_zero_add hGsumm
    rw [h0, zero_add, hshift] at h
    exact h
  have hconv : (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), cauchyF x k * cauchyG x (n - k))
      = (fun n : ℕ => cauchyH x n) := by
    funext n
    exact conv_eq_aux x n
  have hH : HasSum (fun n : ℕ => cauchyH x n) (Complex.exp x *
      (∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1)
        / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ))))) := by
    rw [← hconv, ← hFtsum, ← hGtsum]
    exact hCauchy
  have hHsum : Summable (fun n : ℕ => cauchyH x n) := by
    have hshift : Summable (fun j : ℕ => cauchyH x (j + 1)) := by
      change Summable
        (fun j : ℕ => (_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ))
      exact hS1
    exact (summable_nat_add_iff 1).mp hshift
  have hteq : (∑' n : ℕ, cauchyH x n) = Complex.exp x *
      (∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1)
        / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)))) :=
    HasSum.tsum_eq hH
  have hHtransfer : (∑' n : ℕ, cauchyH x n)
      = (∑' j : ℕ, (_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ)) := by
    have h := Summable.tsum_eq_zero_add hHsum
    have h0 : cauchyH x 0 = 0 := by
      change ((_root_.harmonic 0 : ℚ) : ℂ) * x ^ 0 / (Nat.factorial 0 : ℂ) = 0
      have hz : _root_.harmonic 0 = 0 := by simp
      rw [hz]
      simp
    have hfun : (fun b : ℕ => cauchyH x (b + 1))
        = (fun j : ℕ => (_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) /
          (Nat.factorial (j + 1) : ℂ)) :=
      rfl
    rw [h0, zero_add, hfun] at h
    exact h
  rw [← hHtransfer]
  exact hteq

/-- **Ramanujan's series for the harmonic numbers, with Mathlib's harmonic numbers.** Let
$H_k = \sum_{i=0}^{k-1} (i+1)^{-1}$ be Mathlib's $k$-th harmonic number. For every complex number
$x$, the series $\sum_{k \ge 1} \frac{H_k x^k}{k!}$ and
$\sum_{k \ge 1} \frac{(-1)^{k-1} x^k}{k!\, k}$ converge absolutely, and
$\sum_{k=1}^{\infty} \frac{H_k x^k}{k!} = e^x \sum_{k=1}^{\infty} \frac{(-1)^{k-1} x^k}{k!\, k}$. -/
theorem ramanujan_part1_ch3_entry2_corollary2_harmonic_series_mathlib (x : ℂ) :
    Summable (fun j : ℕ => (_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) /
        (Nat.factorial (j + 1) : ℂ)) ∧
    Summable (fun j : ℕ =>
        ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)))) ∧
    (∑' j : ℕ, (_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ)) =
      Complex.exp x *
          (∑' j : ℕ,
              ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) *
                  ((j + 1 : ℕ) : ℂ)))) :=
  corollary2_core_aux x

/-- **Ramanujan's series for the harmonic numbers (Chapter 3, Entry 2, Corollary 2).** Let
$H_k = \sum_{i=1}^{k} \frac{1}{i}$ be the $k$-th harmonic number. For every complex number $x$, the
series $\sum_{k \ge 1} \frac{H_k x^k}{k!}$ and $\sum_{k \ge 1} \frac{(-1)^{k-1} x^k}{k!\, k}$
converge absolutely, and $\sum_{k=1}^{\infty} \frac{H_k x^k}{k!} =
e^x \sum_{k=1}^{\infty} \frac{(-1)^{k-1} x^k}{k!\, k}$.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 2, formula (2.3) and
    Corollary 2, printed pp. 46--47 / PDF pp. 56--57.

Proves `Wanted` entry `ramanujan_part1_ch3_entry2_corollary2_harmonic_series`.
-/
theorem ramanujan_part1_ch3_entry2_corollary2_harmonic_series (x : ℂ) :
    Summable (fun j : ℕ => (harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ)) ∧
    Summable (fun j : ℕ =>
        ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)))) ∧
    (∑' j : ℕ, (harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ)) =
      Complex.exp x *
          (∑' j : ℕ,
              ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) *
                  ((j + 1 : ℕ) : ℂ)))) := by
  have h :=
    ramanujan_part1_ch3_entry2_corollary2_harmonic_series_mathlib x
  simpa [harmonic_eq_mathlib_harmonic] using h

end Entry2Corollary2HarmonicSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
