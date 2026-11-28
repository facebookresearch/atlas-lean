/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.WienerIkehara
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Normed.Group.Tannery


/-! # Constancy of an infinite cyclotomic product

Constancy of the cyclotomic product on the open unit disk, using ordered Möbius partial sums
and the logarithmic power series.

Source: Hartosh Singh Bal, *Constancy of an Infinite Cyclotomic Product via Ramanujan Sums*,
INTEGERS 25 (2025), Article A96, Theorem 1 (`integers-2025-A96-thm-1`).
-/

open Filter Topology

namespace MetaMathlibExt

/-- At modulus `1`, Mathlib's regularization `(s - 1) * L(1, s)` of the trivial-character
`L`-function (`DirichletCharacter.LFunctionTrivChar₁`) is `(s - 1) * ζ(s)`, with value `1` at
`s = 1`. -/
private lemma LFunctionTrivChar₁_one_eq :
    DirichletCharacter.LFunctionTrivChar₁ 1 =
      Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1 := by
  simp [DirichletCharacter.LFunctionTrivChar₁, DirichletCharacter.LFunctionTrivChar]
private noncomputable def regularPartZeta : ℂ → ℂ :=
  Function.update (fun s ↦ (DirichletCharacter.LFunctionTrivChar₁ 1 s - 1) / (s - 1)) 1
    (deriv (DirichletCharacter.LFunctionTrivChar₁ 1) 1)
private lemma regularPartZeta_continuousOn :
    ContinuousOn regularPartZeta {s : ℂ | 1 ≤ s.re} := by
  intro s _
  apply ContinuousAt.continuousWithinAt
  by_cases hs : s = 1
  · subst s
    simpa [regularPartZeta, LFunctionTrivChar₁_one_eq] using
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1 1).hasDerivAt.continuousAt_div
  · apply ContinuousAt.congr_of_eventuallyEq
      (((DirichletCharacter.differentiable_LFunctionTrivChar₁ 1 s).continuousAt.sub
        (continuousAt_const (y := (1 : ℂ)))).div
        (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hs))
    filter_upwards [eventually_ne_nhds hs] with u hu
    simp [regularPartZeta, Function.update_of_ne hu]
private noncomputable def moebiusExtension (s : ℂ) : ℂ :=
  regularPartZeta s + (s - 1) / DirichletCharacter.LFunctionTrivChar₁ 1 s
private lemma moebiusExtension_continuousOn :
    ContinuousOn moebiusExtension {s : ℂ | 1 ≤ s.re} := by
  exact regularPartZeta_continuousOn.add
    ((continuousOn_id.sub continuousOn_const).div
      (fun s _ ↦
        (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1 s).continuousAt.continuousWithinAt)
      (fun s hs ↦ by
        rcases eq_or_ne s 1 with rfl | h
        · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
        · rw [LFunctionTrivChar₁_one_eq, Function.update_of_ne h]
          exact mul_ne_zero (sub_ne_zero.mpr h) (riemannZeta_ne_zero_of_one_le_re hs)))
private lemma moebiusExtension_eq {s : ℂ} (hs : 1 < s.re) :
    moebiusExtension s =
      LSeries (fun n ↦ ((1 + ArithmeticFunction.moebius n : ℝ) : ℂ)) s - 1 / (s - 1) := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hm := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hm
  have hμ : LSeries (fun n ↦ (ArithmeticFunction.moebius n : ℂ)) s = (riemannZeta s)⁻¹ := by
    apply (mul_left_cancel₀ hz)
    simpa [hz] using hm
  have hsum : (fun n ↦ ((1 + ArithmeticFunction.moebius n : ℝ) : ℂ)) =
      (1 : ℕ → ℂ) + (fun n ↦ (ArithmeticFunction.moebius n : ℂ)) := by
    ext n
    simp
  rw [hsum, LSeries_add (LSeriesSummable_one_iff.mpr hs)
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs),
    LSeries_one_eq_riemannZeta hs, hμ]
  simp only [moebiusExtension, regularPartZeta, LFunctionTrivChar₁_one_eq,
    DirichletCharacter.LFunction_modOne_eq, Function.update_of_ne hs1]
  field_simp [hz, sub_ne_zero.mpr hs1]
  ring
private lemma tendsto_moebius_average :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N,
      (ArithmeticFunction.moebius n : ℝ)) / N) atTop (𝓝 0) := by
  have hbound : ∀ N : ℕ, ∑ n ∈ Finset.range N,
      (1 + ArithmeticFunction.moebius n : ℝ) ≤ 2 * N := by
    intro N
    calc
      _ ≤ ∑ _n ∈ Finset.range N, (2 : ℝ) := Finset.sum_le_sum fun n _ ↦ by
        have h : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
        linarith [(le_abs_self (ArithmeticFunction.moebius n : ℝ))]
      _ = _ := by simp; ring
  have hpos : 0 ≤ (fun n ↦ (1 + ArithmeticFunction.moebius n : ℝ)) := by
    intro n
    change 0 ≤ 1 + (ArithmeticFunction.moebius n : ℝ)
    have h : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    linarith [(neg_abs_le (ArithmeticFunction.moebius n : ℝ))]
  have ht := WienerIkehara.tendsto_sum_range_div (A := 1)
    hbound moebiusExtension_continuousOn (fun s hs ↦ moebiusExtension_eq hs) hpos
  have hconst : Tendsto (fun N : ℕ ↦ (N : ℝ) / N) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp [(Nat.cast_pos.mpr hN).ne']
  simpa [Finset.sum_add_distrib, add_div, sub_eq_add_neg, add_assoc] using ht.sub hconst
private lemma fract_div_eq (N n : ℕ) :
    Int.fract ((N : ℝ) / n) = (N : ℝ) / n - (N / n : ℕ) := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [eq_sub_iff_add_eq, div_add' _ _ _ hn', div_left_inj₀ hn']
    exact_mod_cast (show N % n + N / n * n = N by rw [Nat.mul_comm]; exact Nat.mod_add_div N n)
private lemma fract_div_variation (N m : ℕ) (hm : 0 < m) (hmN : m ≤ N) :
    ∑ i ∈ Finset.Ico m N,
      |Int.fract ((N : ℝ) / ((i + 1 : ℕ) : ℝ)) - Int.fract ((N : ℝ) / ((i : ℕ) : ℝ))| ≤
      2 * (N : ℝ) / m := by
  have hdiff (i : ℕ) (hi : i ∈ Finset.Ico m N) :
      |Int.fract ((N : ℝ) / ((i + 1 : ℕ) : ℝ)) - Int.fract ((N : ℝ) / ((i : ℕ) : ℝ))| ≤
      ((N : ℝ) / i - (N : ℝ) / (i + 1)) +
        ((N / i : ℕ) - (N / (i + 1) : ℕ) : ℝ) := by
    have hi0 : 0 < i := lt_of_lt_of_le hm (Finset.mem_Ico.mp hi).1
    have hx : (N : ℝ) / (i + 1) ≤ (N : ℝ) / i :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg N) (Nat.cast_pos.mpr hi0)
        (by norm_cast; omega)
    have hy : (N / (i + 1) : ℕ) ≤ N / i := Nat.div_le_div_left (by omega) hi0
    have hy' : ((N / (i + 1) : ℕ) : ℝ) ≤ (N / i : ℕ) := Nat.cast_le.mpr hy
    calc
      _ = |((N : ℝ) / (i + 1) - (N : ℝ) / i) -
          (((N / (i + 1) : ℕ) : ℝ) - (N / i : ℕ))| := by
        congr 1
        simp only [fract_div_eq]
        push_cast
        ring
      _ ≤ _ := abs_sub _ _
      _ = _ := by rw [abs_of_nonpos (sub_nonpos.mpr hx),
        abs_of_nonpos (sub_nonpos.mpr hy')]; ring
  calc
    _ ≤ ∑ i ∈ Finset.Ico m N,
        (((N : ℝ) / i - (N : ℝ) / (i + 1)) +
          (((N / i : ℕ) : ℝ) - (N / (i + 1) : ℕ))) :=
      Finset.sum_le_sum hdiff
    _ = (N : ℝ) / m - (N : ℝ) / N + (N / m : ℕ) - (N / N : ℕ) := by
      rw [Finset.sum_add_distrib]
      have h₁ := Finset.sum_Ico_sub (fun i ↦ (N : ℝ) / i) hmN
      have h₂ := Finset.sum_Ico_sub (fun i ↦ ((N / i : ℕ) : ℝ)) hmN
      have hx : (∑ i ∈ Finset.Ico m N, ((N : ℝ) / i - (N : ℝ) / (i + 1))) =
          -∑ i ∈ Finset.Ico m N, ((N : ℝ) / (i + 1) - (N : ℝ) / i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have hy : (∑ i ∈ Finset.Ico m N, (((N / i : ℕ) : ℝ) - (N / (i + 1) : ℕ))) =
          -∑ i ∈ Finset.Ico m N, (((N / (i + 1) : ℕ) : ℝ) - (N / i : ℕ)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      simp only [Nat.cast_add, Nat.cast_one] at h₁
      rw [hx, hy, h₁, h₂]
      ring
    _ ≤ _ := by
      have h := Int.fract_nonneg ((N : ℝ) / ((m : ℕ) : ℝ))
      rw [fract_div_eq] at h
      have hN : 0 ≤ (N : ℝ) / N := div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg N)
      have hNN : (0 : ℝ) ≤ (N / N : ℕ) := Nat.cast_nonneg _
      calc
        _ ≤ 2 * ((N : ℝ) / m) := by linarith
        _ = _ := by ring
private lemma abs_sub_sub_le (x y u : ℝ) : |x - y - u| ≤ |x| + |y| + |u| := by
  calc
    _ ≤ |x - y| + |u| := abs_sub (x - y) u
    _ ≤ _ := add_le_add (abs_sub x y) (le_refl |u|)
private lemma weighted_tail_bound (a : ℕ → ℝ) (N m : ℕ) (hm : 0 < m)
    (hmN : m ≤ N) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ k, m ≤ k → k ≤ N + 1 → |∑ i ∈ Finset.range k, a i| ≤ δ * (N + 1)) :
    |∑ i ∈ Finset.Ico m (N + 1), Int.fract ((N : ℝ) / ((i : ℕ) : ℝ)) * a i| ≤
      δ * (N + 1) * (2 + 2 * (N : ℝ) / m) := by
  have hw (i : ℕ) : |Int.fract ((N : ℝ) / ((i : ℕ) : ℝ))| ≤ 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  have hparts := Finset.sum_Ico_by_parts (R := ℝ) (M := ℝ)
    (fun i : ℕ ↦ Int.fract ((N : ℝ) / ((i : ℕ) : ℝ))) a
    (by omega : m < N + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hparts
  rw [hparts]
  calc
    _ ≤ |Int.fract ((N : ℝ) / ((N : ℕ) : ℝ)) * ∑ i ∈ Finset.range (N + 1), a i| +
        |Int.fract ((N : ℝ) / ((m : ℕ) : ℝ)) * ∑ i ∈ Finset.range m, a i| +
        |∑ i ∈ Finset.Ico m N,
          (Int.fract ((N : ℝ) / ((i + 1 : ℕ) : ℝ)) - Int.fract ((N : ℝ) / ((i : ℕ) : ℝ))) *
          ∑ j ∈ Finset.range (i + 1), a j| := by
      exact abs_sub_sub_le _ _ _
    _ ≤ δ * (N + 1) + δ * (N + 1) +
        (∑ i ∈ Finset.Ico m N,
          |Int.fract ((N : ℝ) / ((i + 1 : ℕ) : ℝ)) - Int.fract ((N : ℝ) / ((i : ℕ) : ℝ))|) *
          (δ * (N + 1)) := by
      apply add_le_add
      · apply add_le_add
        · rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hw N) |>.trans
            (ha (N + 1) (by omega) le_rfl)
        · rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hw m) |>.trans (ha m le_rfl (by omega))
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (ha (i + 1) (by have := Finset.mem_Ico.mp hi; omega)
          (by have := Finset.mem_Ico.mp hi; omega)) (abs_nonneg _)
    _ ≤ δ * (N + 1) + δ * (N + 1) + 2 * (N : ℝ) / m * (δ * (N + 1)) := by
      gcongr
      exact fract_div_variation N m hm hmN
    _ = _ := by ring
private lemma tendsto_fractional_average (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1)
    (hmean : Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, a n) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦
      (∑ n ∈ Finset.range (N + 1), Int.fract ((N : ℝ) / ((n : ℕ) : ℝ)) * a n) / N)
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (max (4 / ε) 2)
  have hK2 : (2 : ℝ) < K := lt_of_le_of_lt (le_max_right _ _) hK
  have hK0 : 0 < K := by exact_mod_cast (by linarith : (0 : ℝ) < K)
  have hK' : (0 : ℝ) < K := Nat.cast_pos.mpr hK0
  have hKε : (1 : ℝ) / K < ε / 4 := by
    have h := lt_of_le_of_lt (le_max_left _ _) hK
    apply (div_lt_iff₀ hK').mpr
    nlinarith [(div_lt_iff₀ hε).mp h]
  let δ : ℝ := ε / (16 * (K + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.mp hmean δ hδ
  obtain ⟨C, hC⟩ := exists_nat_gt (4 / ε)
  refine ⟨max (K * (B + 1)) (C + 1), ?_⟩
  intro N hN
  have hNB : K * (B + 1) ≤ N := (le_max_left _ _).trans hN
  have hNC : C + 1 ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := by omega
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN0
  have hKle : K ≤ N := (Nat.le_mul_of_pos_right K (by omega)).trans hNB
  let m : ℕ := N / K + 1
  have hm0 : 0 < m := Nat.zero_lt_succ (N / K)
  have hmB : B ≤ m := by
    have : B + 1 ≤ N / K := (Nat.le_div_iff_mul_le hK0).mpr (by simpa [Nat.mul_comm] using hNB)
    dsimp [m]
    omega
  have hmN : m ≤ N := by
    have hKnat : 2 ≤ K := by exact_mod_cast hK2.le
    have : N / K ≤ N / 2 := Nat.div_le_div_left hKnat (by decide)
    have : N / 2 + 1 ≤ N := by omega
    dsimp [m]
    omega
  have hratio : (N : ℝ) / m < K := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hm0)).mpr
    exact_mod_cast (by simpa [m, Nat.mul_comm] using Nat.lt_mul_div_succ N hK0)
  have hbound : ∀ k, m ≤ k → k ≤ N + 1 →
      |∑ i ∈ Finset.range k, a i| ≤ δ * (N + 1) := by
    intro k hmk hkN
    have hk0 : 0 < k := lt_of_lt_of_le hm0 hmk
    have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk0
    have hb := hB k (hmB.trans hmk)
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hk'] at hb
    exact ((div_lt_iff₀ hk').mp hb).le.trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hkN) hδ.le)
  have hhead : |∑ i ∈ Finset.range m, Int.fract ((N : ℝ) / ((i : ℕ) : ℝ)) * a i| ≤ m := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ by
        by_cases hi : i = 0
        · simp [hi]
        · rw [abs_mul, abs_of_nonneg (Int.fract_nonneg _)]
          exact (mul_le_mul_of_nonneg_left (ha i) (Int.fract_nonneg _)).trans
            (by simpa using (Int.fract_lt_one ((N : ℝ) / ((i : ℕ) : ℝ))).le)
      _ = _ := by simp
  have htail := weighted_tail_bound a N m hm0 hmN δ hδ.le hbound
  have htotal : |∑ i ∈ Finset.range (N + 1), Int.fract ((N : ℝ) / ((i : ℕ) : ℝ)) * a i| ≤
      m + δ * (N + 1) * (2 + 2 * (N : ℝ) / m) := by
    rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_trans hmN (Nat.le_succ N))]
    exact (abs_add_le _ _).trans (add_le_add hhead htail)
  have hmratio : (m : ℝ) / N ≤ 1 / K + 1 / N := by
    have h := Nat.div_mul_le_self N K
    have h' : ((N / K : ℕ) : ℝ) * K ≤ N := by exact_mod_cast h
    dsimp [m]
    push_cast
    field_simp [hN'.ne', hK'.ne']
    nlinarith
  have hNε : (1 : ℝ) / N < ε / 4 := by
    apply (div_lt_iff₀ hN').mpr
    have hCN : (C : ℝ) < N := by exact_mod_cast hNC
    nlinarith [(div_lt_iff₀ hε).mp hC]
  have hNN : ((N : ℝ) + 1) / N ≤ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN0
    rw [div_le_iff₀ hN']
    linarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hN']
  calc
    _ ≤ (m + δ * (N + 1) * (2 + 2 * (N : ℝ) / m)) / N :=
      div_le_div_of_nonneg_right htotal hN'.le
    _ ≤ 1 / K + 1 / N + δ * 2 * (2 + 2 * K) := by
      rw [add_div]
      apply add_le_add hmratio
      calc
        _ = δ * (((N : ℝ) + 1) / N) * (2 + 2 * ((N : ℝ) / m)) := by ring
        _ ≤ _ := by gcongr
    _ < ε := by
      dsimp [δ]
      have hδeq : ε / (16 * ((K : ℝ) + 1)) * 2 * (2 + 2 * K) = ε / 4 := by
        field_simp
        ring
      rw [hδeq]
      linarith
private lemma tendsto_moebius_div :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Ioc 0 N,
      (ArithmeticFunction.moebius n : ℝ) / n) atTop (𝓝 0) := by
  have hμ (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hE := tendsto_fractional_average (fun n ↦ (ArithmeticFunction.moebius n : ℝ))
    hμ tendsto_moebius_average
  have hlim := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).add hE
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsum := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.moebius N
  have hid : ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.moebius n * (N / n : ℕ) = (1 : ℤ) := by
    simpa [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply,
      Nat.succ_le_iff.mpr hN] using hsum.symm
  have hid' : ∑ n ∈ Finset.Ioc 0 N,
      (ArithmeticFunction.moebius n : ℝ) * (N / n : ℕ) = 1 := by
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_one] using
      congrArg (fun x : ℤ ↦ (x : ℝ)) hid
  have hErange : (∑ n ∈ Finset.range (N + 1),
      Int.fract ((N : ℝ) / ((n : ℕ) : ℝ)) * (ArithmeticFunction.moebius n : ℝ)) =
      ∑ n ∈ Finset.Ioc 0 N,
        Int.fract ((N : ℝ) / ((n : ℕ) : ℝ)) * (ArithmeticFunction.moebius n : ℝ) := by
    rw [Nat.range_eq_Icc_zero_sub_one _ (by omega), Nat.add_sub_cancel,
      Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons]
    simp
  rw [hErange, ← hid', ← add_div]
  field_simp [hN']
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fract_div_eq]
  ring

open scoped Classical in
private lemma sum_nthRoots_pow (n m : ℕ) (hn : 0 < n) :
    ∑ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), ζ ^ m = if n ∣ m then (n : ℂ) else 0 := by
  let ξ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hξ : IsPrimitiveRoot ξ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hξ0 : ξ ≠ 0 := Complex.exp_ne_zero _
  have hmem (ζ : ℂ) : ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ) ↔ ζ ^ n = 1 :=
    Polynomial.mem_nthRootsFinset hn 1
  by_cases hnm : n ∣ m
  · rw [ite_eq_left hnm]
    have hpow (ζ : ℂ) (hζ : ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ)) : ζ ^ m = 1 := by
      obtain ⟨r, rfl⟩ := hnm
      rw [pow_mul, (hmem ζ).mp hζ, one_pow]
    simp_rw [Finset.sum_congr rfl hpow, Finset.sum_const, hξ.card_nthRootsFinset, nsmul_eq_mul,
      mul_one]
  · rw [ite_eq_right hnm]
    have hperm : (∑ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), (ξ * ζ) ^ m) =
        ∑ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), ζ ^ m := by
      apply Finset.sum_bij (fun ζ _ ↦ ξ * ζ)
      · intro ζ hζ
        rw [hmem, mul_pow, hξ.pow_eq_one, (hmem ζ).mp hζ, one_mul]
      · intro ζ _ η _ heq
        exact mul_left_cancel₀ hξ0 heq
      · intro ζ hζ
        refine ⟨ξ⁻¹ * ζ, ?_, ?_⟩
        · rw [hmem, mul_pow, inv_pow, hξ.pow_eq_one, (hmem ζ).mp hζ, inv_one, one_mul]
        · simp [hξ0]
      · intro ζ _
        rfl
    simp_rw [mul_pow, ← Finset.mul_sum] at hperm
    have hp : (ξ ^ m - 1) * (∑ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), ζ ^ m) = 0 := by
      rw [sub_mul, one_mul, hperm, sub_self]
    exact (mul_eq_zero.mp hp).resolve_left
      (sub_ne_zero.mpr ((hξ.pow_eq_one_iff_dvd m).not.mpr hnm))
open scoped Classical in
private lemma sum_primitiveRoots_divisors (n m : ℕ) :
    ∑ d ∈ n.divisors, ∑ ζ ∈ primitiveRoots d ℂ, ζ ^ m =
      ∑ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), ζ ^ m := by
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
  symm
  apply Finset.sum_biUnion
  intro a _ b _ hab
  exact IsPrimitiveRoot.disjoint hab
open scoped Classical in
private lemma primitiveRoots_moebius (n m : ℕ) (hn : 0 < n) :
    ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ m =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℂ) *
        (if d ∣ m then (d : ℂ) else 0) := by
  have h (k : ℕ) (hk : 0 < k) :
      (∑ d ∈ k.divisors, ∑ ζ ∈ primitiveRoots d ℂ, ζ ^ m) =
      if k ∣ m then (k : ℂ) else 0 := by
    rw [sum_primitiveRoots_divisors, sum_nthRoots_pow k m hk]
  have hinv := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp h n hn
  rw [Nat.sum_divisorsAntidiagonal' (fun a b ↦ (ArithmeticFunction.moebius a : ℂ) *
    (if b ∣ m then (b : ℂ) else 0))] at hinv
  exact hinv.symm

private lemma hasSum_partialLog {z : ℂ} (hz : ‖z‖ < 1) (N : ℕ) :
    HasSum (fun m : ℕ ↦ z ^ m / (m : ℂ) *
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ m)
      (∑ n ∈ Finset.Icc 1 N,
        -(n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, Complex.log (1 - z * ζ)) := by
  have hroot (n : ℕ) (hn : n ∈ Finset.Icc 1 N) (ζ : ℂ)
      (hζ : ζ ∈ primitiveRoots n ℂ) :
      HasSum (fun m : ℕ ↦ (z * ζ) ^ m / (m : ℂ)) (-Complex.log (1 - z * ζ)) := by
    apply Complex.hasSum_taylorSeries_neg_log
    simpa [norm_mul, (isPrimitiveRoot_of_mem_primitiveRoots hζ).norm'_eq_one
      (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1)] using hz
  have hn (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :=
    (hasSum_sum (fun ζ hζ ↦ hroot n hn ζ hζ)).mul_left (n : ℂ)⁻¹
  have h := hasSum_sum hn
  convert h using 1
  · ext m
    simp_rw [Finset.mul_sum, mul_pow, div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro ζ _
    ring
  · simp [Finset.sum_neg_distrib, neg_mul]

private noncomputable def weightedMoebius : ArithmeticFunction ℂ :=
  ⟨fun n ↦ (ArithmeticFunction.moebius n : ℂ) / n, by simp⟩
private noncomputable def divisorIndicator (m : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun d ↦ if d ∈ m.divisors then 1 else 0, by simp⟩
open scoped Classical in
private lemma weightedMoebius_convolution (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (divisorIndicator m * weightedMoebius) n =
      (n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ m := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun d r ↦ divisorIndicator m d * weightedMoebius r),
    primitiveRoots_moebius n m hn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdn := Nat.dvd_of_mem_divisors hd
  have hrpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos
  have hfactor : (n : ℂ) = (d : ℂ) * (n / d : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdn).symm
  by_cases hdm : d ∣ m
  · have hdmem : d ∈ m.divisors := Nat.mem_divisors.mpr ⟨hdm, hm.ne'⟩
    simp only [divisorIndicator, weightedMoebius, ArithmeticFunction.coe_mk,
      hdmem, ite_true, hdm, one_mul, hfactor]
    field_simp [Nat.cast_ne_zero.mpr hdpos.ne', Nat.cast_ne_zero.mpr hrpos.ne']
  · simp [divisorIndicator, weightedMoebius, Nat.mem_divisors, hdm]
open scoped Classical in
private lemma partial_ramanujan_eq (N m : ℕ) (hm : 0 < m) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ m) =
      ∑ d ∈ m.divisors, ∑ r ∈ Finset.Ioc 0 (N / d),
        (ArithmeticFunction.moebius r : ℂ) / r := by
  have hconv := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (divisorIndicator m) weightedMoebius N
  have hleft : (∑ n ∈ Finset.Ioc 0 N, (divisorIndicator m * weightedMoebius) n) =
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ m := by
    rw [← Finset.Icc_add_one_left_eq_Ioc]
    apply Finset.sum_congr rfl
    intro n hn
    exact weightedMoebius_convolution n m (Finset.mem_Icc.mp hn).1 hm
  rw [hleft] at hconv
  rw [hconv]
  simp only [divisorIndicator, weightedMoebius, ArithmeticFunction.coe_mk,
    ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  apply Finset.sum_subset
  · intro d hd
    exact (Finset.mem_filter.mp hd).2
  · intro d hd hnot
    have hd0 := Nat.pos_of_mem_divisors hd
    have hdN : N < d := by
      simp only [Finset.mem_filter, Finset.mem_Ioc, hd, and_true, not_and] at hnot
      exact lt_of_not_ge (hnot hd0)
    simp [Nat.div_eq_of_lt hdN]
private lemma tendsto_weightedMoebius :
    Tendsto (fun N : ℕ ↦ ∑ r ∈ Finset.Ioc 0 N,
      (ArithmeticFunction.moebius r : ℂ) / r) atTop (𝓝 0) := by
  have h := Complex.continuous_ofReal.tendsto 0 |>.comp tendsto_moebius_div
  simpa only [Function.comp_def, Complex.ofReal_sum, Complex.ofReal_div,
    Complex.ofReal_intCast, Complex.ofReal_natCast, Complex.ofReal_zero] using h
open scoped Classical in
private lemma tendsto_partial_ramanujan (m : ℕ) (hm : 0 < m) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N,
      (n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ m) atTop (𝓝 0) := by
  have hdiv (d : ℕ) (hd : d ∈ m.divisors) :
      Tendsto (fun N : ℕ ↦ N / d) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b * d)] with N hN
    exact (Nat.le_div_iff_mul_le (Nat.pos_of_mem_divisors hd)).mpr hN
  have h := tendsto_finsetSum m.divisors (fun d hd ↦ tendsto_weightedMoebius.comp (hdiv d hd))
  simpa only [Function.comp_apply, Finset.sum_const_zero, ← partial_ramanujan_eq _ m hm] using h
open scoped Classical in
private lemma bound_partial_ramanujan : ∃ C : ℝ, 0 ≤ C ∧ ∀ N m : ℕ, 0 < m →
    ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ m‖ ≤ C * m := by
  obtain ⟨C, hC⟩ := tendsto_weightedMoebius.norm.bddAbove_range
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (Set.mem_range_self 0))
  refine ⟨C, hC0, ?_⟩
  intro N m hm
  rw [partial_ramanujan_eq N m hm]
  calc
    _ ≤ ∑ d ∈ m.divisors, ‖∑ r ∈ Finset.Ioc 0 (N / d),
        (ArithmeticFunction.moebius r : ℂ) / r‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ m.divisors, C := Finset.sum_le_sum (fun d _ ↦ hC (Set.mem_range_self (N / d)))
    _ = C * m.divisors.card := by simp [mul_comm]
    _ ≤ C * m := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.card_divisors_le_self m) hC0

@[expose] public section

/-- **Constancy of an infinite cyclotomic product.** For $n \ge 1$ and complex $z$, let
$\hat\Phi_n(z) = \prod_\omega (1 - z\omega)$, the product over the primitive $n$-th roots of
unity $\omega$; thus $\hat\Phi_1(z) = 1 - z$ and $\hat\Phi_n = \Phi_n$ for $n \ge 2$, where
$\Phi_n$ is the $n$-th cyclotomic polynomial. For every complex $z$ with $|z| < 1$, the partial
products $\prod_{n=1}^{N} \hat\Phi_n(z)^{-1/n}$ tend to $1$ as $N \to \infty$, where
$\hat\Phi_n(z)^{-1/n} = \exp\bigl(-\tfrac{1}{n} \sum_\omega \log(1 - z\omega)\bigr)$ and $\log$
is the principal branch of the logarithm.

Each factor $1 - z\omega$ has positive real part, and this branch equals $1$ at $z = 0$, as in
the paper's logarithmic-derivative proof. The paper writes the product as
$P(z) = -\prod_{n \ge 1} \Phi_n(z)^{-1/n}$; the sign absorbs $\Phi_1(z) = -(1 - z)$, and the
claim is $P(z) \equiv 1$.

Source: Hartosh Singh Bal, *Constancy of an Infinite Cyclotomic Product via Ramanujan Sums*,
INTEGERS 25 (2025), Article A96, Theorem 1 (`integers-2025-A96-thm-1`). -/
public theorem tendsto_prod_cyclotomicHat_inv_root_one {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 N,
        Complex.exp (-(n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, Complex.log (1 - z * ζ)))
      atTop (𝓝 1) := by
  obtain ⟨C, hC0, hC⟩ := bound_partial_ramanujan
  let F (N m : ℕ) : ℂ := z ^ m / (m : ℂ) *
    ∑ n ∈ Finset.Icc 1 N, (n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ m
  have hpoint (m : ℕ) : Tendsto (fun N ↦ F N m) atTop (𝓝 0) := by
    rcases m.eq_zero_or_pos with rfl | hm
    · simp only [F, Nat.cast_zero, div_zero, zero_mul]
      exact tendsto_const_nhds
    · simpa only [F, mul_zero] using
        (tendsto_partial_ramanujan m hm).const_mul (z ^ m / (m : ℂ))
  have hbound (N m : ℕ) : ‖F N m‖ ≤ C * ‖z‖ ^ m := by
    rcases m.eq_zero_or_pos with rfl | hm
    · simpa only [F, Nat.cast_zero, div_zero, zero_mul, norm_zero, pow_zero, mul_one] using hC0
    · calc
        _ = ‖z‖ ^ m / m * ‖∑ n ∈ Finset.Icc 1 N,
            (n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ m‖ := by
          simp only [F, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
        _ ≤ ‖z‖ ^ m / m * (C * m) :=
          mul_le_mul_of_nonneg_left (hC N m hm) (by positivity)
        _ = C * ‖z‖ ^ m := by
          field_simp
  have hsum : Summable (fun m : ℕ ↦ C * ‖z‖ ^ m) :=
    (summable_geometric_of_abs_lt_one
      (by simpa only [abs_of_nonneg (norm_nonneg z)] using hz)).mul_left C
  have hlimit := tendsto_tsum_of_dominated_convergence hsum hpoint
    (Eventually.of_forall fun N ↦ hbound N)
  have hlog := hlimit.congr (fun N ↦ (hasSum_partialLog hz N).tsum_eq)
  simp only [tsum_zero] at hlog
  have hexp := Complex.continuous_exp.tendsto 0 |>.comp hlog
  simpa only [tsum_zero, Complex.exp_zero, Function.comp_def, Complex.exp_sum] using hexp

end

end MetaMathlibExt
