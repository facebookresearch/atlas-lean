/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Weyl's equidistribution criterion: a real sequence is equidistributed modulo 1
if and only if every nontrivial Fourier mean vanishes.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import MathlibExt.Topology.ContinuousFunction.IntervalCutoff

open scoped BigOperators
open Filter Topology

@[expose] public section

namespace MetaMathlibExt

/-- The exponential monomial `e h t = exp (2 * π * h * t * I)`. -/
private noncomputable def wcE (h : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (h : ℝ) * t : ℝ) : ℂ) * Complex.I)

/-- Count of `n < N` with `Int.fract (x n)` in `[a, b)`. -/
private noncomputable def wcCnt (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  (Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
    (Finset.range N)).card

/-- Reduction mod 1 in the exponent. -/
private lemma wcE_fract (h : ℤ) (t : ℝ) : wcE h t = wcE h (Int.fract t) := by
  classical
  have ht : t = Int.fract t + (⌊t⌋ : ℝ) := by
    have h1 := Int.fract_add_floor t
    linarith
  have hre : (2 * Real.pi * (h : ℝ) * (Int.fract t + (⌊t⌋ : ℝ)) : ℝ) =
      (2 * Real.pi * (h : ℝ) * Int.fract t : ℝ) +
        ((h * ⌊t⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  have hc : ((((2 * Real.pi * (h : ℝ) * (Int.fract t + (⌊t⌋ : ℝ)) : ℝ)) : ℂ) *
      Complex.I) =
      ((((2 * Real.pi * (h : ℝ) * Int.fract t : ℝ)) : ℂ) * Complex.I) +
        ((((h * ⌊t⌋ : ℤ)) : ℂ)) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [hre]
    push_cast
    ring
  unfold wcE
  conv_lhs => rw [ht]
  rw [hc, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The monomial agrees with the circle Fourier monomial. -/
private lemma wcE_eq_fourier (h : ℤ) (t : ℝ) :
    wcE h t = fourier h ((t : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  unfold wcE
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- Lipschitz bound for the exponential monomial. -/
private lemma wcE_lipschitz (h : ℤ) (s t : ℝ) :
    ‖wcE h s - wcE h t‖ ≤ 2 * Real.pi * |(h : ℝ)| * |s - t| := by
  classical
  have hpi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)
  set u : ℝ := 2 * Real.pi * (h : ℝ) * (s - t) with hu
  have hdecomp : wcE h s = wcE h t * Complex.exp ((((u : ℝ)) : ℂ) * Complex.I) := by
    unfold wcE
    rw [← Complex.exp_add]
    congr 1
    rw [hu]
    push_cast
    ring
  have hnorm : ‖wcE h t‖ = 1 := by
    unfold wcE
    exact Complex.norm_exp_ofReal_mul_I _
  have hle : ‖Complex.exp ((((u : ℝ)) : ℂ) * Complex.I) - 1‖ ≤ ‖u‖ := by
    rw [mul_comm ((((u : ℝ)) : ℂ)) Complex.I]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  calc ‖wcE h s - wcE h t‖
      = ‖wcE h t * (Complex.exp ((((u : ℝ)) : ℂ) * Complex.I) - 1)‖ := by
        rw [hdecomp, mul_sub, mul_one]
    _ = ‖wcE h t‖ * ‖Complex.exp ((((u : ℝ)) : ℂ) * Complex.I) - 1‖ :=
        norm_mul _ _
    _ ≤ 1 * ‖u‖ := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left hle zero_le_one
    _ = 2 * Real.pi * |(h : ℝ)| * |s - t| := by
        simp only [hu, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpi, one_mul]

/-- Vanishing sum over roots of unity. -/
private lemma wc_rootsum (h : ℤ) (M : ℕ) (hh : h ≠ 0) (hM : h.natAbs < M) :
    ∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) = 0 := by
  classical
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have h0 : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hM
    exact_mod_cast h0
  set ω : ℂ := wcE h (1 / (M : ℝ)) with hω
  have hterm : ∀ k : ℕ, wcE h ((k : ℝ) / (M : ℝ)) = ω ^ k := by
    intro k
    rw [hω]
    unfold wcE
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpow : ω ^ M = 1 := by
    rw [← hterm M]
    unfold wcE
    have hexp : ((((2 * Real.pi * (h : ℝ) * ((M : ℝ) / (M : ℝ)) : ℝ)) : ℂ) *
        Complex.I) =
        ((((h : ℤ)) : ℂ)) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
      rw [div_self (ne_of_gt hMpos)]
      push_cast
      ring
    rw [hexp, Complex.exp_int_mul_two_pi_mul_I]
  have hne : ω ≠ 1 := by
    intro hcon
    rw [hω] at hcon
    unfold wcE at hcon
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hcon
    have hX : ((((2 * Real.pi * (h : ℝ) * (1 / (M : ℝ))) : ℝ)) : ℂ) =
        ((((n : ℤ)) : ℂ)) * (2 * ((Real.pi : ℝ) : ℂ)) := by
      have hstep : ((((2 * Real.pi * (h : ℝ) * (1 / (M : ℝ))) : ℝ)) : ℂ) *
            Complex.I =
            (((((n : ℤ)) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ)))) * Complex.I := by
        have hassoc : (((((n : ℤ)) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ)))) *
            Complex.I =
            (((n : ℤ)) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) :=
          mul_assoc _ _ _
        rw [hassoc]
        exact hn
      exact mul_right_cancel₀ Complex.I_ne_zero hstep
    have hreal : 2 * Real.pi * (h : ℝ) * (1 / (M : ℝ)) =
        (n : ℝ) * (2 * Real.pi) := by
      have hre := congrArg Complex.re hX
      simpa using hre
    have hfrac : (h : ℝ) / (M : ℝ) = (n : ℝ) := by
      have h2 : (2 : ℝ) * Real.pi ≠ 0 :=
        mul_ne_zero (by norm_num) Real.pi_ne_zero
      apply mul_right_cancel₀ h2
      have e1 : (h : ℝ) / (M : ℝ) * (2 * Real.pi) =
          2 * Real.pi * (h : ℝ) * (1 / (M : ℝ)) := by
        rw [div_eq_mul_one_div]
        ring
      rw [e1]
      exact hreal
    have hMn : (h : ℝ) = (n : ℝ) * (M : ℝ) := by
      have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
      conv_lhs => rw [← div_mul_cancel₀ (h : ℝ) hMne]
      rw [hfrac]
    have hint : h = n * (M : ℤ) := by
      have h2 : (h : ℝ) = ((n * (M : ℤ) : ℤ) : ℝ) := by
        push_cast
        exact hMn
      exact_mod_cast h2
    have habs : h.natAbs = n.natAbs * M := by
      rw [hint, Int.natAbs_mul]
      simp
    have hnne : n ≠ 0 := by
      intro hn0
      rw [hn0, zero_mul] at hint
      exact hh hint
    have h1 : 1 ≤ n.natAbs := by
      have hne0 : n.natAbs ≠ 0 := fun h0 => hnne (Int.natAbs_eq_zero.mp h0)
      omega
    have h2 : 1 * M ≤ n.natAbs * M := mul_le_mul_left h1 M
    omega
  simp only [hterm]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- Membership in cell `k` is a floor equation. -/
private lemma wc_mem_cell (M : ℕ) (hM : 1 ≤ M) (y : ℝ) (hy0 : 0 ≤ y) (k : ℕ) :
    ⌊(M : ℝ) * y⌋₊ = k ↔
      (k : ℝ) / (M : ℝ) ≤ y ∧ y < ((k : ℝ) + 1) / (M : ℝ) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have h0 : 0 < M := hM
    exact_mod_cast h0
  have hMy : (0 : ℝ) ≤ (M : ℝ) * y := mul_nonneg (le_of_lt hMpos) hy0
  rw [Nat.floor_eq_iff hMy]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hMpos, mul_comm y ((M : ℝ))]
      exact h1
    · rw [lt_div_iff₀ hMpos, mul_comm y ((M : ℝ))]
      exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hMpos, mul_comm y ((M : ℝ))] at h1
      exact h1
    · rw [lt_div_iff₀ hMpos, mul_comm y ((M : ℝ))] at h2
      exact h2

/-- Fibre cards are cell counts. -/
private lemma wc_fibre_eq (x : ℕ → ℝ) (M N k : ℕ) (hM : 1 ≤ M) :
    (Finset.filter (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k)
      (Finset.range N)).card =
      wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N := by
  unfold wcCnt
  congr 1
  apply Finset.filter_congr
  intro n _
  exact wc_mem_cell M hM _ (Int.fract_nonneg _) k

/-- Every index lands in some cell. -/
private lemma wc_maps (x : ℕ → ℝ) (M N : ℕ) (hM : 1 ≤ M) :
    ∀ n ∈ Finset.range N, ⌊(M : ℝ) * Int.fract (x n)⌋₊ ∈ Finset.range M := by
  intro n hn
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have h0 : 0 < M := hM
    exact_mod_cast h0
  rw [Finset.mem_range]
  have hy0 : 0 ≤ Int.fract (x n) := Int.fract_nonneg _
  have hy1 : Int.fract (x n) < 1 := Int.fract_lt_one _
  rw [Nat.floor_lt (mul_nonneg (le_of_lt hMpos) hy0)]
  calc (M : ℝ) * Int.fract (x n) < (M : ℝ) * 1 :=
        mul_lt_mul_of_pos_left hy1 hMpos
    _ = ((M : ℕ) : ℝ) := mul_one _

/-- The cell counts add up to `N`. -/
private lemma wc_cells_sum (x : ℕ → ℝ) (M N : ℕ) (hM : 1 ≤ M) :
    ∑ k ∈ Finset.range M,
      wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N = N := by
  have hmapsSet : ((Finset.range N : Set ℕ)).MapsTo
      (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊) (Finset.range M) :=
    fun n hn => Finset.mem_coe.mpr (wc_maps x M N hM n (Finset.mem_coe.mp hn))
  calc ∑ k ∈ Finset.range M,
          wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N
      = ∑ k ∈ Finset.range M, (Finset.filter
          (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k) (Finset.range N)).card :=
        Finset.sum_congr rfl (fun k _ => (wc_fibre_eq x M N k hM).symm)
    _ = (Finset.range N).card :=
        (Finset.card_eq_sum_card_fiberwise hmapsSet).symm
    _ = N := Finset.card_range N

/-- Approximation of the exponential sum by cell contributions. -/
private lemma wc_cells_approx (x : ℕ → ℝ) (h : ℤ) (M N : ℕ) (hM : 1 ≤ M) :
    ‖∑ n ∈ Finset.range N, wcE h (x n) -
      ∑ k ∈ Finset.range M,
        wcE h ((k : ℝ) / (M : ℝ)) *
          (wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℂ)‖
      ≤ 2 * Real.pi * |(h : ℝ)| / (M : ℝ) * (N : ℝ) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have h0 : 0 < M := hM
    exact_mod_cast h0
  have hCnn : (0 : ℝ) ≤ 2 * Real.pi * |(h : ℝ)| :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)) (abs_nonneg _)
  have hmaps : ∀ n ∈ Finset.range N,
      ⌊(M : ℝ) * Int.fract (x n)⌋₊ ∈ Finset.range M :=
    wc_maps x M N hM
  have hmapsSet : ((Finset.range N : Set ℕ)).MapsTo
      (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊) (Finset.range M) :=
    fun n hn => Finset.mem_coe.mpr (hmaps n (Finset.mem_coe.mp hn))
  have hfib_sum : ∑ n ∈ Finset.range N, wcE h (x n) =
      ∑ k ∈ Finset.range M, ∑ n ∈ Finset.range N with
        ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k, wcE h (x n) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hcell_sum : ∀ k ∈ Finset.range M,
      wcE h ((k : ℝ) / (M : ℝ)) *
          (wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℂ) =
        ∑ n ∈ Finset.range N with ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k,
          wcE h ((k : ℝ) / (M : ℝ)) := by
    intro k hk
    rw [Finset.sum_const, nsmul_eq_mul, ← wc_fibre_eq x M N k hM, mul_comm]
  have hdiff : (∑ k ∈ Finset.range M, ∑ n ∈ Finset.range N with
        ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k, wcE h (x n)) -
      (∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) *
        (wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℂ)) =
      ∑ k ∈ Finset.range M, ∑ n ∈ Finset.range N with
        ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k,
          (wcE h (x n) - wcE h ((k : ℝ) / (M : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hcell_sum k hk, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range M,
      ∀ n ∈ Finset.filter (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k)
        (Finset.range N),
      ‖wcE h (x n) - wcE h ((k : ℝ) / (M : ℝ))‖ ≤
        2 * Real.pi * |(h : ℝ)| / (M : ℝ) := by
    intro k hk n hn
    rw [Finset.mem_filter] at hn
    have hmem := (wc_mem_cell M hM _ (Int.fract_nonneg _) k).mp hn.2
    have h1M : (0 : ℝ) < 1 / (M : ℝ) := one_div_pos.mpr hMpos
    have hbd : |Int.fract (x n) - (k : ℝ) / (M : ℝ)| ≤ 1 / (M : ℝ) := by
      rw [abs_le]
      have hsplit : ((k : ℝ) + 1) / (M : ℝ) =
          (k : ℝ) / (M : ℝ) + 1 / (M : ℝ) := add_div _ _ _
      constructor
      · have hle := hmem.1
        have hnn := le_of_lt h1M
        linarith
      · have hlt := hmem.2
        rw [hsplit] at hlt
        linarith
    calc ‖wcE h (x n) - wcE h ((k : ℝ) / (M : ℝ))‖
        = ‖wcE h (Int.fract (x n)) - wcE h ((k : ℝ) / (M : ℝ))‖ := by
          rw [wcE_fract]
      _ ≤ 2 * Real.pi * |(h : ℝ)| * |Int.fract (x n) - (k : ℝ) / (M : ℝ)| :=
          wcE_lipschitz h _ _
      _ ≤ 2 * Real.pi * |(h : ℝ)| * (1 / (M : ℝ)) :=
          mul_le_mul_of_nonneg_left hbd hCnn
      _ = 2 * Real.pi * |(h : ℝ)| / (M : ℝ) := by ring
  have hcount : ∑ k ∈ Finset.range M, (Finset.filter
      (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k)
      (Finset.range N)).card = N := by
    have hkey := Finset.card_eq_sum_card_fiberwise hmapsSet
    rw [Finset.card_range] at hkey
    exact hkey.symm
  calc ‖∑ n ∈ Finset.range N, wcE h (x n) -
        ∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) *
          (wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℂ)‖
      = ‖∑ k ∈ Finset.range M, ∑ n ∈ Finset.range N with
          ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k,
            (wcE h (x n) - wcE h ((k : ℝ) / (M : ℝ)))‖ := by
        rw [hfib_sum, hdiff]
    _ ≤ ∑ k ∈ Finset.range M,
          ‖∑ n ∈ Finset.range N with ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k,
            (wcE h (x n) - wcE h ((k : ℝ) / (M : ℝ)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range M, ∑ n ∈ Finset.range N with
          ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k,
            ‖wcE h (x n) - wcE h ((k : ℝ) / (M : ℝ))‖ := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range M, ∑ n ∈ Finset.range N with
          ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k,
            (2 * Real.pi * |(h : ℝ)| / (M : ℝ)) := by
        refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun n hn => ?_
        exact hterm k hk n hn
    _ = 2 * Real.pi * |(h : ℝ)| / (M : ℝ) * (N : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.sum_mul, ← Nat.cast_sum, hcount, mul_comm]

/-- Forward direction (equidistribution implies Fourier means vanish). -/
private lemma wc_forward (x : ℕ → ℝ)
    (heq : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      Tendsto (fun N : ℕ =>
        ((Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
          (Finset.range N)).card : ℝ) / (N : ℝ))
        atTop (nhds (b - a)))
    (h : ℤ) (hh : h ≠ 0) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n))
      atTop (nhds 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt
    (max ((h.natAbs : ℕ) : ℝ) (2 * Real.pi * |(h : ℝ)| / (ε / 2)))
  set M := M₀ + 1 with hMdef
  have hMnat : h.natAbs < M := by
    have hlt : ((h.natAbs : ℕ) : ℝ) < ((M : ℕ) : ℝ) := by
      calc ((h.natAbs : ℕ) : ℝ) ≤
            max ((h.natAbs : ℕ) : ℝ) (2 * Real.pi * |(h : ℝ)| / (ε / 2)) :=
            le_max_left _ _
        _ < (M₀ : ℝ) := hM₀
        _ < ((M : ℕ) : ℝ) := by
            rw [hMdef]
            push_cast
            linarith [Nat.lt_succ_self M₀]
    exact_mod_cast hlt
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    exact Nat.le_add_left 1 M₀
  have hMposR : (0 : ℝ) < (M : ℝ) := by
    have h0 : 0 < M := hM1
    exact_mod_cast h0
  have hMbound : 2 * Real.pi * |(h : ℝ)| / (M : ℝ) < ε / 2 := by
    have hMgt : 2 * Real.pi * |(h : ℝ)| / (ε / 2) < (M : ℝ) := by
      calc 2 * Real.pi * |(h : ℝ)| / (ε / 2)
          ≤ max ((h.natAbs : ℕ) : ℝ) (2 * Real.pi * |(h : ℝ)| / (ε / 2)) :=
            le_max_right _ _
        _ < (M₀ : ℝ) := hM₀
        _ ≤ (M : ℝ) := by
            rw [hMdef]
            push_cast
            linarith [Nat.le_succ M₀]
    rw [div_lt_iff₀ hMposR, mul_comm (ε / 2) ((M : ℝ))]
    exact (div_lt_iff₀ hε2).mp hMgt
  have hlim_val : ∀ k : ℕ,
      ((k : ℝ) + 1) / (M : ℝ) - (k : ℝ) / (M : ℝ) = 1 / (M : ℝ) := by
    intro k
    rw [add_div, add_sub_cancel_left]
  have hcell : ∀ k : ℕ, k < M →
      Tendsto (fun N : ℕ =>
        ((wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℝ)) /
          (N : ℝ))
        atTop (nhds (1 / (M : ℝ))) := by
    intro k hk
    have ha0 : (0 : ℝ) ≤ (k : ℝ) / (M : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hMposR)
    have hab : (k : ℝ) / (M : ℝ) < ((k : ℝ) + 1) / (M : ℝ) := by
      have h1 : (k : ℝ) < (k : ℝ) + 1 := lt_add_one _
      exact (div_lt_div_iff_of_pos_right hMposR).mpr h1
    have hb1 : ((k : ℝ) + 1) / (M : ℝ) ≤ 1 := by
      rw [div_le_one hMposR]
      have hle : k + 1 ≤ M := hk
      exact_mod_cast hle
    have hlim := heq _ _ ha0 hab hb1
    rwa [hlim_val k] at hlim
  have hS : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range M,
        wcE h ((k : ℝ) / (M : ℝ)) *
          (((wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℝ) /
            (N : ℝ) : ℝ) : ℂ))
      atTop (nhds 0) := by
    have h0 : (∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) *
        ((((1 : ℝ) / (M : ℝ) : ℝ)) : ℂ)) = 0 := by
      rw [← Finset.sum_mul, wc_rootsum h M hh hMnat, zero_mul]
    rw [← h0]
    refine tendsto_finsetSum _ fun k hk => ?_
    have hkcell := hcell k (Finset.mem_range.mp hk)
    have hkC : Tendsto (fun N : ℕ =>
        ((((wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℝ) /
          (N : ℝ) : ℝ)) : ℂ))
        atTop (nhds ((((1 / (M : ℝ) : ℝ))) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hkcell
    exact Filter.Tendsto.const_mul _ hkC
  have hFS : ∀ N : ℕ, 1 ≤ N →
      (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n) -
        ∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) *
          ((((wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℝ) /
            (N : ℝ) : ℝ)) : ℂ) =
      (1 / (N : ℂ)) * (∑ n ∈ Finset.range N, wcE h (x n) -
        ∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) *
          (wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℂ)) := by
    intro N hN
    have hNc : (N : ℂ) ≠ 0 := by
      have hNe : N ≠ 0 := by omega
      exact_mod_cast hNe
    rw [mul_sub]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    field_simp
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hS) (ε / 2) hε2
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN1 : N ≥ N₁ := le_trans (Nat.le_max_left _ _) hN
  have hNge1 : 1 ≤ N := le_trans (Nat.le_max_right _ _) hN
  have hdist := hN₁ N hN1
  have hMle : (1 : ℕ) ≤ M := hM1
  have hD := wc_cells_approx x h M N hMle
  have hFSle : ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n) -
      ∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) *
        ((((wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℝ) /
          (N : ℝ) : ℝ)) : ℂ)‖ ≤ 2 * Real.pi * |(h : ℝ)| / (M : ℝ) := by
    have hnorm1 : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by
      rw [norm_div, norm_one, RCLike.norm_natCast]
    rw [hFS N hNge1, norm_mul, hnorm1]
    have hNr : (N : ℝ) ≠ 0 := by
      have hNe : N ≠ 0 := by omega
      exact_mod_cast hNe
    have hrearr : (1 / (N : ℝ)) * (2 * Real.pi * |(h : ℝ)| / (M : ℝ) * (N : ℝ)) =
        (2 * Real.pi * |(h : ℝ)| / (M : ℝ)) * ((N : ℝ) / (N : ℝ)) := by ring
    have hle : (1 / (N : ℝ)) * ‖∑ n ∈ Finset.range N, wcE h (x n) -
          ∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) *
            (wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℂ)‖ ≤
        (1 / (N : ℝ)) * (2 * Real.pi * |(h : ℝ)| / (M : ℝ) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    rwa [hrearr, div_self hNr, mul_one] at hle
  rw [dist_eq_norm, sub_zero]
  calc ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n)‖
      = ‖((1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n) -
          ∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) *
            ((((wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℝ) /
              (N : ℝ) : ℝ)) : ℂ)) +
          ∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) *
            ((((wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℝ) /
              (N : ℝ) : ℝ)) : ℂ)‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n) -
          ∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) *
            ((((wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℝ) /
              (N : ℝ) : ℝ)) : ℂ)‖ +
          ‖∑ k ∈ Finset.range M, wcE h ((k : ℝ) / (M : ℝ)) *
            ((((wcCnt x ((k : ℝ) / (M : ℝ)) (((k : ℝ) + 1) / (M : ℝ)) N : ℝ) /
              (N : ℝ) : ℝ)) : ℂ)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add
        · exact lt_of_le_of_lt hFSle hMbound
        · rwa [dist_eq_norm, sub_zero] at hdist
    _ = ε := by ring

/-- Averages of Fourier monomials converge to their integrals. -/
private lemma wc_monomial (x : ℕ → ℝ)
    (hfour : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n))
        atTop (nhds 0))
    (h : ℤ) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        fourier h ((x n : ℝ) : AddCircle (1 : ℝ)))
      atTop (nhds (∫ t in (0 : ℝ)..1, fourier h ((t : ℝ) : AddCircle (1 : ℝ)))) := by
  classical
  by_cases hh : h = 0
  · subst hh
    have havg : (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        fourier (0 : ℤ) ((x n : ℝ) : AddCircle (1 : ℝ))) =ᶠ[atTop]
        fun _ => 1 := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNc : (N : ℂ) ≠ 0 := by
        have hNe : N ≠ 0 := by omega
        exact_mod_cast hNe
      simp only [fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one]
      exact div_mul_cancel₀ 1 hNc
    have hint : (∫ t in (0 : ℝ)..1,
        fourier (0 : ℤ) ((t : ℝ) : AddCircle (1 : ℝ))) = 1 := by
      simp only [fourier_zero]
      rw [intervalIntegral.integral_const]
      simp
    rw [hint]
    exact Filter.Tendsto.congr' havg.symm tendsto_const_nhds
  · have havg : (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        fourier h ((x n : ℝ) : AddCircle (1 : ℝ))) =
        (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n)) := by
      funext N
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      exact (wcE_eq_fourier h (x n)).symm
    have hc : (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((h : ℤ) : ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · norm_num
          · exact_mod_cast Real.pi_ne_zero
        · exact Complex.I_ne_zero
      · exact_mod_cast hh
    have hfun : (fun t : ℝ => fourier h ((t : ℝ) : AddCircle (1 : ℝ))) =
        (fun t : ℝ => Complex.exp
          ((2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((h : ℤ) : ℂ)) * ((t : ℝ) : ℂ))) := by
      funext t
      rw [fourier_coe_apply]
      congr 1
      push_cast
      ring
    have hint : (∫ t in (0 : ℝ)..1,
        fourier h ((t : ℝ) : AddCircle (1 : ℝ))) = 0 := by
      rw [hfun, integral_exp_mul_complex hc]
      have e1 : Complex.exp ((2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((h : ℤ) : ℂ)) *
          (((1 : ℝ)) : ℂ)) = 1 := by
        have hexp : ((2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((h : ℤ) : ℂ)) *
            (((1 : ℝ)) : ℂ)) =
            (((h : ℤ)) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
          push_cast
          ring
        rw [hexp, Complex.exp_int_mul_two_pi_mul_I]
      have e0 : Complex.exp ((2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((h : ℤ) : ℂ)) *
          (((0 : ℝ)) : ℂ)) = 1 := by
        rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      rw [e1, e0, sub_self, zero_div]
    rw [havg, hint]
    exact hfour h hh

/-- The real coercion to the circle is continuous. -/
private lemma wc_coe_cont :
    Continuous (fun t : ℝ => ((t : ℝ) : AddCircle (1 : ℝ))) :=
  QuotientAddGroup.continuous_mk

/-- Averages are bounded by the sup norm. -/
private lemma wc_avg_le (x : ℕ → ℝ) (G : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ)
    (hN : 1 ≤ N) :
    ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, G ((x n : ℝ) : AddCircle (1 : ℝ))‖ ≤
      ‖G‖ := by
  classical
  have hNr : (0 : ℝ) < (N : ℝ) := by
    have h0 : 0 < N := by omega
    exact_mod_cast h0
  calc ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, G ((x n : ℝ) : AddCircle (1 : ℝ))‖
      = (1 / (N : ℝ)) *
          ‖∑ n ∈ Finset.range N, G ((x n : ℝ) : AddCircle (1 : ℝ))‖ := by
        rw [norm_mul, norm_div, norm_one, RCLike.norm_natCast]
    _ ≤ (1 / (N : ℝ)) * (∑ n ∈ Finset.range N, ‖G‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ‖∑ n ∈ Finset.range N, G ((x n : ℝ) : AddCircle (1 : ℝ))‖
            ≤ ∑ n ∈ Finset.range N, ‖G ((x n : ℝ) : AddCircle (1 : ℝ))‖ :=
              norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.range N, ‖G‖ :=
              Finset.sum_le_sum fun n _ => ContinuousMap.norm_coe_le_norm _ _
    _ = ‖G‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          div_mul_cancel₀ 1 (ne_of_gt hNr), one_mul]

/-- Circle integrals over `[0, 1]` are bounded by the sup norm. -/
private lemma wc_int_le (G : C(AddCircle (1 : ℝ), ℂ)) :
    ‖∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ))‖ ≤ ‖G‖ := by
  classical
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := ‖G‖)
    (f := fun t : ℝ => G ((t : ℝ) : AddCircle (1 : ℝ)))
    (fun t _ => ContinuousMap.norm_coe_le_norm _ _)
  rwa [sub_zero, abs_one, mul_one] at h

/-- Averages of every continuous circle function converge to its integral. -/
private lemma wc_all_cont (x : ℕ → ℝ)
    (hfour : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n))
        atTop (nhds 0))
    (F : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        F ((x n : ℝ) : AddCircle (1 : ℝ)))
      atTop (nhds (∫ t in (0 : ℝ)..1, F ((t : ℝ) : AddCircle (1 : ℝ)))) := by
  classical
  have hspan : ∀ G : C(AddCircle (1 : ℝ), ℂ),
      G ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) →
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          G ((x n : ℝ) : AddCircle (1 : ℝ)))
        atTop (nhds (∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ)))) := by
    intro G hG
    refine Submodule.span_induction (p := fun G _ =>
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          G ((x n : ℝ) : AddCircle (1 : ℝ)))
        atTop (nhds (∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ))))) ?_ ?_ ?_ ?_ hG
    · intro G' hmem
      obtain ⟨h, rfl⟩ := hmem
      exact wc_monomial x hfour h
    · have h0avg : (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          (0 : C(AddCircle (1 : ℝ), ℂ)) ((x n : ℝ) : AddCircle (1 : ℝ))) =
          fun _ => 0 := by
        funext N
        simp
      have h0int : (∫ t in (0 : ℝ)..1,
          (0 : C(AddCircle (1 : ℝ), ℂ)) ((t : ℝ) : AddCircle (1 : ℝ))) = 0 := by
        simp
      rw [h0avg, h0int]
      exact tendsto_const_nhds
    · intro G1 G2 _ _ ih1 ih2
      have hcont1 : Continuous (fun t : ℝ => G1 ((t : ℝ) : AddCircle (1 : ℝ))) :=
        G1.continuous.comp wc_coe_cont
      have hcont2 : Continuous (fun t : ℝ => G2 ((t : ℝ) : AddCircle (1 : ℝ))) :=
        G2.continuous.comp wc_coe_cont
      have hint : (∫ t in (0 : ℝ)..1,
          (G1 + G2) ((t : ℝ) : AddCircle (1 : ℝ))) =
          (∫ t in (0 : ℝ)..1, G1 ((t : ℝ) : AddCircle (1 : ℝ))) +
          (∫ t in (0 : ℝ)..1, G2 ((t : ℝ) : AddCircle (1 : ℝ))) := by
        have e : (fun t : ℝ => (G1 + G2) ((t : ℝ) : AddCircle (1 : ℝ))) =
            (fun t : ℝ => G1 ((t : ℝ) : AddCircle (1 : ℝ)) +
              G2 ((t : ℝ) : AddCircle (1 : ℝ))) := by
          funext t
          exact ContinuousMap.add_apply _ _ _
        rw [e]
        exact intervalIntegral.integral_add (hcont1.intervalIntegrable _ _)
          (hcont2.intervalIntegrable _ _)
      have havg : (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          (G1 + G2) ((x n : ℝ) : AddCircle (1 : ℝ))) =
          (fun N : ℕ => ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            G1 ((x n : ℝ) : AddCircle (1 : ℝ))) +
            ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
              G2 ((x n : ℝ) : AddCircle (1 : ℝ)))) := by
        funext N
        simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]
      rw [havg, hint]
      exact ih1.add ih2
    · intro c G' _ ih
      have havg : (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          (c • G') ((x n : ℝ) : AddCircle (1 : ℝ))) =
          (fun N : ℕ => c * ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            G' ((x n : ℝ) : AddCircle (1 : ℝ)))) := by
        funext N
        simp only [ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        ring
      have hint : (∫ t in (0 : ℝ)..1,
          (c • G') ((t : ℝ) : AddCircle (1 : ℝ))) =
          c * (∫ t in (0 : ℝ)..1, G' ((t : ℝ) : AddCircle (1 : ℝ))) := by
        have e : (fun t : ℝ => (c • G') ((t : ℝ) : AddCircle (1 : ℝ))) =
            (fun t : ℝ => c * (G' ((t : ℝ) : AddCircle (1 : ℝ)))) := by
          funext t
          simp only [ContinuousMap.smul_apply, smul_eq_mul]
        rw [e, intervalIntegral.integral_const_mul]
      rw [havg, hint]
      exact Filter.Tendsto.const_mul _ ih
  have hdense : ∀ ε : ℝ, 0 < ε →
      ∃ G ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))),
        dist F G < ε := by
    intro ε hε
    have htop := span_fourier_closure_eq_top (T := (1 : ℝ))
    have h0 : F ∈
        Submodule.topologicalClosure
          (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) := by
      rw [htop]
      simp
    have hmem : F ∈ closure
        ((Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) : Set _) := by
      rw [← Submodule.topologicalClosure_coe]
      exact h0
    obtain ⟨G, hGs, hdist⟩ := (Metric.mem_closure_iff.mp hmem) ε hε
    exact ⟨G, hGs, hdist⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨G, hGs, hdist⟩ := hdense (ε / 3) (by linarith)
  have hG := hspan G hGs
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hG) (ε / 3) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN0 : N ≥ N₀ := le_trans (Nat.le_max_left _ _) hN
  have hNge1 : 1 ≤ N := le_trans (Nat.le_max_right _ _) hN
  have h1 := hN₀ N hN0
  have h1n : ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
      G ((x n : ℝ) : AddCircle (1 : ℝ)) -
      (∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ)))‖ < ε / 3 := by
    rwa [dist_eq_norm] at h1
  have hFG : ‖F - G‖ < ε / 3 := by
    rwa [dist_eq_norm] at hdist
  have havgFG : ‖((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
      F ((x n : ℝ) : AddCircle (1 : ℝ))) -
      ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        G ((x n : ℝ) : AddCircle (1 : ℝ)))‖ ≤ ‖F - G‖ := by
    have e : ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        F ((x n : ℝ) : AddCircle (1 : ℝ))) -
        ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          G ((x n : ℝ) : AddCircle (1 : ℝ))) =
        ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          (F - G) ((x n : ℝ) : AddCircle (1 : ℝ))) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
    rw [e]
    exact wc_avg_le x (F - G) N hNge1
  have hGc : IntervalIntegrable (fun t : ℝ => G ((t : ℝ) : AddCircle (1 : ℝ)))
      MeasureTheory.volume 0 1 :=
    (G.continuous.comp wc_coe_cont).intervalIntegrable _ _
  have hFc : IntervalIntegrable (fun t : ℝ => F ((t : ℝ) : AddCircle (1 : ℝ)))
      MeasureTheory.volume 0 1 :=
    (F.continuous.comp wc_coe_cont).intervalIntegrable _ _
  have hintFG : ‖(∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ))) -
      (∫ t in (0 : ℝ)..1, F ((t : ℝ) : AddCircle (1 : ℝ)))‖ ≤ ‖F - G‖ := by
    have e : (∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ))) -
        (∫ t in (0 : ℝ)..1, F ((t : ℝ) : AddCircle (1 : ℝ))) =
        (∫ t in (0 : ℝ)..1, (G - F) ((t : ℝ) : AddCircle (1 : ℝ))) := by
      have e2 : (fun t : ℝ => G ((t : ℝ) : AddCircle (1 : ℝ)) -
          F ((t : ℝ) : AddCircle (1 : ℝ))) =
          (fun t : ℝ => (G - F) ((t : ℝ) : AddCircle (1 : ℝ))) := by
        funext t
        exact (ContinuousMap.sub_apply _ _ _).symm
      rw [← intervalIntegral.integral_sub hGc hFc, e2]
    rw [e]
    calc ‖∫ t in (0 : ℝ)..1, (G - F) ((t : ℝ) : AddCircle (1 : ℝ))‖ ≤ ‖G - F‖ :=
          wc_int_le _
      _ = ‖F - G‖ := norm_sub_rev _ _
  rw [dist_eq_norm]
  calc ‖((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        F ((x n : ℝ) : AddCircle (1 : ℝ))) -
        (∫ t in (0 : ℝ)..1, F ((t : ℝ) : AddCircle (1 : ℝ)))‖
      = ‖(((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          F ((x n : ℝ) : AddCircle (1 : ℝ))) -
          ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            G ((x n : ℝ) : AddCircle (1 : ℝ)))) +
          (((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            G ((x n : ℝ) : AddCircle (1 : ℝ))) -
            (∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ))) +
            ((∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ))) -
              (∫ t in (0 : ℝ)..1, F ((t : ℝ) : AddCircle (1 : ℝ)))))‖ := by
        congr 1
        ring
    _ ≤ ‖((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          F ((x n : ℝ) : AddCircle (1 : ℝ))) -
          ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            G ((x n : ℝ) : AddCircle (1 : ℝ)))‖ +
          ‖((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            G ((x n : ℝ) : AddCircle (1 : ℝ))) -
            (∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ))) +
            ((∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ))) -
              (∫ t in (0 : ℝ)..1, F ((t : ℝ) : AddCircle (1 : ℝ))))‖ :=
        norm_add_le _ _
    _ ≤ ‖((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          F ((x n : ℝ) : AddCircle (1 : ℝ))) -
          ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            G ((x n : ℝ) : AddCircle (1 : ℝ)))‖ +
          (‖((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            G ((x n : ℝ) : AddCircle (1 : ℝ))) -
            (∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ)))‖ +
            ‖(∫ t in (0 : ℝ)..1, G ((t : ℝ) : AddCircle (1 : ℝ))) -
              (∫ t in (0 : ℝ)..1, F ((t : ℝ) : AddCircle (1 : ℝ)))‖) := by
        gcongr
        exact norm_add_le _ _
    _ < ε / 3 + (ε / 3 + ε / 3) := by
        apply add_lt_add
        · exact lt_of_le_of_lt havgFG hFG
        · apply add_lt_add
          · exact h1n
          · exact lt_of_le_of_lt hintFG hFG
    _ = ε := by ring

/-- Trapezoidal bump below the indicator of `[a, b)`. -/
private noncomputable abbrev wcPhi (a b δ t : ℝ) : ℝ :=
  Real.intervalCutoff a b δ t

/-- The bump sum is bounded by the interval count. -/
private lemma wcPhi_sum_le (x : ℕ → ℝ) (a b δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    ∑ n ∈ Finset.range N, wcPhi a b δ (Int.fract (x n)) ≤
      (wcCnt x a b N : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
    (fun n => wcPhi a b δ (Int.fract (x n)))
  have h1 : ∑ n ∈ Finset.filter
      (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b) (Finset.range N),
      wcPhi a b δ (Int.fract (x n)) ≤ (wcCnt x a b N : ℝ) := by
    calc ∑ n ∈ Finset.filter
            (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
            (Finset.range N),
            wcPhi a b δ (Int.fract (x n))
        ≤ ∑ _n ∈ Finset.filter
            (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
            (Finset.range N), (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => Real.intervalCutoff_le_one _ _ _ _
      _ = (wcCnt x a b N : ℝ) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one, wcCnt]
  have hzero : ∑ n ∈ Finset.filter
      (fun n => ¬(a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)) (Finset.range N),
      wcPhi a b δ (Int.fract (x n)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter] at hn
    rcases lt_or_ge (Int.fract (x n)) a with ha | ha
    · exact Real.intervalCutoff_eq_zero_of_le a b δ _ hδ (le_of_lt ha)
    · have hb : b ≤ Int.fract (x n) := by
        by_contra hcon
        exact hn.2 ⟨ha, not_le.mp hcon⟩
      exact Real.intervalCutoff_eq_zero_of_ge a b δ _ hδ hb
  rw [← hsplit, hzero, add_zero]
  exact h1

private lemma wcPhi_integral_ge (a b δ : ℝ) (ha0 : 0 ≤ a) (_hab : a < b)
    (hb1 : b ≤ 1) (hδ : 0 < δ) (h2 : 2 * δ < b - a) :
    b - a - 2 * δ ≤ ∫ t in (0 : ℝ)..1, wcPhi a b δ t := by
  classical
  have huv : a + δ ≤ b - δ := by linarith
  have h0u : (0 : ℝ) ≤ a + δ := by linarith [ha0, le_of_lt hδ]
  have hv1 : b - δ ≤ 1 := by linarith [hb1, le_of_lt hδ]
  have hcont : Continuous (wcPhi a b δ) := Real.intervalCutoff_continuous _ _ _
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    ((hcont.intervalIntegrable (μ := MeasureTheory.volume)) 0 (a + δ))
    ((hcont.intervalIntegrable (μ := MeasureTheory.volume)) (a + δ) (b - δ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    ((hcont.intervalIntegrable (μ := MeasureTheory.volume)) 0 (b - δ))
    ((hcont.intervalIntegrable (μ := MeasureTheory.volume)) (b - δ) 1)
  have houter1 : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..(a + δ), wcPhi a b δ t := by
    have h := intervalIntegral.integral_mono_on h0u
      ((continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 (a + δ)) :
        IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume 0 (a + δ))
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (a + δ))
      (fun t _ => Real.intervalCutoff_nonneg a b δ t)
    have h0 : (∫ t in (0 : ℝ)..(a + δ), (fun _ : ℝ => (0 : ℝ)) t) = 0 := by
      simp only [intervalIntegral.integral_zero]
    rwa [h0] at h
  have houter2 : (0 : ℝ) ≤ ∫ t in (b - δ)..(1 : ℝ), wcPhi a b δ t := by
    have h := intervalIntegral.integral_mono_on hv1
      ((continuous_const.intervalIntegrable (μ := MeasureTheory.volume) (b - δ) 1) :
        IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume (b - δ) 1)
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) (b - δ) 1)
      (fun t _ => Real.intervalCutoff_nonneg a b δ t)
    have h0 : (∫ t in (b - δ)..(1 : ℝ), (fun _ : ℝ => (0 : ℝ)) t) = 0 := by
      simp only [intervalIntegral.integral_zero]
    rwa [h0] at h
  have hmid : (b - δ) - (a + δ) ≤
      ∫ t in (a + δ)..(b - δ), wcPhi a b δ t := by
    have h := intervalIntegral.integral_mono_on huv
      ((continuous_const.intervalIntegrable (μ := MeasureTheory.volume) (a + δ) (b - δ)) :
        IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume (a + δ)
          (b - δ))
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) (a + δ) (b - δ))
      (fun t ht => by
        rw [Set.mem_Icc] at ht
        exact le_of_eq
          (Real.intervalCutoff_eq_one a b δ t hδ ht.1 ht.2).symm)
    have h1 : (∫ t in (a + δ)..(b - δ), (fun _ : ℝ => (1 : ℝ)) t) =
        (b - δ) - (a + δ) := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    rwa [h1] at h
  have hfinal : b - a - 2 * δ = ((b - δ) - (a + δ)) := by ring
  rw [hfinal]
  linarith [e1, e2, houter1, hmid, houter2]

/-- The bump transferred to the circle as a bundled continuous map. -/
private noncomputable def wcF (a b δ : ℝ) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hδ : 0 < δ) : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨AddCircle.liftIco 1 0 (fun t => ((wcPhi a b δ t : ℝ) : ℂ)), by
    apply AddCircle.liftIco_zero_continuous
    · change ((Real.intervalCutoff a b δ 0 : ℝ) : ℂ) =
        ((Real.intervalCutoff a b δ 1 : ℝ) : ℂ)
      rw [Real.intervalCutoff_eq_zero_of_le a b δ 0 hδ ha0,
        Real.intervalCutoff_eq_zero_of_ge a b δ 1 hδ hb1]
    · exact (Complex.continuous_ofReal.comp
        (Real.intervalCutoff_continuous a b δ)).continuousOn⟩

private lemma wcF_coe (a b δ : ℝ) (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hδ : 0 < δ)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    wcF a b δ ha0 hb1 hδ ((t : ℝ) : AddCircle (1 : ℝ)) =
      ((wcPhi a b δ t : ℝ) : ℂ) := by
  unfold wcF
  rw [ContinuousMap.coe_mk]
  exact AddCircle.liftIco_zero_coe_apply ht

private lemma wcF_fract (a b δ : ℝ) (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hδ : 0 < δ)
    (s : ℝ) :
    wcF a b δ ha0 hb1 hδ ((s : ℝ) : AddCircle (1 : ℝ)) =
      ((wcPhi a b δ (Int.fract s) : ℝ) : ℂ) := by
  have hfloor0 : ((((⌊s⌋ : ℤ)) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff (1 : ℝ)]
    exact ⟨⌊s⌋, by rw [zsmul_eq_mul, mul_one]⟩
  have hs : s = Int.fract s + ((⌊s⌋ : ℤ) : ℝ) := by
    have h1 := Int.fract_add_floor s
    linarith
  conv_lhs => rw [hs]
  rw [AddCircle.coe_add, hfloor0, add_zero]
  exact wcF_coe a b δ ha0 hb1 hδ _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

private lemma wcF_integral (a b δ : ℝ) (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1, wcF a b δ ha0 hb1 hδ ((t : ℝ) : AddCircle (1 : ℝ))) =
      ((∫ t in (0 : ℝ)..1, wcPhi a b δ t : ℝ) : ℂ) := by
  classical
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  have hIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le (by norm_num)
  rw [hIcc]
  intro t ht
  rw [Set.mem_Icc] at ht
  by_cases ht1 : t = 1
  · subst ht1
    have h10 : ((1 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
      have h1 : ((1 : ℝ) : AddCircle (1 : ℝ)) - ((0 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        have hzero : ((((1 : ℤ)) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
          rw [AddCircle.coe_eq_zero_iff (1 : ℝ)]
          exact ⟨1, by rw [zsmul_eq_mul, mul_one]⟩
        have c0 : ((0 : ℝ) : AddCircle (1 : ℝ)) = 0 := AddCircle.coe_zero (1 : ℝ)
        have c1 : ((((1 : ℤ)) : ℝ) : AddCircle (1 : ℝ)) =
            ((1 : ℝ) : AddCircle (1 : ℝ)) := by
          norm_cast
        rw [c0, sub_zero, ← c1]
        exact hzero
      exact sub_eq_zero.mp h1
    change (wcF a b δ ha0 hb1 hδ ((1 : ℝ) : AddCircle (1 : ℝ))) =
      ((wcPhi a b δ 1 : ℝ) : ℂ)
    rw [h10]
    rw [wcF_coe a b δ ha0 hb1 hδ 0 ⟨le_refl _, one_pos⟩]
    change ((Real.intervalCutoff a b δ 0 : ℝ) : ℂ) =
      ((Real.intervalCutoff a b δ 1 : ℝ) : ℂ)
    rw [Real.intervalCutoff_eq_zero_of_le a b δ 0 hδ ha0,
      Real.intervalCutoff_eq_zero_of_ge a b δ 1 hδ hb1]
  · exact wcF_coe a b δ ha0 hb1 hδ t
      ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩

/-- Lower bound for interval frequencies. -/
private lemma wc_lower (x : ℕ → ℝ)
    (hfour : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n))
        atTop (nhds 0))
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, b - a - ε ≤
      ((Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
        (Finset.range N)).card : ℝ) / (N : ℝ) := by
  classical
  set δ := min (ε / 2) ((b - a) / 2) / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    apply div_pos _ (by norm_num)
    exact lt_min (by linarith) (by linarith)
  have h2δ : 2 * δ < b - a := by
    rw [hδdef]
    have h1 : min (ε / 2) ((b - a) / 2) ≤ (b - a) / 2 := min_le_right _ _
    linarith
  have h2δε : 2 * δ ≤ ε / 2 := by
    rw [hδdef]
    have h1 : min (ε / 2) ((b - a) / 2) ≤ ε / 2 := min_le_left _ _
    linarith
  have hF := wc_all_cont x hfour (wcF a b δ ha0 hb1 hδpos)
  rw [wcF_integral a b δ ha0 hb1 hδpos] at hF
  have hR : Tendsto
      (fun N : ℕ => (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
        wcPhi a b δ (Int.fract (x n)))
      atTop (nhds (∫ t in (0 : ℝ)..1, wcPhi a b δ t)) := by
    have hre := (Complex.continuous_re.tendsto _).comp hF
    have elim : Complex.re
        (((∫ t in (0 : ℝ)..1, wcPhi a b δ t : ℝ) : ℂ)) =
        (∫ t in (0 : ℝ)..1, wcPhi a b δ t) := by simp
    rw [elim] at hre
    have efun : ∀ N : ℕ, Complex.re ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        wcF a b δ ha0 hb1 hδpos ((x n : ℝ) : AddCircle (1 : ℝ))) =
        (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
          wcPhi a b δ (Int.fract (x n)) := by
      intro N
      have e1 : (∑ n ∈ Finset.range N,
          wcF a b δ ha0 hb1 hδpos ((x n : ℝ) : AddCircle (1 : ℝ))) =
          (((∑ n ∈ Finset.range N, wcPhi a b δ (Int.fract (x n)) : ℝ)) : ℂ) := by
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl
          (fun n _ => wcF_fract a b δ ha0 hb1 hδpos (x n))
      have e2' : (1 / (N : ℂ)) = (((1 / (N : ℝ)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
      have ere : ∀ z : ℝ, Complex.re (((z : ℝ)) : ℂ) = z := fun z => by simp
      rw [e1, e2', ← Complex.ofReal_mul, ere]
    have efun2 : (Complex.re ∘ (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        wcF a b δ ha0 hb1 hδpos ((x n : ℝ) : AddCircle (1 : ℝ)))) =
        (fun N : ℕ => (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
          wcPhi a b δ (Int.fract (x n))) :=
      funext efun
    rwa [efun2] at hre
  have hL := wcPhi_integral_ge a b δ ha0 hab hb1 hδpos h2δ
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hR) (ε / 2) (by linarith)
  have main : ∀ᶠ N in atTop, b - a - ε ≤ (wcCnt x a b N : ℝ) / (N : ℝ) := by
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
    have hN0 : N ≥ N₀ := le_trans (Nat.le_max_left _ _) hN
    have hNge1 : 1 ≤ N := le_trans (Nat.le_max_right _ _) hN
    have h1 := hN₀ N hN0
    rw [dist_eq_norm, Real.norm_eq_abs] at h1
    have havg_gt : (∫ t in (0 : ℝ)..1, wcPhi a b δ t) - ε / 2 <
        (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
          wcPhi a b δ (Int.fract (x n)) := by
      have h' := (abs_lt.mp h1).1
      linarith
    have hNr : (0 : ℝ) < (N : ℝ) := by
      have hNe : 0 < N := by omega
      exact_mod_cast hNe
    have hle : (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
        wcPhi a b δ (Int.fract (x n)) ≤ (wcCnt x a b N : ℝ) / (N : ℝ) := by
      have hsum := wcPhi_sum_le x a b δ hδpos N
      calc (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
              wcPhi a b δ (Int.fract (x n))
          ≤ (1 / (N : ℝ)) * (wcCnt x a b N : ℝ) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (wcCnt x a b N : ℝ) / (N : ℝ) := by
            conv_rhs => rw [div_eq_mul_one_div]
            exact mul_comm _ _
    linarith [havg_gt, hL, hle, h2δε]
  exact main

/-- Backward direction (Fourier means vanish implies equidistribution). -/
private lemma wc_backward (x : ℕ → ℝ)
    (hfour : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, wcE h (x n))
        atTop (nhds 0))
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1) :
    Tendsto (fun N : ℕ =>
      ((Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
        (Finset.range N)).card : ℝ) / (N : ℝ))
      atTop (nhds (b - a)) := by
  have hsum : ∀ N : ℕ, wcCnt x 0 a N + wcCnt x a b N + wcCnt x b 1 N = N := by
    intro N
    have hpart : Finset.filter
          (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < a)
          (Finset.range N) ∪
        (Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
          (Finset.range N) ∪
          Finset.filter (fun n => b ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
          (Finset.range N)) =
        Finset.range N := by
      ext n
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (⟨hnN, _⟩ | (⟨hnN, _⟩ | ⟨hnN, _⟩))
        · exact hnN
        · exact hnN
        · exact hnN
      · intro hnN
        have hy0 : 0 ≤ Int.fract (x n) := Int.fract_nonneg _
        have hy1 : Int.fract (x n) < 1 := Int.fract_lt_one _
        rcases lt_or_ge (Int.fract (x n)) a with hya | hya
        · exact Or.inl ⟨hnN, hy0, hya⟩
        · rcases lt_or_ge (Int.fract (x n)) b with hyb | hyb
          · exact Or.inr (Or.inl ⟨hnN, hya, hyb⟩)
          · exact Or.inr (Or.inr ⟨hnN, hyb, hy1⟩)
    have hdisj2 : Disjoint
        (Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
          (Finset.range N))
        (Finset.filter (fun n => b ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
          (Finset.range N)) := by
      rw [Finset.disjoint_filter]
      intro n _ h1 h2
      linarith [h1.2, h2.1]
    have hdisj1 : Disjoint
        (Finset.filter
          (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < a)
          (Finset.range N))
        (Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
          (Finset.range N) ∪
          Finset.filter (fun n => b ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
          (Finset.range N)) := by
      rw [Finset.disjoint_union_right]
      constructor
      · rw [Finset.disjoint_filter]
        intro n _ h1 h2
        linarith [h1.2, h2.1]
      · rw [Finset.disjoint_filter]
        intro n _ h1 h2
        linarith [h1.2, h2.1, hab]
    have hcard : (Finset.filter
        (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < a)
        (Finset.range N)).card +
        ((Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
          (Finset.range N)).card +
        (Finset.filter (fun n => b ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
          (Finset.range N)).card) = (Finset.range N).card := by
      have e := congrArg Finset.card hpart
      rwa [Finset.card_union_of_disjoint hdisj1,
        Finset.card_union_of_disjoint hdisj2] at e
    have hcr : (Finset.range N).card = N := Finset.card_range N
    have eL : wcCnt x 0 a N = (Finset.filter
        (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < a)
        (Finset.range N)).card := by rfl
    have eM : wcCnt x a b N = (Finset.filter
        (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
        (Finset.range N)).card := by rfl
    have eR : wcCnt x b 1 N = (Finset.filter
        (fun n => b ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
        (Finset.range N)).card := by rfl
    omega
  have hlow_mid : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      b - a - ε ≤ (wcCnt x a b N : ℝ) / (N : ℝ) :=
    fun ε hε => wc_lower x hfour a b ha0 hab hb1 ε hε
  have hlow_left : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      a - 0 - ε ≤ (wcCnt x 0 a N : ℝ) / (N : ℝ) := by
    intro ε hε
    by_cases ha : 0 < a
    · have ha1 : a ≤ 1 := le_trans (le_of_lt hab) hb1
      exact wc_lower x hfour 0 a le_rfl ha ha1 ε hε
    · have ha0' : a = 0 := le_antisymm (not_lt.mp ha) ha0
      filter_upwards with N
      have hzero : wcCnt x 0 0 N = 0 := by
        have hemp : Finset.filter
            (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 0)
            (Finset.range N) = ∅ := by
          apply Finset.filter_false_of_mem
          intro n _ hn
          linarith [hn.1, hn.2]
        have e : wcCnt x 0 0 N = (Finset.filter
            (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 0)
            (Finset.range N)).card := by rfl
        rw [e, hemp, Finset.card_empty]
      rw [ha0', hzero]
      simp only [Nat.cast_zero, zero_div, sub_zero, zero_sub]
      exact neg_nonpos.mpr (le_of_lt hε)
  have hlow_right : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      1 - b - ε ≤ (wcCnt x b 1 N : ℝ) / (N : ℝ) := by
    intro ε hε
    by_cases hb : b < 1
    · have hb0 : 0 ≤ b := le_trans ha0 (le_of_lt hab)
      exact wc_lower x hfour b 1 hb0 hb le_rfl ε hε
    · have hb1' : b = 1 := le_antisymm hb1 (not_lt.mp hb)
      filter_upwards with N
      have hzero : wcCnt x 1 1 N = 0 := by
        have hemp : Finset.filter
            (fun n => (1 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
            (Finset.range N) = ∅ := by
          apply Finset.filter_false_of_mem
          intro n _ hn
          linarith [hn.1, hn.2]
        have e : wcCnt x 1 1 N = (Finset.filter
            (fun n => (1 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)
            (Finset.range N)).card := by rfl
        rw [e, hemp, Finset.card_empty]
      rw [hb1', hzero]
      simp only [Nat.cast_zero, zero_div, sub_self, zero_sub]
      exact neg_nonpos.mpr (le_of_lt hε)
  have hdiv : ∀ N : ℕ, 1 ≤ N →
      (wcCnt x a b N : ℝ) / (N : ℝ) =
        1 - (wcCnt x 0 a N : ℝ) / (N : ℝ) - (wcCnt x b 1 N : ℝ) / (N : ℝ) := by
    intro N hN
    have hNr : (N : ℝ) ≠ 0 := by
      have hNe : N ≠ 0 := by omega
      exact_mod_cast hNe
    have hsumR : (wcCnt x 0 a N : ℝ) + (wcCnt x a b N : ℝ) +
        (wcCnt x b 1 N : ℝ) = (N : ℝ) := by
      exact_mod_cast hsum N
    have e : (wcCnt x a b N : ℝ) / (N : ℝ) =
        ((N : ℝ) - (wcCnt x 0 a N : ℝ) - (wcCnt x b 1 N : ℝ)) / (N : ℝ) := by
      congr 1
      linarith [hsumR]
    rw [e, sub_div, sub_div, div_self hNr]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlo_mid := hlow_mid (ε / 3) (by linarith)
  have hlo_L := hlow_left (ε / 3) (by linarith)
  have hlo_R := hlow_right (ε / 3) (by linarith)
  have hev := hlo_mid.and (hlo_L.and (hlo_R.and (eventually_ge_atTop 1)))
  rw [eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hmid, hL, hR, hN1⟩ := hN₀ N hN
  have hN : 1 ≤ N := hN1
  have hup : (wcCnt x a b N : ℝ) / (N : ℝ) ≤ b - a + 2 * (ε / 3) := by
    rw [hdiv N hN]
    linarith [hL, hR]
  change dist ((wcCnt x a b N : ℝ) / (N : ℝ)) (b - a) < ε
  rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
  constructor
  · linarith [hmid]
  · linarith [hup]

/-- Weyl's equidistribution criterion (statement `weyl-criterion-s1`):
a real sequence `x` is equidistributed mod 1 iff every nontrivial Fourier mean
vanishes. Source: https://en.wikipedia.org/wiki/Equidistribution_theorem.

Proves `Wanted` entry `weyl_criterion`. -/
public theorem weyl_criterion (x : ℕ → ℝ) :
    (∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      Tendsto (fun N : ℕ =>
        ((Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
          (Finset.range N)).card : ℝ) / (N : ℝ))
        atTop (nhds (b - a)))
    ↔ ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ =>
        (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          Complex.exp (((2 * Real.pi * (h : ℝ) * x n : ℝ) : ℂ) * Complex.I))
        atTop (nhds 0) := by
  constructor
  · intro heq h hh
    exact wc_forward x heq h hh
  · intro hfour a b ha0 hab hb1
    exact wc_backward x hfour a b ha0 hab hb1

end MetaMathlibExt
