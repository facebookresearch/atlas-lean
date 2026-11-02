/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Corollary to Entry 5

Series for (1/2)log 3+(1/3)log 4-1 via 2/(216n³-6n).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry5Corollary

private noncomputable def auxHR (m : ℕ) : ℝ := ∑ k ∈ Finset.range m, (1 : ℝ) / ((k : ℝ) + 1)

private lemma auxHR_add (m d : ℕ) :
    auxHR (m + d) = auxHR m + ∑ i ∈ Finset.range d, (1 : ℝ) / (((m + i : ℕ) : ℝ) + 1) := by
  unfold auxHR
  rw [Finset.sum_range_add]

private lemma auxExpand6 (N : ℕ) :
    ∑ i ∈ Finset.range 6, (1 : ℝ) / (((6 * N + 1 + i : ℕ) : ℝ) + 1)
    = 1 / (6 * (N : ℝ) + 2) + 1 / (6 * (N : ℝ) + 3) + 1 / (6 * (N : ℝ) + 4)
      + 1 / (6 * (N : ℝ) + 5) + 1 / (6 * (N : ℝ) + 6) + 1 / (6 * (N : ℝ) + 7) := by
  simp [Finset.sum_range_succ]
  ring

private lemma auxExpand3 (N : ℕ) :
    ∑ i ∈ Finset.range 3, (1 : ℝ) / (((3 * N + i : ℕ) : ℝ) + 1)
    = 1 / (3 * (N : ℝ) + 1) + 1 / (3 * (N : ℝ) + 2) + 1 / (3 * (N : ℝ) + 3) := by
  simp [Finset.sum_range_succ]
  ring

private lemma auxExpand2 (N : ℕ) :
    ∑ i ∈ Finset.range 2, (1 : ℝ) / (((2 * N + i : ℕ) : ℝ) + 1)
    = 1 / (2 * (N : ℝ) + 1) + 1 / (2 * (N : ℝ) + 2) := by
  simp [Finset.sum_range_succ]
  ring

private lemma auxExpand1 (N : ℕ) :
    ∑ i ∈ Finset.range 1, (1 : ℝ) / (((N + i : ℕ) : ℝ) + 1)
    = 1 / ((N : ℝ) + 1) := by
  simp

private lemma auxStep (N : ℕ) :
    (2 : ℝ) / ((6 * ((N : ℝ) + 1)) ^ 3 - 6 * ((N : ℝ) + 1))
    = (1 / (6 * (N : ℝ) + 2) + 1 / (6 * (N : ℝ) + 3) + 1 / (6 * (N : ℝ) + 4)
      + 1 / (6 * (N : ℝ) + 5) + 1 / (6 * (N : ℝ) + 6) + 1 / (6 * (N : ℝ) + 7))
      - (1 / 2) * (1 / (3 * (N : ℝ) + 1) + 1 / (3 * (N : ℝ) + 2) + 1 / (3 * (N : ℝ) + 3))
      - (1 / 3) * (1 / (2 * (N : ℝ) + 1) + 1 / (2 * (N : ℝ) + 2))
      - (1 / 6) * (1 / ((N : ℝ) + 1)) := by
  have xnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have d1 : (6 : ℝ) * (N : ℝ) + 2 ≠ 0 := by positivity
  have d2 : (6 : ℝ) * (N : ℝ) + 3 ≠ 0 := by positivity
  have d3 : (6 : ℝ) * (N : ℝ) + 4 ≠ 0 := by positivity
  have d4 : (6 : ℝ) * (N : ℝ) + 5 ≠ 0 := by positivity
  have d5 : (6 : ℝ) * (N : ℝ) + 6 ≠ 0 := by positivity
  have d6 : (6 : ℝ) * (N : ℝ) + 7 ≠ 0 := by positivity
  have e1 : (3 : ℝ) * (N : ℝ) + 1 ≠ 0 := by positivity
  have e2 : (3 : ℝ) * (N : ℝ) + 2 ≠ 0 := by positivity
  have e3 : (3 : ℝ) * (N : ℝ) + 3 ≠ 0 := by positivity
  have g1 : (2 : ℝ) * (N : ℝ) + 1 ≠ 0 := by positivity
  have g2 : (2 : ℝ) * (N : ℝ) + 2 ≠ 0 := by positivity
  have hN : (N : ℝ) + 1 ≠ 0 := by positivity
  have h6M : (0 : ℝ) < 6 * ((N : ℝ) + 1) := by positivity
  have ha : (0 : ℝ) < 6 * ((N : ℝ) + 1) - 1 := by
    have hle : (6 : ℝ) ≤ 6 * ((N : ℝ) + 1) := by nlinarith [xnn]
    linarith
  have hb : (0 : ℝ) < 6 * ((N : ℝ) + 1) + 1 := by positivity
  have hD1 : (6 : ℝ) * ((N : ℝ) + 1) ≠ 0 := ne_of_gt h6M
  have hD2 : (6 : ℝ) * ((N : ℝ) + 1) - 1 ≠ 0 := ne_of_gt ha
  have hD3 : (6 : ℝ) * ((N : ℝ) + 1) + 1 ≠ 0 := ne_of_gt hb
  have hfac : ((6 : ℝ) * ((N : ℝ) + 1)) ^ 3 - 6 * ((N : ℝ) + 1)
      = (6 * ((N : ℝ) + 1)) * (6 * ((N : ℝ) + 1) - 1) * (6 * ((N : ℝ) + 1) + 1) := by ring
  rw [hfac]
  field_simp
  ring

private lemma auxKey : ∀ N : ℕ,
    ∑ j ∈ Finset.range N, (2 : ℝ) / ((6 * ((j : ℝ) + 1)) ^ 3 - 6 * ((j : ℝ) + 1))
    = auxHR (6 * N + 1) - (1 / 2) * auxHR (3 * N) - (1 / 3) * auxHR (2 * N)
      - (1 / 6) * auxHR N - 1 := by
  intro N
  induction N with
  | zero =>
    simp [auxHR]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h6 : 6 * (N + 1) + 1 = (6 * N + 1) + 6 := by ring
    have h3 : 3 * (N + 1) = (3 * N) + 3 := by ring
    have h2 : 2 * (N + 1) = (2 * N) + 2 := by ring
    have e6 := auxHR_add (6 * N + 1) 6
    have e3 := auxHR_add (3 * N) 3
    have e2 := auxHR_add (2 * N) 2
    have e1 := auxHR_add N 1
    rw [h6, h3, h2, e6, e3, e2, e1, auxExpand6, auxExpand3, auxExpand2, auxExpand1, auxStep]
    ring

private lemma auxHReq (m : ℕ) : auxHR m = ((harmonic m : ℚ) : ℝ) := by
  induction m with
  | zero => simp [auxHR, harmonic_zero]
  | succ n ih =>
    have h1 : auxHR (n + 1) = auxHR n + 1 / ((n : ℝ) + 1) := by
      unfold auxHR
      rw [Finset.sum_range_succ]
    have h2 : ((harmonic (n + 1) : ℚ) : ℝ) = ((harmonic n : ℚ) : ℝ) + 1 / ((n : ℝ) + 1) := by
      rw [harmonic_succ]
      push_cast
      ring
    rw [h1, h2, ih]

private lemma auxSm6 : StrictMono (fun N : ℕ => 6 * N + 1) := by
  intro a b hab
  simp only
  omega

private lemma auxSm3 : StrictMono (fun N : ℕ => 3 * N) := by
  intro a b hab
  simp only
  omega

private lemma auxSm2 : StrictMono (fun N : ℕ => 2 * N) := by
  intro a b hab
  simp only
  omega

private lemma auxLim1 : Filter.Tendsto (fun N : ℕ => auxHR N - Real.log ((N : ℕ) : ℝ))
    Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  simp only [auxHReq]
  exact Real.tendsto_harmonic_sub_log

private lemma auxLim6 : Filter.Tendsto (fun N : ℕ => auxHR (6 * N + 1) - Real.log ((6 * N + 1 : ℕ) : ℝ))
    Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have hcomp := Real.tendsto_harmonic_sub_log.comp auxSm6.tendsto_atTop
  simp only [Function.comp_def] at hcomp
  simp only [← auxHReq] at hcomp
  exact hcomp

private lemma auxLim3 : Filter.Tendsto (fun N : ℕ => auxHR (3 * N) - Real.log ((3 * N : ℕ) : ℝ))
    Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have hcomp := Real.tendsto_harmonic_sub_log.comp auxSm3.tendsto_atTop
  simp only [Function.comp_def] at hcomp
  simp only [← auxHReq] at hcomp
  exact hcomp

private lemma auxLim2 : Filter.Tendsto (fun N : ℕ => auxHR (2 * N) - Real.log ((2 * N : ℕ) : ℝ))
    Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have hcomp := Real.tendsto_harmonic_sub_log.comp auxSm2.tendsto_atTop
  simp only [Function.comp_def] at hcomp
  simp only [← auxHReq] at hcomp
  exact hcomp

private lemma auxLimE : Filter.Tendsto
    (fun N : ℕ => (auxHR (6 * N + 1) - Real.log ((6 * N + 1 : ℕ) : ℝ))
      - (1 / 2) * (auxHR (3 * N) - Real.log ((3 * N : ℕ) : ℝ))
      - (1 / 3) * (auxHR (2 * N) - Real.log ((2 * N : ℕ) : ℝ))
      - (1 / 6) * (auxHR N - Real.log ((N : ℕ) : ℝ)))
    Filter.atTop (nhds 0) := by
  have h := Filter.Tendsto.sub
    (Filter.Tendsto.sub
      (Filter.Tendsto.sub auxLim6 (Filter.Tendsto.const_mul (1 / 2 : ℝ) auxLim3))
      (Filter.Tendsto.const_mul (1 / 3 : ℝ) auxLim2))
    (Filter.Tendsto.const_mul (1 / 6 : ℝ) auxLim1)
  have hv : Real.eulerMascheroniConstant - (1 / 2) * Real.eulerMascheroniConstant
      - (1 / 3) * Real.eulerMascheroniConstant - (1 / 6) * Real.eulerMascheroniConstant
      = (0 : ℝ) := by ring
  rwa [hv] at h

private lemma auxLog61 : (fun N : ℕ => Real.log ((6 * N + 1 : ℕ) : ℝ))
    =ᶠ[Filter.atTop] (fun N : ℕ => Real.log (N : ℝ) + Real.log (6 + 1 / (N : ℝ))) := by
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  have Nne : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hNpos
  have h61 : ((6 * N + 1 : ℕ) : ℝ) = (N : ℝ) * (6 + 1 / (N : ℝ)) := by
    push_cast
    field_simp
  rw [h61, Real.log_mul Nne (by positivity)]

private lemma auxLog3 : (fun N : ℕ => Real.log ((3 * N : ℕ) : ℝ))
    =ᶠ[Filter.atTop] (fun N : ℕ => Real.log 3 + Real.log (N : ℝ)) := by
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  have Nne : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hNpos
  have h : ((3 * N : ℕ) : ℝ) = 3 * (N : ℝ) := by push_cast; ring
  rw [h, Real.log_mul (by norm_num) Nne]

private lemma auxLog2 : (fun N : ℕ => Real.log ((2 * N : ℕ) : ℝ))
    =ᶠ[Filter.atTop] (fun N : ℕ => Real.log 2 + Real.log (N : ℝ)) := by
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  have Nne : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hNpos
  have h : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  rw [h, Real.log_mul (by norm_num) Nne]

private lemma auxLev : (fun N : ℕ => Real.log ((6 * N + 1 : ℕ) : ℝ)
      - (1 / 2) * Real.log ((3 * N : ℕ) : ℝ)
      - (1 / 3) * Real.log ((2 * N : ℕ) : ℝ)
      - (1 / 6) * Real.log ((N : ℕ) : ℝ))
    =ᶠ[Filter.atTop]
    (fun N : ℕ => Real.log (6 + 1 / (N : ℝ)) - (1 / 2) * Real.log 3 - (1 / 3) * Real.log 2) := by
  filter_upwards [auxLog61, auxLog3, auxLog2] with N h61 h3 h2
  rw [h61, h3, h2]
  ring

private lemma auxSixPlus : Filter.Tendsto (fun N : ℕ => (6 : ℝ) + 1 / (N : ℝ))
    Filter.atTop (nhds 6) := by
  have h := Filter.Tendsto.add
    (tendsto_const_nhds (x := (6 : ℝ)) (f := (Filter.atTop : Filter ℕ)))
    tendsto_one_div_atTop_nhds_zero_nat
  simpa [add_comm] using h

private lemma auxLimL : Filter.Tendsto
    (fun N : ℕ => Real.log ((6 * N + 1 : ℕ) : ℝ)
      - (1 / 2) * Real.log ((3 * N : ℕ) : ℝ)
      - (1 / 3) * Real.log ((2 * N : ℕ) : ℝ)
      - (1 / 6) * Real.log ((N : ℕ) : ℝ))
    Filter.atTop (nhds (Real.log 6 - (1 / 2) * Real.log 3 - (1 / 3) * Real.log 2)) := by
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (6 + 1 / (N : ℝ)))
      Filter.atTop (nhds (Real.log 6)) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp auxSixPlus
  have hRHS : Filter.Tendsto
      (fun N : ℕ => Real.log (6 + 1 / (N : ℝ)) - (1 / 2) * Real.log 3 - (1 / 3) * Real.log 2)
      Filter.atTop (nhds (Real.log 6 - (1 / 2) * Real.log 3 - (1 / 3) * Real.log 2)) :=
    Filter.Tendsto.sub
      (Filter.Tendsto.sub hlog (tendsto_const_nhds (x := ((1 / 2 : ℝ) * Real.log 3)) (f := (Filter.atTop : Filter ℕ))))
      (tendsto_const_nhds (x := ((1 / 3 : ℝ) * Real.log 2)) (f := (Filter.atTop : Filter ℕ)))
  exact Filter.Tendsto.congr' auxLev.symm hRHS

private lemma auxNonneg (j : ℕ) :
    0 ≤ (2 : ℝ) / ((6 * ((j : ℝ) + 1)) ^ 3 - 6 * ((j : ℝ) + 1)) := by
  have hpos : (0 : ℝ) < 6 * ((j : ℝ) + 1) := by positivity
  have ha : (0 : ℝ) < 6 * ((j : ℝ) + 1) - 1 := by
    have hle : (6 : ℝ) ≤ 6 * ((j : ℝ) + 1) := by
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  have hb : (0 : ℝ) < 6 * ((j : ℝ) + 1) + 1 := by positivity
  have hfac : ((6 : ℝ) * ((j : ℝ) + 1)) ^ 3 - 6 * ((j : ℝ) + 1)
      = (6 * ((j : ℝ) + 1)) * (6 * ((j : ℝ) + 1) - 1) * (6 * ((j : ℝ) + 1) + 1) := by ring
  rw [hfac]
  exact div_nonneg (by norm_num) (le_of_lt (mul_pos (mul_pos hpos ha) hb))

private lemma auxTendsto : Filter.Tendsto
    (fun N : ℕ => ∑ j ∈ Finset.range N, (2 : ℝ) / ((6 * ((j : ℝ) + 1)) ^ 3 - 6 * ((j : ℝ) + 1)))
    Filter.atTop (nhds (1 / 2 * Real.log 3 + 1 / 3 * Real.log 4 - 1)) := by
  have hdecomp : (fun N : ℕ => ∑ j ∈ Finset.range N,
        (2 : ℝ) / ((6 * ((j : ℝ) + 1)) ^ 3 - 6 * ((j : ℝ) + 1)))
      = (fun N : ℕ => ((auxHR (6 * N + 1) - Real.log ((6 * N + 1 : ℕ) : ℝ))
          - (1 / 2) * (auxHR (3 * N) - Real.log ((3 * N : ℕ) : ℝ))
          - (1 / 3) * (auxHR (2 * N) - Real.log ((2 * N : ℕ) : ℝ))
          - (1 / 6) * (auxHR N - Real.log ((N : ℕ) : ℝ)))
        + (Real.log ((6 * N + 1 : ℕ) : ℝ)
          - (1 / 2) * Real.log ((3 * N : ℕ) : ℝ)
          - (1 / 3) * Real.log ((2 * N : ℕ) : ℝ)
          - (1 / 6) * Real.log ((N : ℕ) : ℝ)) - 1) := by
    funext N
    rw [auxKey N]
    ring
  rw [hdecomp]
  have hlim := Filter.Tendsto.add auxLimE auxLimL
  have hlim2 := Filter.Tendsto.sub hlim
    (tendsto_const_nhds (x := (1 : ℝ)) (f := (Filter.atTop : Filter ℕ)))
  have hval : (0 : ℝ) + (Real.log 6 - (1 / 2) * Real.log 3 - (1 / 3) * Real.log 2) - 1
      = 1 / 2 * Real.log 3 + 1 / 3 * Real.log 4 - 1 := by
    have h6 : (6 : ℝ) = 2 * 3 := by norm_num
    have h4 : (4 : ℝ) = 2 * 2 := by norm_num
    rw [h6, h4, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rwa [hval] at hlim2

/-- **Ramanujan's series for $\frac{1}{2}\log 3 + \frac{1}{3}\log 4 - 1$.** The numbers
$\frac{2}{(6k)^3 - 6k}$ for $k = 1, 2, 3, \dots$ are summable with sum
$\frac{1}{2}\log 3 + \frac{1}{3}\log 4 - 1$, where $\log$ is the natural logarithm.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2,
    corollary to Entry 5, printed p. 30 / PDF p. 40.
Proves `Wanted` entry `ramanujan_part1_ch2_entry5_corollary`.
-/
theorem ramanujan_part1_ch2_entry5_corollary :
    HasSum (fun j : ℕ => (2 : ℝ) / ((6 * (↑j + 1)) ^ 3 - 6 * (↑j + 1)))
        (1 / 2 * Real.log 3 + 1 / 3 * Real.log 4 - 1) := by
  exact (hasSum_iff_tendsto_nat_of_nonneg auxNonneg _).mpr auxTendsto

end Entry5Corollary

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
