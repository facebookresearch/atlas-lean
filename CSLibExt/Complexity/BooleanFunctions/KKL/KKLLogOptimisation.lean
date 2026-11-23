/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLLogSobolev

/-!
# The edge-isoperimetric inequality and the logarithmic KKL reduction

For an event of uniform measure `m` on `{0, 1}^ι`, combining the indicator hypercontractive
bound with `1 - x^k ≤ k (1 - x)` gives `m - m^{2/(1+ρ²)} ≤ (1 - ρ²) · I / 4`, where `I` is the
total influence. Letting `ρ → 1` yields the edge-isoperimetric inequality
`2 m log (1 / m) ≤ I`. The same bound reduces the predicate `kls_LogOptimisation` to
`klo_DeltaUpgrade`.

## Main definitions

* `StatMech.Probability.klo_DeltaUpgrade`: the KKL inequality at `p = 1/2` in Fourier form,
  with the bound `m - m^{2/(1+ρ²)} ≤ (1 - ρ²) I / 4` as a hypothesis.

## Main results

* `StatMech.Probability.klo_master_le`: `m - m^{2/(1+ρ²)} ≤ (1 - ρ²) I / 4`.
* `StatMech.Probability.klo_edge_isoperimetric`: `2 m log (1 / m) ≤ I`.
* `StatMech.Probability.klo_logOptimisation`: `klo_DeltaUpgrade c` implies
  `KKLHypercontractive (1/2) c`.

## References

* S. Hart, *A note on the edges of the n-cube*, Discrete Math. 14 (1976).
-/

@[expose] public section

open scoped BigOperators
open Finset
open Real Filter Topology

namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem klo_indicator_sq (φ : ConfigSpace ι → Bool) (ω : ConfigSpace ι) :
    ((fun ω => if φ ω then (1 : ℝ) else 0) ω) ^ 2
      = (fun ω => if φ ω then (1 : ℝ) else 0) ω := by
  by_cases h : φ ω <;> simp [h]

theorem klo_uexp_sq_eq_mean (φ : ConfigSpace ι → Bool) :
    bnt_uexp (fun x => ((fun ω => if φ ω then (1 : ℝ) else 0) x) ^ 2)
      = bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) := by
  congr 1; funext ω; exact klo_indicator_sq φ ω

theorem klo_var_eq (φ : ConfigSpace ι → Bool) :
    (∑ S ∈ (univ.erase (∅ : Finset ι)),
        (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      = bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)
        - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set m := bnt_uexp f with hm
  have hpars : bnt_uexp (fun x => (f x) ^ 2) = ∑ S : Finset ι, (khc_fourierCoeff f S) ^ 2 :=
    khc_parseval_sq f
  rw [klo_uexp_sq_eq_mean φ] at hpars
  have hempty : khc_fourierCoeff f ∅ = m := (khc_uexp_eq_coeff_empty f).symm
  have hsplit : (∑ S : Finset ι, (khc_fourierCoeff f S) ^ 2)
      = (khc_fourierCoeff f ∅) ^ 2
        + ∑ S ∈ (univ.erase (∅ : Finset ι)), (khc_fourierCoeff f S) ^ 2 :=
    (Finset.add_sum_erase univ (fun S => (khc_fourierCoeff f S) ^ 2) (Finset.mem_univ ∅)).symm
  rw [hsplit, hempty] at hpars
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Bernoulli's inequality in the form `1 - x^k ≤ k (1 - x)` for `0 ≤ x` (the hypothesis
`x ≤ 1` is not needed). See also `one_add_mul_le_pow`. -/
theorem klo_one_sub_pow_le (x : ℝ) (h0 : 0 ≤ x) (_h1 : x ≤ 1) (k : ℕ) :
    1 - x ^ k ≤ (1 - x) * k := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ x - 1 by linarith) k
  rw [add_sub_cancel] at h
  linarith

omit [Fintype ι] [DecidableEq ι] in
theorem klo_one_sub_rhopow (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (k : ℕ) :
    1 - (ρ ^ k) ^ 2 ≤ (1 - ρ ^ 2) * k := by
  rw [← pow_mul, mul_comm, pow_mul]
  exact klo_one_sub_pow_le (ρ ^ 2) (sq_nonneg _) (by nlinarith) k

theorem klo_var_sub_damped_le (φ : ConfigSpace ι → Bool) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    (∑ S ∈ (univ.erase (∅ : Finset ι)),
        (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      - (∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (1 - ρ ^ 2) * (∑ S : Finset ι, 4 * (S.card : ℝ)
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) / 4 := by
  set c := fun S : Finset ι =>
      (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  have hcnn : ∀ S, 0 ≤ c S := fun S => sq_nonneg _
  rw [← Finset.sum_sub_distrib]
  have step1 : (∑ S ∈ (univ.erase (∅ : Finset ι)), (c S - (ρ ^ S.card) ^ 2 * c S))
      ≤ ∑ S ∈ (univ.erase (∅ : Finset ι)), (1 - ρ ^ 2) * (S.card : ℝ) * c S := by
    apply Finset.sum_le_sum
    intro S _
    have hpow := klo_one_sub_rhopow ρ h0 h1 S.card
    nlinarith [hcnn S, hpow]
  refine step1.trans ?_
  have hsub : (∑ S ∈ (univ.erase (∅ : Finset ι)), (1 - ρ ^ 2) * (S.card : ℝ) * c S)
      ≤ ∑ S : Finset ι, (1 - ρ ^ 2) * (S.card : ℝ) * c S := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    intro S _ _
    have : 0 ≤ 1 - ρ ^ 2 := by nlinarith
    positivity
  refine hsub.trans ?_
  rw [Finset.mul_sum, Finset.sum_div]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro S _; ring

/-- For an event of uniform measure `m` and total influence `I = ∑_S 4 |S| f̂(S)²`, `m -
  m^{2/(1+ρ²)} ≤ (1 - ρ²) I / 4` for `0 ≤ ρ ≤ 1`. -/
theorem klo_master_le (φ : ConfigSpace ι → Bool) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)
        - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2))
      ≤ (1 - ρ ^ 2) * (∑ S : Finset ι, 4 * (S.card : ℝ)
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) / 4 := by
  have Hfluct := kls_fluctWeight_le_pow h0 h1 φ
  have Hvar := klo_var_eq (ι := ι) φ
  have Hsub := klo_var_sub_damped_le φ ρ h0 h1
  rw [Hvar] at Hsub
  linarith [Hfluct, Hsub]

theorem klo_master_sub (φ : ConfigSpace ι → Bool) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)
        - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (1 / (1 - u / 2))
      ≤ u * ((∑ S : Finset ι, 4 * (S.card : ℝ)
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) / 4) := by
  have hu1' : (1 : ℝ) - u ≥ 0 := by linarith
  set ρ := Real.sqrt (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hρsq : ρ ^ 2 = 1 - u := Real.sq_sqrt hu1'
  have H := klo_master_le φ ρ hρ0 hρ1
  rw [hρsq] at H
  have he1 : (2 : ℝ) / (1 + (1 - u)) = 1 / (1 - u / 2) := by
    rw [div_eq_div_iff (by linarith) (by intro h; linarith [h])]; ring
  have he2 : (1 : ℝ) - (1 - u) = u := by ring
  rw [he1, he2] at H
  linarith

/-- **Edge-isoperimetric inequality** on the discrete cube (S. Hart, *A note on the edges of the
  n-cube*, Discrete Math. 1976): an event of uniform measure `m > 0` has total influence at least
  `2 m log (1 / m)`. Here `log` is the natural logarithm, so this is weaker by the factor `log 2`
  than the sharp bound `2 m log₂ (1 / m)`. -/
theorem klo_edge_isoperimetric (φ : ConfigSpace ι → Bool)
    (hm0 : 0 < bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) :
    2 * bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ ∑ S : Finset ι, 4 * (S.card : ℝ)
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  set m := bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) with hm
  set W := ∑ S : Finset ι, 4 * (S.card : ℝ)
      * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hW
  have Hg : ∀ u : ℝ, 0 < u → u ≤ 1 → m - m ^ (1 / (1 - u / 2)) ≤ u * (W / 4) :=
    fun u hu0 hu1 => klo_master_sub φ u hu0 hu1
  have hd : HasDerivAt (fun u : ℝ => m ^ (1 / (1 - u / 2))) (m * Real.log m / 2) 0 := by
    have hrw : (fun u : ℝ => m ^ (1 / (1 - u / 2)))
        = (fun u => Real.exp (Real.log m * (1 / (1 - u / 2)))) := by
      funext u; rw [Real.rpow_def_of_pos hm0, mul_comm]
    rw [hrw]
    have hden : HasDerivAt (fun u : ℝ => 1 - u / 2) (-(1 / 2)) (0 : ℝ) := by
      have : HasDerivAt (fun u : ℝ => 1 - u / 2) (0 - 1 / 2) (0 : ℝ) :=
        HasDerivAt.sub (hasDerivAt_const _ _)
          (by simpa using (hasDerivAt_id (0 : ℝ)).div_const 2)
      simpa using this
    have hinv : HasDerivAt (fun u : ℝ => 1 / (1 - u / 2)) (1 / 2) (0 : ℝ) := by
      have := hden.inv (by norm_num)
      simp only [one_div]; convert this using 1; norm_num
    have hphi : HasDerivAt (fun u : ℝ => Real.log m * (1 / (1 - u / 2)))
        (Real.log m * (1 / 2)) (0 : ℝ) := hinv.const_mul (Real.log m)
    have hexp := (Real.hasDerivAt_exp (Real.log m * (1 / ((1 : ℝ) - 0 / 2)))).comp 0 hphi
    simp only [sub_zero, zero_div, mul_one, div_one] at hexp ⊢
    rw [Real.exp_log hm0] at hexp
    convert hexp using 1
    all_goals first | rfl | ring
  have hlim : Filter.Tendsto (fun u : ℝ => (m - m ^ (1 / (1 - u / 2))) / u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(m * Real.log m / 2))) := by
    have hslope := hd.tendsto_slope
    have hh0 : (fun u : ℝ => m ^ (1 / (1 - u / 2))) 0 = m := by norm_num
    have hsub : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin (0 : ℝ) {0}ᶜ := by
      apply nhdsWithin_mono; intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢; exact ne_of_gt hx
    have hslope2 := hslope.mono_left hsub
    have hrw : (fun u => (m - m ^ (1 / (1 - u / 2))) / u)
        = (fun u => -(slope (fun u : ℝ => m ^ (1 / (1 - u / 2))) 0 u)) := by
      funext u; rw [slope_def_field]; simp only [hh0, sub_zero]; rw [← neg_div, neg_sub]
    rw [hrw]; exact hslope2.neg
  have hL : -(m * Real.log m / 2) ≤ W / 4 := by
    have hev : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (m - m ^ (1 / (1 - u / 2))) / u ≤ W / 4 := by
      filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
      obtain ⟨hu0, huU⟩ := hu
      rw [div_le_iff₀ hu0, mul_comm]; exact Hg u hu0 huU
    exact le_of_tendsto hlim hev
  rw [Real.log_div (by norm_num) (ne_of_gt hm0), Real.log_one, zero_sub]
  nlinarith [hL]

/-- The KKL inequality at `p = 1/2` in Fourier form, with the bound `m - m^{2/(1+ρ²)} ≤ (1 - ρ²) I /
  4` (for all `ρ ∈ [0, 1]`) as a hypothesis, where `m` is the measure and `I` the total influence
  of `φ`. The hypothesis always holds (`klo_master_le`). -/
def klo_DeltaUpgrade (c : ℝ) : Prop :=
  ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool),
    (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
        bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)
            - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2))
          ≤ (1 - ρ ^ 2) * (∑ S : Finset E, 4 * (S.card : ℝ)
              * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) / 4) →
      c * (∑ S ∈ (univ.erase (∅ : Finset E)),
            (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if φ ω then (1 : ℝ) else 0))
        ≤ ∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2

/-- `klo_DeltaUpgrade 0` holds trivially. -/
theorem klo_deltaUpgrade_zero : klo_DeltaUpgrade 0 := by
  intro E _ _ _ φ _
  rw [zero_mul, zero_mul]
  exact kls_W_nonneg φ

/-- `klo_DeltaUpgrade c` implies `kls_LogOptimisation c`. -/
theorem klo_logOptimisation_of_deltaUpgrade {c : ℝ} (H : klo_DeltaUpgrade c) :
    kls_LogOptimisation c := by
  intro E _ _ _ φ _hfluct
  exact H φ (fun ρ h0 h1 => klo_master_le φ ρ h0 h1)

/-- `klo_DeltaUpgrade c` implies the KKL inequality `KKLHypercontractive (1/2) c`. -/
theorem klo_logOptimisation {c : ℝ} (H : klo_DeltaUpgrade c) :
    KKLHypercontractive (1 / 2 : ℝ) c :=
  kls_logSobolevStep (klo_logOptimisation_of_deltaUpgrade H)

end StatMech.Probability
