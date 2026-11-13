/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SFSGrowth
public import MathlibExtTest.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Tests for the site frequency spectrum under exponential growth

Values of the intensity `R`, the time change `G` and the growth holding times computed from
the definitions (constant size, a growth rate `ρ = 1`, the junk value of `G` outside its
domain, the empty genealogy `n = 1`), the strict shortening of an epoch at concrete numbers,
satisfiability of the strict-monotonicity hypotheses, and a non-vacuity witness for the
growth spectrum theorems: sample size `2`, the product model of the Kingman holding times and
the constant topology from the `SiteFrequencySpectrum` tests, `ρ = 1`, and `ξ i` equal to its
conditional mean. On the witness `E ξ₁` is computed once directly from the definitions and
once through `integral_sfs_growth`; the two agree, and the result is `θ c₂ < θ`. A `θ = 0`
version of the witness satisfies `sfsCondMoments_growth` and exercises
`covariance_count_growth`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSGrowth

open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
open MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSGrowth
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSCovariance
open MathlibExtTest.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

/-! ### The intensity and the time change, from the definitions -/

/-- `ρ = 1`: `R(1) = ∫_0^1 e^r dr = e - 1`, computed directly from `cumRate`. -/
example : cumRate (expGrowthSize 1) 1 = Real.exp 1 - 1 := by
  simp only [cumRate, expGrowthSize, one_mul, ← Real.exp_neg, neg_neg, integral_exp,
    Real.exp_zero]

/-- Constant size (`ρ = 0`): `R(s) = s`. -/
example (s : ℝ) : cumRate (expGrowthSize 0) s = s := by
  simp [cumRate, expGrowthSize]

/-- `ρ = 1`: `G(e - 1) = log e = 1`, so `G` undoes the intensity computed above. -/
example : growthTime 1 (Real.exp 1 - 1) = 1 := by
  simp [growthTime]

/-- Boundary: `G(0) = 0` and, without growth, `G = id`. -/
example (ρ u : ℝ) : growthTime ρ 0 = 0 ∧ growthTime 0 u = u := by
  simp [growthTime]

/-- Junk value outside the domain `1 + ρ u > 0`: `G(-1) = log 0 / 1 = 0` for `ρ = 1`. -/
example : growthTime 1 (-1) = 0 := by
  simp [growthTime]

/-- Strict shortening at concrete numbers: with `ρ = 1` the standard interval `[0, 1]` lasts
`G(1) - G(0) = log 2 < 1` in real time. -/
example : growthTime 1 1 - growthTime 1 0 < 1 - 0 := by
  have h : growthTime 1 1 = Real.log 2 := by norm_num [growthTime]
  rw [h, growthTime_zero_right]
  linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)]

/-- The same inequality through `growthTime_sub_lt` (its hypotheses are satisfiable). -/
example : growthTime 1 1 - growthTime 1 0 < 1 - 0 :=
  growthTime_sub_lt one_pos le_rfl one_pos

/-- The equivalence `t < G(y) ↔ R(t) < y` at `ρ = 1`, `t = 1`, `y = e`: `R(1) = e - 1 < e`. -/
example : (1 : ℝ) < growthTime 1 (Real.exp 1) := by
  rw [lt_growthTime_iff zero_le_one zero_le_one (Real.exp_pos 1).le,
    cumRate_expGrowthSize one_ne_zero, one_mul, div_one]
  linarith

/-! ### Growth holding times, from the definitions -/

/-- `n = 3`, `ρ = 1`, `T₃ = e - 1`: the most recent epoch lasts `G(e - 1) - G(0) = 1`. -/
example (T : ℕ → ℝ) (hT : T 3 = Real.exp 1 - 1) : growthHolding 1 3 T 3 = 1 := by
  simp [growthHolding, epochEnd, hT, growthTime]

/-- `n = 3`, `ρ = 0`: the epoch with two lineages lasts `T₂`. -/
example (T : ℕ → ℝ) : growthHolding 0 3 T 2 = T 2 := by
  have h2 : (Icc 2 3 : Finset ℕ) = {2, 3} := by decide
  simp [growthHolding, epochEnd, h2]

/-- Boundary `n = 1`: there is no epoch, `V_2 = 0`. -/
example (T : ℕ → ℝ) : epochEnd 1 T 2 = 0 := by
  simp [epochEnd]

/-- The real TMRCA is `G` of the standard one, for `n = 2`, `ρ = 1`, `T₂ = e - 1`: both equal
`1`. -/
example (T : ℕ → ℝ) (hT : T 2 = Real.exp 1 - 1) :
    ∑ k ∈ Icc 2 2, growthHolding 1 2 T k = 1 := by
  rw [sum_growthHolding]
  simp [hT, growthTime]

/-! ### Monotonicity of the spectrum -/

/-- The kernel entry for two lineages in a sample of two is `2` (both lineages carry one
copy). -/
example : sfsKernel 2 1 2 = 2 := by norm_num [sfsKernel]

/-- The strict-monotonicity hypotheses are satisfiable: `t = 0 < t' = 1` gives
`0 = variableSFS 1 2 0 1 < variableSFS 1 2 1 1 = 1`. -/
example : variableSFS 1 2 (fun _ => 0) 1 < variableSFS 1 2 (fun _ => 1) 1 :=
  variableSFS_lt_variableSFS one_pos le_rfl (fun _ _ => zero_le_one) zero_lt_one 1

example : variableSFS 1 2 (fun _ => 1) 1 = 1 := by
  norm_num [variableSFS, sfsKernel]

/-! ### Non-vacuity witness: a sample of two under growth `ρ = 1` -/

section Witness

/-- The counts under growth, equal to their conditional means. -/
noncomputable def xiG (θ : ℝ) (i : ℕ) (ω : Icc 2 2 → ℝ) : ℝ :=
  θ / 2 * sfsLength 2 i (tau2 ω) (fun k => growthTimes K2 1 k ω)

lemma integrable_xiG (θ : ℝ) (i : ℕ) : Integrable (xiG θ i) (piMeasure 2) := by
  unfold xiG sfsLength tau2
  exact (integrable_finsetSum _ fun _ hk =>
    (integrable_growthTimes zero_le_one measurable_K2 hk).const_mul _).const_mul _

lemma condExp_xiG (θ : ℝ) (i : ℕ) :
    (piMeasure 2)[xiG θ i | MeasurableSpace.comap tau2 ⊤ ⊔
        MeasurableSpace.comap (fun ω k => growthTimes K2 1 k ω) MeasurableSpace.pi] =ᵐ[piMeasure 2]
      fun ω => θ / 2 * sfsLength 2 i (tau2 ω) (fun k => growthTimes K2 1 k ω) := by
  have hmT : MeasurableSpace.comap (fun ω k => growthTimes K2 1 k ω) MeasurableSpace.pi ≤
      MeasurableSpace.pi := (measurable_growthTimes measurable_K2).comap_le
  refine (condExp_of_stronglyMeasurable (sup_le comap_tau2_le hmT) ?_
    (integrable_xiG θ i)).eventuallyEq
  refine Measurable.stronglyMeasurable ?_
  have hF : Measurable fun x : ℕ → ℝ =>
      θ / 2 * ∑ k ∈ Icc 2 2, ((([[1, 1], [2]] : List (List ℕ)).getD (2 - k) []).count i : ℝ) *
        x k := by
    fun_prop
  exact (hF.comp (comap_measurable _)).mono le_sup_right le_rfl

/-- `E ξ₁ = θ E T^1_2`, computed directly from the definitions (two lineages, each carrying
one copy, during the only epoch). -/
example (θ : ℝ) : (piMeasure 2)[xiG θ 1] = θ * (piMeasure 2)[growthTimes K2 1 2] := by
  have h : xiG θ 1 = fun ω => θ * growthTimes K2 1 2 ω := by
    funext ω
    simp [xiG, sfsLength, tau2]
    ring
  rw [h, integral_const_mul]

/-- **Non-vacuity of `integral_sfs_growth`**: every hypothesis holds on the witness, and the
theorem gives the same value `θ E T^1_2` as the direct computation above. -/
example (θ : ℝ) : (piMeasure 2)[xiG θ 1] = θ * (piMeasure 2)[growthTimes K2 1 2] := by
  rw [integral_sfs_growth zero_le_one measurable_K2 comap_tau2_le law_tau2 indep_tau2
    (integrable_xiG θ) (condExp_xiG θ) le_rfl (by norm_num)]
  norm_num [variableSFS, sfsKernel]
  ring

/-- **Non-vacuity of `integral_sfs_growth_lt`**: on the witness, `E ξ₁ < θ` for `θ > 0`. -/
example (θ : ℝ) (hθ : 0 < θ) : (piMeasure 2)[xiG θ 1] < θ := by
  have := integral_sfs_growth_lt hθ one_pos measurable_K2 comap_tau2_le law_tau2 indep_tau2
    (integrable_xiG θ) (condExp_xiG θ) le_rfl (by norm_num : 1 < 2)
  simpa using this

/-- **Non-vacuity of `integral_growthTimes_top`**: on the witness the mean of the only epoch is
`c₂ = ∫_0^∞ exp(-R(s)) ds`, so `E ξ₁ = θ c₂`. -/
example (θ : ℝ) : (piMeasure 2)[xiG θ 1] = θ * firstCoalMean (expGrowthSize 1) 2 := by
  rw [integral_sfs_growth zero_le_one measurable_K2 comap_tau2_le law_tau2 indep_tau2
    (integrable_xiG θ) (condExp_xiG θ) le_rfl (by norm_num),
    ← integral_growthTimes_top zero_le_one measurable_K2 le_rfl]
  norm_num [variableSFS, sfsKernel]
  ring

/-- The strict bound on the witness's epoch: `E T^1_2 < 1 = 1 / C(2,2)`. -/
example : (piMeasure 2)[growthTimes K2 1 2] < 1 := by
  have h := integral_growthTimes_lt (K := K2) one_pos measurable_K2
    (show 2 ∈ Icc 2 2 from mem_Icc.2 ⟨le_rfl, le_rfl⟩)
  simpa using h

/-- **Non-vacuity of `sfsCondMoments_growth`**: on the witness with `θ = 0` and zero counts,
every moment hypothesis holds. -/
lemma sfsCondMoments_growth_K2 : SFSCondMoments (piMeasure 2) (MeasurableSpace.comap tau2 ⊤ ⊔
    MeasurableSpace.comap (fun ω k => growthTimes K2 1 k ω) MeasurableSpace.pi) 0
    (fun _ _ => 0) (fun i ω => sfsLength 2 i (tau2 ω) (fun k => growthTimes K2 1 k ω)) :=
  sfsCondMoments_growth zero_le_one measurable_K2 comap_tau2_le law_tau2
    (fun _ => memLp_const 0) (fun _ => by simp) (fun _ _ => by simp)

/-- **Non-vacuity of `covariance_count_growth`**: on the `θ = 0` witness its right-hand side
is `0`, matching the covariance of the zero counts computed directly. -/
example : (if (1 : ℕ) = 1 then variableSFS 0 2 (fun k => (piMeasure 2)[growthTimes K2 1 k]) 1
      else 0) + (0 / 2 : ℝ) ^ 2 *
      cov[fun ω => sfsLength 2 1 (tau2 ω) (fun k => growthTimes K2 1 k ω),
        fun ω => sfsLength 2 1 (tau2 ω) (fun k => growthTimes K2 1 k ω); piMeasure 2] = 0 := by
  rw [← covariance_count_growth zero_le_one measurable_K2 comap_tau2_le law_tau2 indep_tau2
    sfsCondMoments_growth_K2 le_rfl (by norm_num) 1]
  simp [covariance]

end Witness

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSGrowth
