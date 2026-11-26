/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.SFSBottleneck
public import DomainsTest.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

/-!
# Tests for the site frequency spectrum under a bottleneck

Values of the intensity `R`, the time change `G` and the bottleneck holding times computed
from the definitions (a bottleneck `a = 1`, `d = 1`, `f = 1/2`, whose window in standard time
is `[1, 3]`; an expansion `f = 2`; the constant-size boundaries `f = 1` and `d = 0`; the empty
genealogy `n = 1`), satisfiability of the comparison hypotheses, and a non-vacuity witness for
the bottleneck spectrum theorems: sample size `2`, the product model of the Kingman holding
times and the constant topology from the `SiteFrequencySpectrum` tests, and `ξ i` equal to its
conditional mean. On the witness `E ξ₁` is computed once directly from the definitions and once
through `integral_sfs_bottleneck`; the two agree, and the comparison theorems give
`E ξ₁ < θ` for the bottleneck `f = 1/2`, `θ ≤ E ξ₁` for the expansion `f = 2` and `E ξ₁ = θ`
for `f = 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSBottleneck

open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
open MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSGrowth
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSBottleneck
open MathlibExtTest.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

/-! ### The intensity and the time change, from the definitions -/

/-- Constant size (`f = 1`): `η ≡ 1` and `R(s) = s`, directly from `cumRate`. -/
example (a d s : ℝ) : cumRate (bottleneckSize a d 1) s = s := by
  simp [cumRate, bottleneckSize]

/-- Before the bottleneck (`a = 2`, `s = 1`): `η = 1` on `[0, 1]`, so `R(1) = 1`, directly
from `cumRate`. -/
example : cumRate (bottleneckSize 2 1 (1 / 2)) 1 = 1 := by
  have h : Set.EqOn (fun r => (bottleneckSize 2 1 (1 / 2) r)⁻¹) (fun _ => (1 : ℝ))
      (Set.uIcc 0 1) := by
    intro r hr
    rw [Set.uIcc_of_le zero_le_one] at hr
    have hn : ¬((2 : ℝ) ≤ r ∧ r < 2 + 1) := fun h => by linarith [h.1, hr.2]
    simp only [bottleneckSize, hn, ↓reduceIte, inv_one]
  simp only [cumRate]
  rw [intervalIntegral.integral_congr h]
  simp

/-- `a = 1`, `d = 1`, `f = 1/2`: `R(3) = 3 + (2 - 1) · 1 = 4` from the closed form. -/
example : bottleneckRate 1 1 (1 / 2) 3 = 4 := by
  rw [bottleneckRate, bottleneckOverlap, max_eq_left (by norm_num), min_eq_right (by norm_num)]
  norm_num

/-- The same value of `R(3)` through `cumRate_bottleneckSize`. -/
example : cumRate (bottleneckSize 1 1 (1 / 2)) 3 = 4 := by
  rw [cumRate_bottleneckSize zero_le_one zero_le_one (by norm_num), bottleneckRate,
    bottleneckOverlap, max_eq_left (by norm_num), min_eq_right (by norm_num)]
  norm_num

/-- `G(4) = 4 - (1 - 1/2) · 2 = 3`, so `G` undoes `R(3) = 4`. -/
example : bottleneckTime 1 1 (1 / 2) 4 = 3 := by
  rw [bottleneckTime, bottleneckOverlap, max_eq_left (by norm_num), min_eq_right (by norm_num)]
  norm_num

/-- Inside the window: `G(2) = 2 - (1/2) · 1 = 3/2`. -/
example : bottleneckTime 1 1 (1 / 2) 2 = 3 / 2 := by
  rw [bottleneckTime, bottleneckOverlap, max_eq_left (by norm_num), min_eq_left (by norm_num)]
  norm_num

/-- Before the window `G` is the identity: `G(1/2) = 1/2`. -/
example : bottleneckTime 1 1 (1 / 2) (1 / 2) = 1 / 2 := by
  rw [bottleneckTime, bottleneckOverlap, max_eq_right (by norm_num), min_eq_left (by norm_num)]
  norm_num

/-- Boundaries: `f = 1` and `d = 0` give `G = id`, from the definition. -/
example (a d u : ℝ) : bottleneckTime a d 1 u = u ∧ bottleneckTime a 0 (1 / 2) u = u := by
  refine ⟨by simp [bottleneckTime], ?_⟩
  rw [bottleneckTime, bottleneckOverlap, zero_div, min_eq_right (le_max_right _ _)]
  ring

/-- Junk value of `G` for `a < 0` (outside the model): `G(0) = -(1/2) ≠ 0` for `a = -1`,
`d = 1`, `f = 1/2`, so `bottleneckTime_zero` needs `a ≥ 0`. -/
example : bottleneckTime (-1) 1 (1 / 2) 0 = -(1 / 2) := by
  rw [bottleneckTime, bottleneckOverlap, max_eq_left (by norm_num), min_eq_left (by norm_num)]
  norm_num

/-- Strict shortening at concrete numbers: with `f = 1/2` the standard interval `[0, 2]` lasts
`G(2) - G(0) = 3/2 < 2` in real time. -/
example : bottleneckTime 1 1 (1 / 2) 2 - bottleneckTime 1 1 (1 / 2) 0 < 2 - 0 := by
  norm_num [bottleneckTime, bottleneckOverlap, max_eq_left, max_eq_right, min_eq_left,
    min_eq_right]

/-- The bottleneck bound through `bottleneckTime_sub_le` (its hypotheses are satisfiable). -/
example : bottleneckTime 1 1 (1 / 2) 2 - bottleneckTime 1 1 (1 / 2) 0 ≤ 2 - 0 :=
  bottleneckTime_sub_le (by norm_num) (by norm_num)

/-- An expansion lengthens time: `a = 0`, `d = 1`, `f = 2` (window `[0, 1/2]` in standard time)
gives `G(1) = 1 + 1/2 > 1`, from the definition. -/
example : 1 < bottleneckTime 0 1 2 1 := by
  rw [bottleneckTime, bottleneckOverlap, max_eq_left (by norm_num), min_eq_right (by norm_num)]
  norm_num

/-- The same through `le_bottleneckTime_sub`. -/
example : 1 - 0 ≤ bottleneckTime 0 1 2 1 - bottleneckTime 0 1 2 0 :=
  le_bottleneckTime_sub (by norm_num) zero_le_one

/-- The equivalence `t < G(y) ↔ R(t) < y` at `t = 3`, `y = 5`: `R(3) = 4 < 5`. -/
example : (3 : ℝ) < bottleneckTime 1 1 (1 / 2) 5 := by
  rw [lt_bottleneckTime_iff zero_le_one (by norm_num), bottleneckRate, bottleneckOverlap,
    max_eq_left (by norm_num), min_eq_right (by norm_num)]
  norm_num

/-! ### Bottleneck holding times, from the definitions -/

/-- `n = 3`, `T₃ = 4`: the most recent epoch lasts `G(4) - G(0) = 3`. -/
example (T : ℕ → ℝ) (hT : T 3 = 4) : bottleneckHolding 1 1 (1 / 2) 3 T 3 = 3 := by
  norm_num [bottleneckHolding, epochEnd, hT, bottleneckTime, bottleneckOverlap, max_eq_left,
    max_eq_right, min_eq_left, min_eq_right]

/-- Boundary `n = 1`: there is no epoch, `V_2 = 0`. -/
example (T : ℕ → ℝ) : epochEnd 1 T 2 = 0 := by
  simp [epochEnd]

/-- The real TMRCA is `G` of the standard one, for `n = 2`, `T₂ = 4`: both equal `3`. -/
example (T : ℕ → ℝ) (hT : T 2 = 4) :
    ∑ k ∈ Icc 2 2, bottleneckHolding 1 1 (1 / 2) 2 T k = 3 := by
  rw [sum_bottleneckHolding zero_le_one zero_le_one (by norm_num)]
  simp only [Icc_self, sum_singleton, hT]
  rw [bottleneckTime, bottleneckOverlap, max_eq_left (by norm_num), min_eq_right (by norm_num)]
  norm_num

/-- The strict-shortening hypotheses of `bottleneckHolding_two_lt` are satisfiable: `n = 2`,
`T₂ = 2`, `a = 1`, `d = 1`, `f = 1/2` (so `V_3 = 0 < 3`, `T₂ > 1`), and the epoch lasts
`G(2) = 3/2 < 2`. -/
example (T : ℕ → ℝ) (hT2 : T 2 = 2) : bottleneckHolding 1 1 (1 / 2) 2 T 2 < T 2 := by
  have h3 : epochEnd 2 T 3 = 0 := by simp [epochEnd]
  refine bottleneckHolding_two_lt zero_le_one one_pos (by norm_num) (by norm_num) le_rfl
    (fun j hj => ?_) (by rw [h3]; norm_num) (by rw [hT2]; norm_num)
  rw [show j = 2 by simpa using hj, hT2]
  norm_num

/-! ### Non-vacuity witness: a sample of two under a bottleneck -/

section Witness

/-- The counts under the bottleneck history `(a, d, f)`, equal to their conditional means. -/
noncomputable def xiB (a d f θ : ℝ) (i : ℕ) (ω : Icc 2 2 → ℝ) : ℝ :=
  θ / 2 * sfsLength 2 i (tau2 ω) (fun k => bottleneckTimes K2 a d f k ω)

lemma integrable_xiB {a d f : ℝ} (hd : 0 ≤ d) (hf : 0 < f) (θ : ℝ) (i : ℕ) :
    Integrable (xiB a d f θ i) (piMeasure 2) := by
  unfold xiB sfsLength tau2
  exact (integrable_finsetSum _ fun _ hk =>
    (integrable_bottleneckTimes hd hf measurable_K2 hk).const_mul _).const_mul _

lemma condExp_xiB {a d f : ℝ} (hd : 0 ≤ d) (hf : 0 < f) (θ : ℝ) (i : ℕ) :
    (piMeasure 2)[xiB a d f θ i | MeasurableSpace.comap tau2 ⊤ ⊔
        MeasurableSpace.comap (fun ω k => bottleneckTimes K2 a d f k ω)
          MeasurableSpace.pi] =ᵐ[piMeasure 2]
      fun ω => θ / 2 * sfsLength 2 i (tau2 ω) (fun k => bottleneckTimes K2 a d f k ω) := by
  have hmT : MeasurableSpace.comap (fun ω k => bottleneckTimes K2 a d f k ω)
      MeasurableSpace.pi ≤ MeasurableSpace.pi :=
    (measurable_bottleneckTimes measurable_K2).comap_le
  refine (condExp_of_stronglyMeasurable (sup_le comap_tau2_le hmT) ?_
    (integrable_xiB hd hf θ i)).eventuallyEq
  refine Measurable.stronglyMeasurable ?_
  have hF : Measurable fun x : ℕ → ℝ =>
      θ / 2 * ∑ k ∈ Icc 2 2, ((([[1, 1], [2]] : List (List ℕ)).getD (2 - k) []).count i : ℝ) *
        x k := by
    fun_prop
  exact (hF.comp (comap_measurable _)).mono le_sup_right le_rfl

/-- `E ξ₁ = θ E T^b_2`, computed directly from the definitions (two lineages, each carrying
one copy, during the only epoch). -/
lemma integral_xiB_direct (a d f θ : ℝ) :
    (piMeasure 2)[xiB a d f θ 1] = θ * (piMeasure 2)[bottleneckTimes K2 a d f 2] := by
  have h : xiB a d f θ 1 = fun ω => θ * bottleneckTimes K2 a d f 2 ω := by
    funext ω
    simp [xiB, sfsLength, tau2]
    ring
  rw [h, integral_const_mul]

/-- **Non-vacuity of `integral_sfs_bottleneck`**: every hypothesis holds on the witness
(`a = 0`, `d = 1`, `f = 1/2`), and the theorem gives the same value `θ E T^b_2` as the direct
computation above. -/
example (θ : ℝ) :
    (piMeasure 2)[xiB 0 1 (1 / 2) θ 1] = θ * (piMeasure 2)[bottleneckTimes K2 0 1 (1 / 2) 2] := by
  rw [integral_sfs_bottleneck zero_le_one (by norm_num) measurable_K2 comap_tau2_le law_tau2
    indep_tau2 (integrable_xiB zero_le_one (by norm_num) θ)
    (condExp_xiB zero_le_one (by norm_num) θ) le_rfl (by norm_num)]
  norm_num [variableSFS, sfsKernel]
  ring

/-- **Non-vacuity of `integral_sfs_bottleneck_lt`**: on the witness, `E ξ₁ < θ` for `θ > 0`. -/
example (θ : ℝ) (hθ : 0 < θ) : (piMeasure 2)[xiB 0 1 (1 / 2) θ 1] < θ := by
  have := integral_sfs_bottleneck_lt (a := 0) (d := 1) (f := 1 / 2) hθ le_rfl
    one_pos (by norm_num) (by norm_num) measurable_K2
    comap_tau2_le law_tau2 indep_tau2 (integrable_xiB zero_le_one (by norm_num) θ)
    (condExp_xiB zero_le_one (by norm_num) θ) le_rfl (by norm_num : 1 < 2)
  simpa using this

/-- **Non-vacuity of `integral_sfs_bottleneck_ge`**: for the expansion `f = 2`, `θ ≤ E ξ₁`. -/
example (θ : ℝ) (hθ : 0 ≤ θ) : θ ≤ (piMeasure 2)[xiB 0 1 2 θ 1] := by
  have := integral_sfs_bottleneck_ge (a := 0) (d := 1) (f := 2) hθ zero_le_one
    one_le_two measurable_K2
    comap_tau2_le law_tau2 indep_tau2 (integrable_xiB zero_le_one two_pos θ)
    (condExp_xiB zero_le_one two_pos θ) le_rfl (by norm_num : 1 < 2)
  simpa using this

/-- **Non-vacuity of `integral_sfs_bottleneck_eq`**: for `f = 1`, `E ξ₁ = θ`, matching the
direct computation `θ E T_2 = θ` of Kingman's coalescent. -/
example (θ : ℝ) : (piMeasure 2)[xiB 0 1 1 θ 1] = θ := by
  have := integral_sfs_bottleneck_eq (a := 0) (d := 1) (f := 1) (Or.inl rfl)
    zero_le_one one_pos measurable_K2
    comap_tau2_le law_tau2 indep_tau2 (integrable_xiB zero_le_one one_pos θ)
    (condExp_xiB zero_le_one one_pos θ) le_rfl (by norm_num : 1 < 2)
  simpa using this

/-- **Non-vacuity of `integral_bottleneckTimes_top`**: on the witness the mean of the only
epoch is `c₂ = ∫_0^∞ exp(-R(s)) ds`, so `E ξ₁ = θ c₂`. -/
example (θ : ℝ) :
    (piMeasure 2)[xiB 0 1 (1 / 2) θ 1] = θ * firstCoalMean (bottleneckSize 0 1 (1 / 2)) 2 := by
  rw [integral_xiB_direct, integral_bottleneckTimes_top le_rfl zero_le_one (by norm_num)
    measurable_K2 le_rfl]

/-- The strict bound on the witness's epoch: `E T^b_2 < 1 = 1 / C(2,2)`. -/
example : (piMeasure 2)[bottleneckTimes K2 0 1 (1 / 2) 2] < 1 := by
  have h := integral_bottleneckTimes_two_lt (K := K2) (a := 0) (d := 1) (f := 1 / 2) le_rfl
    one_pos (by norm_num) (by norm_num) measurable_K2 le_rfl
  simpa using h

/-- The positive-probability event behind the strict bound is satisfiable on the witness. -/
example : 0 < piMeasure 2 {ω | epochEnd 2 (fun j => K2.T j ω) 3 < 2 ∧ (0 : ℝ) < K2.T 2 ω} :=
  measure_epochEnd_three_lt_pos K2 le_rfl two_pos le_rfl

end Witness

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSBottleneck
