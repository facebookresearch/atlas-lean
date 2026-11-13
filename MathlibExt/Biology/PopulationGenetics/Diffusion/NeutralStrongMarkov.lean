/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Process.Stopping
public import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Realization
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Strong Markov property of the neutral Wright–Fisher diffusion

Let `X` be a continuous `[0, 1]`-valued process, adapted to a filtration `ℱ` indexed by `ℝ≥0`,
that is Markov with respect to `ℱ` with the neutral Wright–Fisher transition semigroup
`wfSemigroup`, in the conditional-expectation form taken by
`NeutralMartingaleProblem.isWrightFisherSolution_zero_of_markov`:
for `s ≤ t` and every continuous `g` on `[0, 1]`,
`μ[g (X t) | ℱ s] = (wfSemigroup (t - s) g) (X s)` almost surely (states are read in `[0, 1]`
through `Set.projIcc`). This file proves that `X` is then **strongly** Markov: for every
`ℱ`-stopping time `τ : Ω → WithTop ℝ≥0`, every `t ≥ 0` and every continuous `g`,
`μ[1_{τ < ∞} g (X (τ + t)) | ℱ_τ] = 1_{τ < ∞} (wfSemigroup t g) (X τ)` almost surely.

The Markov property is a hypothesis: for the selected realization `modifiedProcess x` with its
natural filtration it is the subject of a separate, not yet merged, development, which proves
it in exactly the form assumed here. `condExp_modifiedProcess_stoppedValue_add` specializes the
general result to that realization.

## Main results

* `setIntegral_stoppedValue_add_eq`: the strong Markov property integrated over an event
  `A ∈ ℱ_τ` intersected with `{τ < ∞}`.
* `condExp_stoppedValue_add_ae_eq`: the strong Markov property in conditional-expectation form.
* `condExp_stoppedValue_add_ae_eq_of_ne_top`: the same for an everywhere-finite stopping time,
  without indicators.
* `condExp_modifiedProcess_stoppedValue_add`: the specialization to the neutral Wright–Fisher
  realization `modifiedProcess x` under `rawMeasure x` with `naturalFiltration x`.

## Method

The classical argument for Feller processes. For the dyadic upper approximations
`τₙ = ⌈2ⁿ τ⌉ / 2ⁿ` the event `A ∩ {τₙ = k / 2ⁿ}` lies in `ℱ (k / 2ⁿ)` when `A ∈ ℱ_τ`, so the
simple Markov property at the deterministic times `k / 2ⁿ ≤ k / 2ⁿ + t`, summed over the countable
partition `{τₙ = k / 2ⁿ}` of `{τ < ∞}`, gives the integrated identity at `τₙ`. As `n → ∞`,
`τₙ ↓ τ`, and both integrands converge pointwise by path continuity of `X` and continuity of `g`
and `wfSemigroup t g`; they are bounded, so dominated convergence passes the identity to `τ`.
The right-hand side is `ℱ_τ`-measurable because a continuous adapted process is progressively
measurable.

## Scope

Proved for one-time functionals `g (X (τ + t))` with `g` continuous on `[0, 1]`, the class used
by the Markov hypothesis. Not covered: bounded measurable `g` (a monotone-class extension) and
multi-time or path functionals of the post-`τ` process.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), ch. 4, §1 (Markov processes; Prop. 1.7) and ch. 4, Thm. 2.7 (Feller processes are
  strong Markov, via dyadic approximation of stopping times).
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer (1999),
  ch. III, Thm. 3.1 (strong Markov property of Feller processes).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal unitInterval

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralStrongMarkov

open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup

noncomputable section

/-! ### Dyadic upper approximation of a time -/

/-- The dyadic upper approximation `⌈2ⁿ r⌉ / 2ⁿ` of a time `r`. -/
private def dyadicUp (n : ℕ) (r : ℝ≥0) : ℝ≥0 :=
  (⌈(2 : ℝ≥0) ^ n * r⌉₊ : ℝ≥0) / 2 ^ n

private theorem le_dyadicUp (n : ℕ) (r : ℝ≥0) : r ≤ dyadicUp n r := by
  unfold dyadicUp
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact Nat.le_ceil _

private theorem dyadicUp_le (n : ℕ) (r : ℝ≥0) : dyadicUp n r ≤ r + (1 / 2) ^ n := by
  unfold dyadicUp
  rw [div_le_iff₀ (by positivity), add_mul, div_pow, one_pow,
    div_mul_cancel₀ _ (by positivity), mul_comm r]
  exact (Nat.ceil_lt_add_one (by positivity)).le

private theorem tendsto_dyadicUp (r : ℝ≥0) :
    Tendsto (fun n => dyadicUp n r) atTop (𝓝 r) := by
  have h : Tendsto (fun n : ℕ => r + (1 / 2 : ℝ≥0) ^ n) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 / 2) (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (le_dyadicUp · r)
    (dyadicUp_le · r)

private theorem measurable_dyadicUp (n : ℕ) : Measurable (dyadicUp n) := by
  unfold dyadicUp
  exact (measurable_from_nat.comp (Nat.measurable_ceil.comp
    (measurable_const.mul measurable_id))).div_const _

@[simp]
private theorem untopA_coe (r : ℝ≥0) : (r : WithTop ℝ≥0).untopA = r :=
  WithTop.untopD_coe _ r

/-- The dyadic grid point `k / 2ⁿ`. -/
private def grid (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ n

private theorem grid_mono (n : ℕ) {j k : ℕ} (h : j ≤ k) : grid n j ≤ grid n k := by
  unfold grid
  gcongr

/-- A finite time lies at or below the grid point `m / 2ⁿ` iff its dyadic index is at most
`m`. -/
private theorem le_grid_iff (n m : ℕ) (a : WithTop ℝ≥0) :
    a ≤ (grid n m : WithTop ℝ≥0) ↔ a ≠ ⊤ ∧ ⌈(2 : ℝ≥0) ^ n * a.untopA⌉₊ ≤ m := by
  induction a with
  | top => simpa using WithTop.not_top_le_coe (grid n m)
  | coe r =>
    simp only [WithTop.coe_le_coe, ne_eq, WithTop.coe_ne_top, not_false_eq_true,
      untopA_coe, true_and, Nat.ceil_le, grid]
    rw [le_div_iff₀ (by positivity), mul_comm]

/-! ### Measurability and integrability along the paths -/

/-- States are read in `[0, 1]` through `Set.projIcc`, as in the Markov hypothesis. -/
local notation "toI" => projIcc (0 : ℝ) 1 zero_le_one

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

private theorem measurable_uncurry (hcont : ∀ ω, Continuous fun t => X t ω)
    (hadapt : StronglyAdapted ℱ X) : Measurable (Function.uncurry X) :=
  measurable_uncurry_of_continuous_of_measurable hcont fun t =>
    ((hadapt t).mono (ℱ.le t)).measurable

private theorem measurable_comp_time (hX : Measurable (Function.uncurry X)) {ρ : Ω → ℝ≥0}
    (hρ : Measurable ρ) (g : C(I, ℝ)) : Measurable fun ω => g (toI (X (ρ ω) ω)) :=
  (g.continuous.comp continuous_projIcc).measurable.comp (hX.comp (hρ.prodMk measurable_id))

private theorem integrable_comp [IsFiniteMeasure μ] {F : Ω → ℝ} (hF : Measurable F)
    (g : C(I, ℝ)) : Integrable (fun ω => g (toI (F ω))) μ :=
  Integrable.of_bound
    ((g.continuous.comp continuous_projIcc).measurable.comp hF).aestronglyMeasurable
    ‖g‖ (Eventually.of_forall fun _ => g.norm_coe_le_norm _)

private theorem integrable_comp_time [IsFiniteMeasure μ] (hX : Measurable (Function.uncurry X))
    {ρ : Ω → ℝ≥0} (hρ : Measurable ρ) (g : C(I, ℝ)) :
    Integrable (fun ω => g (toI (X (ρ ω) ω))) μ :=
  integrable_comp (hX.comp (hρ.prodMk measurable_id)) g

private theorem stoppedValue_add_of_ne_top {ω : Ω} (hω : τ ω ≠ ⊤) (t : ℝ≥0) :
    stoppedValue X (fun ω => τ ω + t) ω = X ((τ ω).untopA + t) ω := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hω
  simp only [stoppedValue, ← hr, ← WithTop.coe_add, untopA_coe]

/-! ### The dyadic partition of `{τ < ∞}` -/

/-- The event `{τ < ∞, ⌈2ⁿ τ⌉ = k}` on which the dyadic approximation of `τ` equals `k / 2ⁿ`. -/
private def dyadicSet (τ : Ω → WithTop ℝ≥0) (n k : ℕ) : Set Ω :=
  {ω | τ ω ≠ ⊤ ∧ ⌈(2 : ℝ≥0) ^ n * (τ ω).untopA⌉₊ = k}

private theorem measurableSet_inter_dyadicSet (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (n k : ℕ) :
    MeasurableSet[ℱ (grid n k)] (A ∩ dyadicSet τ n k) := by
  cases k with
  | zero =>
    have h : A ∩ dyadicSet τ n 0 = A ∩ {ω | τ ω ≤ grid n 0} := by
      ext ω
      simp only [dyadicSet, mem_inter_iff, mem_ofPred_eq, le_grid_iff, Nat.le_zero]
    rw [h]
    exact hA.2 _
  | succ j =>
    have h : A ∩ dyadicSet τ n (j + 1) =
        (A ∩ {ω | τ ω ≤ grid n (j + 1)}) ∩ {ω | τ ω ≤ grid n j}ᶜ := by
      ext ω
      simp only [dyadicSet, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, le_grid_iff]
      by_cases hω : τ ω = ⊤
      · simp [hω]
      · simp only [ne_eq, hω, not_false_eq_true, true_and]
        constructor
        · rintro ⟨ha, hk⟩
          exact ⟨⟨ha, hk.le⟩, by omega⟩
        · rintro ⟨⟨ha, hk⟩, hj⟩
          exact ⟨ha, by omega⟩
    rw [h]
    exact (hA.2 _).inter ((ℱ.mono (grid_mono n j.le_succ) _ (hτ _)).compl)

private theorem dyadicUp_of_mem_dyadicSet {n k : ℕ} {ω : Ω} (hω : ω ∈ dyadicSet τ n k) :
    dyadicUp n (τ ω).untopA = grid n k := by
  simp only [dyadicUp, grid, hω.2]

/-- **Strong Markov property at a dyadic approximation.** The integrated identity holds with
`τ` replaced by `⌈2ⁿ τ⌉ / 2ⁿ`. -/
private theorem setIntegral_dyadic [IsFiniteMeasure μ]
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (hτ : IsStoppingTime ℱ τ) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (t : ℝ≥0) (g : C(I, ℝ)) (n : ℕ) :
    ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, g (toI (X (dyadicUp n (τ ω).untopA + t) ω)) ∂μ =
      ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, wfSemigroup t g (toI (X (dyadicUp n (τ ω).untopA) ω)) ∂μ := by
  have hX := measurable_uncurry hcont hadapt
  have hρ : Measurable fun ω => dyadicUp n (τ ω).untopA :=
    (measurable_dyadicUp n).comp hτ.measurable'.untopA
  have hS : ∀ k, MeasurableSet (A ∩ dyadicSet τ n k) := fun k =>
    ℱ.le _ _ (measurableSet_inter_dyadicSet hτ hA n k)
  have hU : A ∩ {ω | τ ω ≠ ⊤} = ⋃ k, A ∩ dyadicSet τ n k := by
    ext ω
    simp [dyadicSet]
  have hD : Pairwise (Function.onFun Disjoint fun k => A ∩ dyadicSet τ n k) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, -, hi⟩ ⟨-, -, hj⟩
    exact hij (hi.symm.trans hj)
  rw [hU, integral_iUnion hS hD (integrable_comp_time hX (hρ.add_const t) g).integrableOn,
    integral_iUnion hS hD (integrable_comp_time hX hρ (wfSemigroup t g)).integrableOn]
  refine tsum_congr fun k => ?_
  have hm := hmarkov (grid n k) (grid n k + t) le_self_add g
  have hgap : ((grid n k + t : ℝ≥0) : ℝ) - grid n k = t := by
    push_cast
    ring
  calc ∫ ω in A ∩ dyadicSet τ n k, g (toI (X (dyadicUp n (τ ω).untopA + t) ω)) ∂μ
      = ∫ ω in A ∩ dyadicSet τ n k, g (toI (X (grid n k + t) ω)) ∂μ :=
        setIntegral_congr_fun (hS k) fun ω hω => by
          simp only [dyadicUp_of_mem_dyadicSet hω.2]
    _ = ∫ ω in A ∩ dyadicSet τ n k,
          (μ[fun ω => g (toI (X (grid n k + t) ω)) | ℱ (grid n k)]) ω ∂μ :=
        (setIntegral_condExp (ℱ.le _)
          (integrable_comp ((hadapt _).mono (ℱ.le _)).measurable g)
          (measurableSet_inter_dyadicSet hτ hA n k)).symm
    _ = ∫ ω in A ∩ dyadicSet τ n k, wfSemigroup t g (toI (X (grid n k) ω)) ∂μ :=
        setIntegral_congr_ae (hS k) (hm.mono fun ω hω _ => by rw [hω, hgap])
    _ = ∫ ω in A ∩ dyadicSet τ n k,
          wfSemigroup t g (toI (X (dyadicUp n (τ ω).untopA) ω)) ∂μ :=
        (setIntegral_congr_fun (hS k) fun ω hω => by
          simp only [dyadicUp_of_mem_dyadicSet hω.2]).symm

/-! ### The strong Markov property -/

/-- **Strong Markov property, integrated form.** Let `X` be a continuous process adapted to `ℱ`
under a finite measure `μ` that is Markov with respect to `ℱ` with the neutral Wright–Fisher
semigroup, in the form of `NeutralMartingaleProblem.isWrightFisherSolution_zero_of_markov`.
Then for every `ℱ`-stopping time `τ`, every `A ∈ ℱ_τ`, every `t ≥ 0` and every continuous `g`
on `[0, 1]`,
`∫_{A ∩ {τ < ∞}} g (X (τ + t)) dμ = ∫_{A ∩ {τ < ∞}} (wfSemigroup t g) (X τ) dμ`.

Source: Ethier & Kurtz (1986), ch. 4, Thm. 2.7; Revuz & Yor (1999), ch. III, Thm. 3.1
(dyadic approximation of `τ` from above and right continuity of the paths). -/
theorem setIntegral_stoppedValue_add_eq [IsFiniteMeasure μ]
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) (g : C(I, ℝ)) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    ∫ ω in A ∩ {ω | τ ω ≠ ⊤},
        g (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun ω => τ ω + t) ω)) ∂μ =
      ∫ ω in A ∩ {ω | τ ω ≠ ⊤},
        wfSemigroup t g (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω)) ∂μ := by
  have hX := measurable_uncurry hcont hadapt
  have hτm : Measurable fun ω => (τ ω).untopA := hτ.measurable'.untopA
  have hB : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter hτ.measurableSet_eq_top.compl
  have hcongr : ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, g (toI (stoppedValue X (fun ω => τ ω + t) ω)) ∂μ =
      ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, g (toI (X ((τ ω).untopA + t) ω)) ∂μ :=
    setIntegral_congr_fun hB fun ω hω => by simp only [stoppedValue_add_of_ne_top hω.2]
  rw [hcongr]
  simp only [stoppedValue]
  have hL : Tendsto (fun n => ∫ ω in A ∩ {ω | τ ω ≠ ⊤},
      g (toI (X (dyadicUp n (τ ω).untopA + t) ω)) ∂μ) atTop
      (𝓝 (∫ ω in A ∩ {ω | τ ω ≠ ⊤}, g (toI (X ((τ ω).untopA + t) ω)) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
      (fun n => (measurable_comp_time hX
        (((measurable_dyadicUp n).comp hτm).add_const t) g).aestronglyMeasurable)
      (integrable_const _) (fun _ => Eventually.of_forall fun _ => g.norm_coe_le_norm _)
      (Eventually.of_forall fun ω => ((g.continuous.comp continuous_projIcc).tendsto _).comp
        (((hcont ω).tendsto _).comp ((tendsto_dyadicUp _).add_const t)))
  have hR : Tendsto (fun n => ∫ ω in A ∩ {ω | τ ω ≠ ⊤},
      wfSemigroup t g (toI (X (dyadicUp n (τ ω).untopA) ω)) ∂μ) atTop
      (𝓝 (∫ ω in A ∩ {ω | τ ω ≠ ⊤}, wfSemigroup t g (toI (X (τ ω).untopA ω)) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => ‖wfSemigroup t g‖)
      (fun n => (measurable_comp_time hX ((measurable_dyadicUp n).comp hτm)
        (wfSemigroup t g)).aestronglyMeasurable)
      (integrable_const _)
      (fun _ => Eventually.of_forall fun _ => (wfSemigroup t g).norm_coe_le_norm _)
      (Eventually.of_forall fun ω =>
        (((wfSemigroup t g).continuous.comp continuous_projIcc).tendsto _).comp
          (((hcont ω).tendsto _).comp (tendsto_dyadicUp _)))
  exact tendsto_nhds_unique
    (hL.congr fun n => setIntegral_dyadic hcont hadapt hmarkov hτ hA t g n) hR

/-- **Strong Markov property of the neutral Wright–Fisher diffusion.** Under the hypotheses of
`setIntegral_stoppedValue_add_eq`, for every `ℱ`-stopping time `τ`, every `t ≥ 0` and every
continuous `g` on `[0, 1]`,
`μ[1_{τ < ∞} g (X (τ + t)) | ℱ_τ] = 1_{τ < ∞} (wfSemigroup t g) (X τ)` almost surely.

Source: Ethier & Kurtz (1986), ch. 4, Thm. 2.7; Revuz & Yor (1999), ch. III, Thm. 3.1. -/
theorem condExp_stoppedValue_add_ae_eq [IsFiniteMeasure μ]
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) (g : C(I, ℝ)) :
    μ[{ω | τ ω ≠ ⊤}.indicator
        (fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun ω => τ ω + t) ω))) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator
        (fun ω => wfSemigroup t g (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω))) := by
  have hX := measurable_uncurry hcont hadapt
  have hτm : Measurable fun ω => (τ ω).untopA := hτ.measurable'.untopA
  have hfin : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    hτ.measurable (measurableSet_singleton ⊤).compl
  have hfin' : MeasurableSet {ω | τ ω ≠ ⊤} := hτ.measurableSpace_le _ hfin
  have hG : StronglyMeasurable[hτ.measurableSpace]
      ({ω | τ ω ≠ ⊤}.indicator fun ω => wfSemigroup t g (toI (stoppedValue X τ ω))) :=
    ((((wfSemigroup t g).continuous.comp continuous_projIcc).measurable.comp
      (measurable_stoppedValue (hadapt.isStronglyProgressive_of_continuous hcont)
        hτ)).stronglyMeasurable).indicator hfin
  have hFeq : {ω | τ ω ≠ ⊤}.indicator
        (fun ω => g (toI (stoppedValue X (fun ω => τ ω + t) ω))) =
      {ω | τ ω ≠ ⊤}.indicator (fun ω => g (toI (X ((τ ω).untopA + t) ω))) :=
    indicator_congr fun ω hω => by simp only [stoppedValue_add_of_ne_top hω]
  have hFint : Integrable ({ω | τ ω ≠ ⊤}.indicator
      (fun ω => g (toI (stoppedValue X (fun ω => τ ω + t) ω)))) μ := by
    rw [hFeq]
    exact (integrable_comp_time hX (hτm.add_const t) g).indicator hfin'
  have hGint : Integrable ({ω | τ ω ≠ ⊤}.indicator
      fun ω => wfSemigroup t g (toI (stoppedValue X τ ω))) μ :=
    (integrable_comp_time hX hτm (wfSemigroup t g)).indicator hfin'
  refine (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hFint
    (fun s _ _ => hGint.integrableOn) (fun s hs _ => ?_) hG.aestronglyMeasurable).symm
  rw [setIntegral_indicator hfin', setIntegral_indicator hfin']
  exact (setIntegral_stoppedValue_add_eq hcont hadapt hmarkov hτ t g hs).symm

/-- **Strong Markov property at an everywhere-finite stopping time.** If `τ` never takes the
value `∞`, then `μ[g (X (τ + t)) | ℱ_τ] = (wfSemigroup t g) (X τ)` almost surely. -/
theorem condExp_stoppedValue_add_ae_eq_of_ne_top [IsFiniteMeasure μ]
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (hτ : IsStoppingTime ℱ τ) (hτ_fin : ∀ ω, τ ω ≠ ⊤) (t : ℝ≥0) (g : C(I, ℝ)) :
    μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun ω => τ ω + t) ω)) |
        hτ.measurableSpace] =ᵐ[μ]
      fun ω => wfSemigroup t g (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω)) := by
  have hs : {ω | τ ω ≠ ⊤} = univ := eq_univ_of_forall hτ_fin
  simpa only [hs, indicator_univ] using
    condExp_stoppedValue_add_ae_eq hcont hadapt hmarkov hτ t g

/-! ### The neutral Wright–Fisher realization -/

open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem

/-- **Strong Markov property of the neutral Wright–Fisher realization.** Suppose the selected
continuous realization `modifiedProcess x` under `rawMeasure x` is Markov for its natural
filtration with the neutral semigroup, in the form of
`NeutralMartingaleProblem.isWrightFisherSolution_zero_of_markov`. Then for every stopping time
`τ` of `naturalFiltration x`, every `t ≥ 0` and every continuous `g` on `[0, 1]`,
`E_x[1_{τ < ∞} g (X (τ + t)) | ℱ_τ] = 1_{τ < ∞} (wfSemigroup t g) (X τ)` almost surely, where
`X = modifiedState x` is the realization read in the state space `[0, 1]`.

Source: Ethier & Kurtz (1986), ch. 4, Thm. 2.7 and ch. 10 (Wright–Fisher diffusion). -/
theorem condExp_modifiedProcess_stoppedValue_add (x : I)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      (rawMeasure x)[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess x t ω)) |
          naturalFiltration x s] =ᵐ[rawMeasure x]
        fun ω =>
          wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess x s ω)))
    {τ : SamplePath → WithTop ℝ≥0} (hτ : IsStoppingTime (naturalFiltration x) τ) (t : ℝ≥0)
    (g : C(I, ℝ)) :
    (rawMeasure x)[{ω | τ ω ≠ ⊤}.indicator
        (fun ω => g (stoppedValue (modifiedState x) (fun ω => τ ω + t) ω)) |
        hτ.measurableSpace] =ᵐ[rawMeasure x]
      {ω | τ ω ≠ ⊤}.indicator
        (fun ω => wfSemigroup t g (stoppedValue (modifiedState x) τ ω)) := by
  have hproj : ∀ (ρ : SamplePath → WithTop ℝ≥0) ω,
      projIcc (0 : ℝ) 1 zero_le_one (stoppedValue (modifiedProcess x) ρ ω) =
        stoppedValue (modifiedState x) ρ ω :=
    fun ρ ω => projIcc_of_mem _ (modifiedProcess_mem_Icc x _ ω)
  simpa only [hproj] using condExp_stoppedValue_add_ae_eq (continuous_modifiedProcess x)
    (stronglyAdapted_naturalFiltration x) hmarkov hτ t g

end

end MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralStrongMarkov
