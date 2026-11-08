/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConditionalOptionalStopping

import Mathlib.Probability.Martingale.Centering

/-!
# Conditional optional stopping for uniformly integrable submartingales

For a uniformly integrable submartingale `f` and stopping times `L ≤ M`
(possibly infinite),
`f_L ≤ᵐ μ[f_M | ℱ_L]`, where `f_τ` is the stopped value at `τ`, with the
a.e. limit `f_∞` used on `{τ = ∞}`. Taking integrals gives the expectation
form `∫ f_L ≤ ∫ f_M`.

## Source

This proves the whole-process UI specialization of the target
"Theorem (General form of optional stopping)" (Lecture 29)
of `v1/Atlas/TheoryOfProbability/targets.yaml`: "If `L ≤ M` are stopping
times and `Y_{M ∧ n}` is a uniformly integrable submartingale, then
`EY_L ≤ EY_M` and `Y_L ≤ E(Y_M | ℱ_L)`." The v1 file
`GeneralOptionalStopping.lean` only proves the bounded-stopping-time
form and leaves the unbounded form unproved; the bounded form was
ported in an earlier batch, the expectation form for unbounded stopping
times in another, and the conditional form for martingales in a third.
The conditional form for submartingales, proved here, is in none of
them.

## Proof outline

Write `f = M + A` for the Doob decomposition (`martingalePart`,
`predictablePart`). Since `f` is uniformly integrable, so is `A` (it is
dominated by its integrable limit `A_∞`), hence so is the martingale
part `M = f - A`. The martingale part satisfies the conditional
optional-stopping equality by optional sampling at `τ ∧ n` for each
stopping time `τ`, plus Lévy's upward theorem for the stopped filtration
`n ↦ ℱ_{τ ∧ n}` and the tower property. The predictable part satisfies
`A_L ≤ μ[A_M | ℱ_L]` because `A` is monotone and each
`A_{L ∧ n}` is `ℱ_L`-measurable, so conditioning on `ℱ_L` fixes it
while monotonicity bounds the other side. Adding the two parts gives
the result.

## Scope and canonical API

The stopped value is the existing `MeasureTheory.stoppedValueAtTop` from
`OptionalStoppingUniformIntegrable`, with its finite stopped-value branch and
`limUnder atTop` branch at infinity. The martingale conditional equality and
stopped-filtration machinery come from `ConditionalOptionalStopping`; whole-process
UI supplies its stopped-process UI premise through the canonical preservation theorem.
The bounded conditional result is already public in `BoundedOptionalStopping`.

The new content is the predictable-part conditional argument and its combination
with the canonical martingale result. The sharper predictable-part estimates and
Doob-decomposition arguments are retained. The hypothesis here remains UI of the
whole process `f`; the book's weaker stopped-process UI hypothesis is not claimed.

## Main results

* `MeasureTheory.stoppedValueAtTop`: the existing canonical stopped value at a
  possibly infinite stopping time.
* `MeasureTheory.Submartingale.stoppedValueAtTop_le_condExp_stoppedValueAtTop`:
  `f_L ≤ᵐ μ[f_M | ℱ_L]` for a uniformly integrable submartingale `f`
  and stopping times `L ≤ M`.
* `MeasureTheory.Submartingale.integral_stoppedValueAtTop_mono_of_uniformIntegrable`:
  `∫ f_L ≤ ∫ f_M` under the same hypotheses.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- If `f n ω → g ω` almost everywhere, then the stopped process
`n ↦ f_{τ ∧ n} ω` converges almost everywhere to the stopped value at
`τ` (with the limit `g ω` used on `{τ = ∞}`). -/
private theorem tendsto_stoppedProcess_to_stoppedValueAtTop {g : Ω → ℝ}
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    {τ : Ω → WithTop ℕ} :
    ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedProcess f τ n ω) atTop
      (𝓝 (stoppedValueAtTop f τ ω)) := by
  filter_upwards [hconv] with ω hω
  by_cases hτtop : τ ω = ⊤
  · have hlim : limUnder atTop (fun n => f n ω) = g ω := hω.limUnder_eq
    have hfun : (fun n => stoppedProcess f τ n ω) = fun n => f n ω := by
      funext n
      show f (min ((n : WithTop ℕ)) (τ ω)).untopA ω = f n ω
      rw [hτtop, min_top_right]
      rfl
    rw [hfun]
    have hval : stoppedValueAtTop f τ ω = g ω := by
      show (if τ ω = ⊤ then limUnder atTop (fun n => f n ω)
        else stoppedValue f τ ω) = g ω
      rw [ite_eq_left hτtop, hlim]
    rw [hval]
    exact hω
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hτtop
    have hval : stoppedValueAtTop f τ ω = f k ω := by
      show (if τ ω = ⊤ then limUnder atTop (fun n => f n ω)
        else stoppedValue f τ ω) = f k ω
      rw [ite_eq_right hτtop]
      show f (τ ω).untopA ω = f k ω
      rw [← hk]
      rfl
    rw [hval]
    refine tendsto_atTop_of_eventually_const (i₀ := k) (fun n hn => ?_)
    have hle : τ ω ≤ ((n : WithTop ℕ)) := by
      rw [← hk]
      exact WithTop.coe_le_coe.mpr hn
    have hsp := stoppedProcess_eq_of_ge (u := f) (τ := τ) (i := n) hle
    rw [hsp, ← hk]
    rfl

/-- A sum of two finite `ℝ≥0∞` numbers is finite. -/
private theorem ennreal_add_ne_top {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a + b ≠ ⊤ := by
  rw [ne_eq, ENNReal.add_eq_top]
  exact fun h => h.elim ha hb

omit [IsProbabilityMeasure μ] in
/-- Each term of the predictable part of a process is integrable. -/
private theorem integrable_predictablePart (_hsub : Submartingale f ℱ μ) (n : ℕ) :
    Integrable (predictablePart f ℱ μ n) μ := by
  have hEq : predictablePart f ℱ μ n =
      fun ω => ∑ i ∈ Finset.range n, μ[f (i + 1) - f i | ℱ i] ω := by
    funext ω
    simp [predictablePart, Finset.sum_apply]
  rw [hEq]
  exact integrable_finsetSum _ (fun i _ => integrable_condExp)

/-- The predictable part of a submartingale is itself a submartingale:
its increments are the conditional expectations of the increments of
`f`, which are a.e. nonnegative, and the tower property turns
`μ[∑_{k ∈ [i,j)} μ[Δf_k | ℱ_k] | ℱ_i]` back into a sum of
`μ[Δf_k | ℱ_i] ≥ 0`. -/
private theorem submartingale_predictablePart (hsub : Submartingale f ℱ μ) :
    Submartingale (predictablePart f ℱ μ) ℱ μ := by
  apply submartingale_of_condExp_sub_nonneg stronglyAdapted_predictablePart'
    (integrable_predictablePart hsub)
  intro i j hij
  have hdiff : (predictablePart f ℱ μ j - predictablePart f ℱ μ i) =
      ∑ k ∈ Finset.Ico i j, μ[f (k + 1) - f k | ℱ k] := by
    simp only [predictablePart]
    rw [Finset.sum_Ico_eq_sub (fun k => μ[f (k + 1) - f k | ℱ k]) hij]
  rw [hdiff]
  have hcond : μ[∑ k ∈ Finset.Ico i j, μ[f (k + 1) - f k | ℱ k] | ℱ i] =ᵐ[μ]
      ∑ k ∈ Finset.Ico i j, μ[f (k + 1) - f k | ℱ i] :=
    condExp_finsetSum (s := Finset.Ico i j) (f := fun k => μ[f (k + 1) - f k | ℱ k])
      (fun k _ => integrable_condExp) (ℱ i) |>.trans
        (eventuallyEq_sum fun k hk => condExp_condExp_of_le
          (ℱ.mono (Finset.mem_Ico.mp hk).1) (ℱ.le k))
  have hnonneg : ∀ᵐ ω ∂μ, ∀ k, k ∈ Finset.Ico i j →
      0 ≤ μ[f (k + 1) - f k | ℱ i] ω := by
    rw [ae_all_iff]
    intro k
    by_cases hk : k ∈ Finset.Ico i j
    · have h1 : (0 : Ω → ℝ) ≤ᵐ[μ] μ[f (k + 1) - f k | ℱ k] :=
        hsub.condExp_sub_nonneg (Nat.le_succ k)
      have h2 : μ[(0 : Ω → ℝ) | ℱ i] ≤ᵐ[μ] μ[μ[f (k + 1) - f k | ℱ k] | ℱ i] :=
        condExp_mono (integrable_const (0 : ℝ)) integrable_condExp h1
      rw [condExp_zero] at h2
      have h3 := h2.trans (condExp_condExp_of_le
        (ℱ.mono (Finset.mem_Ico.mp hk).1) (ℱ.le k)).le
      filter_upwards [h3] with ω hω hkmem
      exact hω
    · filter_upwards with ω
      intro hkmem
      exact absurd hkmem hk
  filter_upwards [hcond, hnonneg] with ω hω hωnonneg
  rw [hω, Finset.sum_apply]
  exact Finset.sum_nonneg (fun k hk => hωnonneg k hk)

/-- The integral of the predictable part telescopes:
`∫ A n = ∫ f n - ∫ f 0`, since the martingale part has constant
expectation. -/
private theorem integral_predictablePart (hsub : Submartingale f ℱ μ) (n : ℕ) :
    ∫ ω, predictablePart f ℱ μ n ω ∂μ = ∫ ω, f n ω ∂μ - ∫ ω, f 0 ω ∂μ := by
  have hMt : Martingale (martingalePart f ℱ μ) ℱ μ :=
    martingale_martingalePart hsub.stronglyAdapted (fun k => hsub.integrable k)
  have hMt_int : ∫ ω, martingalePart f ℱ μ n ω ∂μ = ∫ ω, f 0 ω ∂μ := by
    simpa [setIntegral_univ] using
      (hMt.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ).symm
  have hdecomp : martingalePart f ℱ μ n + predictablePart f ℱ μ n = f n :=
    congrFun (martingalePart_add_predictablePart ℱ μ f) n
  have h1 : ∫ ω, (martingalePart f ℱ μ n ω + predictablePart f ℱ μ n ω) ∂μ
      = ∫ ω, f n ω ∂μ := by
    rw [← hdecomp]
    rfl
  rw [integral_add (integrable_martingalePart (fun k => hsub.integrable k) n)
    (integrable_predictablePart hsub n)] at h1
  linarith [h1, hMt_int]

/-- The `L¹` norm of the predictable part is bounded by the uniform
integrability bound of `f` plus `|∫ f 0|`. -/
private theorem eLpNorm_predictablePart_le (hsub : Submartingale f ℱ μ)
    {R : ℝ≥0} (hR : ∀ n, eLpNorm (f n) 1 μ ≤ (R : ℝ≥0∞)) (n : ℕ) :
    eLpNorm (predictablePart f ℱ μ n) 1 μ ≤
      (R : ℝ≥0∞) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ| := by
  have hA_nonneg : ∀ᵐ ω ∂μ, 0 ≤ predictablePart f ℱ μ n ω := by
    filter_upwards [hsub.predictablePart_nonneg] with ω hω
    exact hω n
  have hA_sm : AEStronglyMeasurable (predictablePart f ℱ μ n) μ :=
    (integrable_predictablePart hsub n).aestronglyMeasurable
  have heq : eLpNorm (predictablePart f ℱ μ n) 1 μ
      = ENNReal.ofReal (∫ ω, predictablePart f ℱ μ n ω ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm hA_sm,
      ofReal_integral_eq_lintegral_ofReal (integrable_predictablePart hsub n) hA_nonneg]
    refine lintegral_congr_ae ?_
    filter_upwards [hA_nonneg] with ω hω
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hω]
  rw [heq, integral_predictablePart hsub n]
  calc ENNReal.ofReal (∫ ω, f n ω ∂μ - ∫ ω, f 0 ω ∂μ)
      ≤ ENNReal.ofReal (∫ ω, |f n ω| ∂μ + |∫ ω, f 0 ω ∂μ|) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : ∫ ω, f n ω ∂μ - ∫ ω, f 0 ω ∂μ
            ≤ |∫ ω, f n ω ∂μ| + |∫ ω, f 0 ω ∂μ| := by
          have h1a : ∫ ω, f n ω ∂μ ≤ |∫ ω, f n ω ∂μ| := le_abs_self _
          have h1b : -∫ ω, f 0 ω ∂μ ≤ |∫ ω, f 0 ω ∂μ| := neg_le_abs _
          linarith
        refine h1.trans ?_
        have h2 : |∫ ω, f n ω ∂μ| ≤ ∫ ω, |f n ω| ∂μ :=
          abs_integral_le_integral_abs
        linarith
    _ = ENNReal.ofReal (∫ ω, |f n ω| ∂μ) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ| := by
        rw [ENNReal.ofReal_add (integral_nonneg (fun ω => abs_nonneg _)) (abs_nonneg _)]
    _ ≤ (R : ℝ≥0∞) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ| := by
        apply add_le_add _ le_rfl
        have hfn : ENNReal.ofReal (∫ ω, |f n ω| ∂μ) = eLpNorm (f n) 1 μ := by
          rw [ofReal_integral_eq_lintegral_ofReal (hsub.integrable n).abs
              (Filter.Eventually.of_forall fun ω => abs_nonneg _),
            eLpNorm_one_eq_lintegral_enorm (hsub.integrable n).aestronglyMeasurable]
          refine lintegral_congr_ae ?_
          filter_upwards with ω
          simp [Real.enorm_eq_ofReal_abs]
        rw [hfn]
        exact hR n

/-- A uniform `L¹` bound for the predictable part, in the `ℝ≥0`-coerced
form that `Submartingale.memLp_limitProcess` and
`Submartingale.ae_tendsto_limitProcess` expect. -/
private theorem eLpNorm_predictablePart_le_nnreal (hsub : Submartingale f ℱ μ)
    {R : ℝ≥0} (hR : ∀ n, eLpNorm (f n) 1 μ ≤ (R : ℝ≥0∞)) (n : ℕ) :
    eLpNorm (predictablePart f ℱ μ n) 1 μ ≤
      (((R : ℝ≥0∞) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ|).toNNReal : ℝ≥0∞) := by
  rw [ENNReal.coe_toNNReal
    (ennreal_add_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)]
  exact eLpNorm_predictablePart_le hsub hR n

/-- The limit of the predictable part is integrable: its `L¹` norms are
uniformly bounded, so `Submartingale.memLp_limitProcess` applies. -/
private theorem integrable_limitProcess_predictablePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) :
    Integrable (ℱ.limitProcess (predictablePart f ℱ μ) μ) μ := by
  obtain ⟨R, hR⟩ := hui.2
  exact ((submartingale_predictablePart hsub).memLp_limitProcess
    (fun n => eLpNorm_predictablePart_le_nnreal hsub hR n)).integrable le_rfl

/-- The predictable part of a uniformly integrable submartingale is
uniformly integrable: it is dominated by its integrable limit. -/
private theorem uniformIntegrable_predictablePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) :
    UniformIntegrable (predictablePart f ℱ μ) 1 μ := by
  obtain ⟨R, hR⟩ := hui.2
  set A := predictablePart f ℱ μ
  set Alim := ℱ.limitProcess A μ
  have hAlim_int : Integrable Alim μ := integrable_limitProcess_predictablePart hsub hui
  have hAlim_memLp : MemLp Alim 1 μ := memLp_one_iff_integrable.2 hAlim_int
  have hUI_const : UniformIntegrable (fun _ : ℕ => Alim) 1 μ :=
    uniformIntegrable_const le_rfl ENNReal.one_ne_top hAlim_memLp
  have hle : ∀ n, (‖A n ·‖ₑ) ≤ᵐ[μ] (‖Alim ·‖ₑ) := by
    intro n
    have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (Alim ω)) :=
      (submartingale_predictablePart hsub).ae_tendsto_limitProcess
        (fun m => eLpNorm_predictablePart_le_nnreal hsub hR m)
    have hmono : ∀ᵐ ω ∂μ, Monotone (fun n => A n ω) :=
      hsub.monotone_predictablePart
    filter_upwards [hconv, hmono, hsub.predictablePart_nonneg] with ω hω hmonoω hnnω
    have hleω : A n ω ≤ Alim ω := hmonoω.ge_of_tendsto hω n
    have hnn : 0 ≤ A n ω := hnnω n
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg hnn, abs_of_nonneg (le_trans hnn hleω)]
    exact ENNReal.ofReal_le_ofReal hleω
  refine ⟨(hUI_const.1).ae_mono (fun n => (integrable_predictablePart hsub n).aestronglyMeasurable)
    hle, ?_⟩
  refine ⟨((R : ℝ≥0∞) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ|).toNNReal, fun n => ?_⟩
  rw [ENNReal.coe_toNNReal
    (ennreal_add_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)]
  exact eLpNorm_predictablePart_le hsub hR n

/-- The martingale part of a uniformly integrable submartingale is a
uniformly integrable martingale. -/
private theorem uniformIntegrable_martingalePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) :
    Martingale (martingalePart f ℱ μ) ℱ μ ∧
      UniformIntegrable (martingalePart f ℱ μ) 1 μ := by
  obtain ⟨R, hR⟩ := hui.2
  set A := predictablePart f ℱ μ
  set Mt := martingalePart f ℱ μ
  have hMt_mart : Martingale Mt ℱ μ :=
    martingale_martingalePart hsub.stronglyAdapted (fun k => hsub.integrable k)
  have hA_UI := uniformIntegrable_predictablePart hsub hui
  have hMt_UI : UniformIntegrable Mt 1 μ := by
    have hMt_eq : Mt = f - A := by
      funext n ω
      simp [Mt, A, martingalePart]
    rw [hMt_eq]
    refine ⟨(hui.1).sub (hA_UI.1) le_rfl, ?_⟩
    refine ⟨((R : ℝ≥0∞) + ((R : ℝ≥0∞) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ|)).toNNReal,
      fun n => ?_⟩
    rw [ENNReal.coe_toNNReal (ennreal_add_ne_top ENNReal.coe_ne_top
      (ennreal_add_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top))]
    have hsub_le : eLpNorm ((f - A) n) 1 μ ≤ eLpNorm (f n) 1 μ + eLpNorm (A n) 1 μ := by
      have hEq : (f - A) n = f n + (-A n) := by
        simp only [Pi.sub_apply, sub_eq_add_neg]
      rw [hEq]
      calc eLpNorm (f n + (-A n)) 1 μ
          ≤ eLpNorm (f n) 1 μ + eLpNorm (-A n) 1 μ := eLpNorm_add_le le_rfl
        _ = eLpNorm (f n) 1 μ + eLpNorm (A n) 1 μ := by rw [eLpNorm_neg]
    exact (hsub_le.trans (add_le_add (hR n) (eLpNorm_predictablePart_le hsub hR n)))
  exact ⟨hMt_mart, hMt_UI⟩

omit [IsProbabilityMeasure μ] in
/-- Stopped values split over sums, when both summands converge
almost everywhere. -/
private theorem stoppedValueAtTop_add {g h : ℕ → Ω → ℝ} {G H : Ω → ℝ}
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (G ω)))
    (hh : ∀ᵐ ω ∂μ, Tendsto (fun n => h n ω) atTop (𝓝 (H ω)))
    {τ : Ω → WithTop ℕ} :
    stoppedValueAtTop (g + h) τ =ᵐ[μ] stoppedValueAtTop g τ + stoppedValueAtTop h τ := by
  filter_upwards [hg, hh] with ω hωg hωh
  by_cases hτtop : τ ω = ⊤
  · show (if τ ω = ⊤ then limUnder atTop (fun n => (g + h) n ω)
        else stoppedValue (g + h) τ ω)
      = (if τ ω = ⊤ then limUnder atTop (fun n => g n ω) else stoppedValue g τ ω) +
        (if τ ω = ⊤ then limUnder atTop (fun n => h n ω) else stoppedValue h τ ω)
    simp only [ite_eq_left hτtop]
    have hadd : Tendsto (fun n => (g + h) n ω) atTop (𝓝 (G ω + H ω)) :=
      hωg.add hωh
    rw [hadd.limUnder_eq, hωg.limUnder_eq, hωh.limUnder_eq]
  · show (if τ ω = ⊤ then limUnder atTop (fun n => (g + h) n ω)
        else stoppedValue (g + h) τ ω)
      = (if τ ω = ⊤ then limUnder atTop (fun n => g n ω) else stoppedValue g τ ω) +
        (if τ ω = ⊤ then limUnder atTop (fun n => h n ω) else stoppedValue h τ ω)
    simp only [ite_eq_right hτtop]
    rfl

/-- The stopped value of `f` at any stopping time splits over the Doob
decomposition. -/
private theorem stoppedValueAtTop_decomp (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) {τ : Ω → WithTop ℕ} :
    stoppedValueAtTop f τ =ᵐ[μ] stoppedValueAtTop (martingalePart f ℱ μ) τ +
      stoppedValueAtTop (predictablePart f ℱ μ) τ := by
  obtain ⟨R, hR⟩ := hui.2
  obtain ⟨hMt_mart, hMt_UI⟩ := uniformIntegrable_martingalePart hsub hui
  have hMt_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => martingalePart f ℱ μ n ω) atTop
      (𝓝 (ℱ.limitProcess (martingalePart f ℱ μ) μ ω)) :=
    hMt_mart.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hMt_UI
  have hA_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => predictablePart f ℱ μ n ω) atTop
      (𝓝 (ℱ.limitProcess (predictablePart f ℱ μ) μ ω)) :=
    (submartingale_predictablePart hsub).ae_tendsto_limitProcess
      (fun m => eLpNorm_predictablePart_le_nnreal hsub hR m)
  have h := stoppedValueAtTop_add hMt_conv hA_conv (τ := τ)
  rwa [martingalePart_add_predictablePart ℱ μ f] at h

/-- The stopped value of the predictable part at any stopping time is
integrable: it is dominated by its integrable limit. -/
private theorem integrable_stoppedValueAtTop_predictablePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    Integrable (stoppedValueAtTop (predictablePart f ℱ μ) τ) μ := by
  obtain ⟨R, hR⟩ := hui.2
  set A := predictablePart f ℱ μ
  set Alim := ℱ.limitProcess A μ
  have hAlim_int : Integrable Alim μ := integrable_limitProcess_predictablePart hsub hui
  have hA_sub : Submartingale A ℱ μ := submartingale_predictablePart hsub
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (Alim ω)) :=
    hA_sub.ae_tendsto_limitProcess (fun m => eLpNorm_predictablePart_le_nnreal hsub hR m)
  have hstop_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedProcess A τ n ω) atTop
      (𝓝 (stoppedValueAtTop A τ ω)) :=
    tendsto_stoppedProcess_to_stoppedValueAtTop hconv
  have hle : ∀ᵐ ω ∂μ, ‖stoppedValueAtTop A τ ω‖ ≤ ‖Alim ω‖ := by
    filter_upwards [hconv, hstop_conv, hsub.monotone_predictablePart,
      hsub.predictablePart_nonneg] with ω hω hstopω hmonoω hnnω
    have hnn' : 0 ≤ stoppedValueAtTop A τ ω :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hstopω
        (Filter.Eventually.of_forall fun n => by
          show 0 ≤ A (min (n : WithTop ℕ) (τ ω)).untopA ω
          exact hnnω _)
    have hle' : stoppedValueAtTop A τ ω ≤ Alim ω :=
      le_of_tendsto_of_tendsto hstopω tendsto_const_nhds
        (Filter.Eventually.of_forall fun n => by
          show A (min (n : WithTop ℕ) (τ ω)).untopA ω ≤ Alim ω
          exact hmonoω.ge_of_tendsto hω _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn', Real.norm_eq_abs,
      abs_of_nonneg (le_trans hnn' hle')]
    exact hle'
  have hsm : AEStronglyMeasurable (stoppedValueAtTop A τ) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (stronglyAdapted_predictablePart'.stronglyMeasurable_stoppedProcess_of_discrete
        hτ n).aestronglyMeasurable)
      hstop_conv
  exact (hAlim_int.norm).mono' hsm hle

/-- The stopped value of the martingale part at any stopping time is
integrable: it is a.e. equal to a conditional expectation. -/
private theorem integrable_stoppedValueAtTop_martingalePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    Integrable (stoppedValueAtTop (martingalePart f ℱ μ) τ) μ := by
  obtain ⟨hMt_mart, hMt_UI⟩ := uniformIntegrable_martingalePart hsub hui
  have hEq := hMt_mart.stoppedValueAtTop_ae_eq_condExp_limitProcess hMt_UI hτ
  exact integrable_condExp.congr hEq.symm

/-- The predictable part satisfies the conditional optional stopping
inequality: `A_L ≤ᵐ μ[A_M | ℱ_L]`. The proof works with the stopped
process `n ↦ A_{L ∧ n}`, each term of which is `ℱ_L`-measurable, and
passes to the limit. -/
private theorem predictablePart_stoppedValueAtTop_le_condExp (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    stoppedValueAtTop (predictablePart f ℱ μ) L ≤ᵐ[μ]
      μ[stoppedValueAtTop (predictablePart f ℱ μ) M | hL.measurableSpace] := by
  obtain ⟨R, hR⟩ := hui.2
  set A := predictablePart f ℱ μ
  set Alim := ℱ.limitProcess A μ
  have hAlim_int : Integrable Alim μ := integrable_limitProcess_predictablePart hsub hui
  have hA_sub : Submartingale A ℱ μ := submartingale_predictablePart hsub
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (Alim ω)) :=
    hA_sub.ae_tendsto_limitProcess (fun m => eLpNorm_predictablePart_le_nnreal hsub hR m)
  have hgood : ∀ᵐ ω ∂μ, Monotone (fun n => A n ω) ∧ (∀ n, 0 ≤ A n ω) ∧
      Tendsto (fun n => A n ω) atTop (𝓝 (Alim ω)) := by
    filter_upwards [hsub.monotone_predictablePart, hsub.predictablePart_nonneg, hconv]
      with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- Pointwise bounds on the good set.
  have hbound : ∀ᵐ ω ∂μ, ∀ n, stoppedProcess A L n ω ≤ stoppedProcess A M n ω ∧
      stoppedProcess A M n ω ≤ stoppedValueAtTop A M ω ∧
      stoppedProcess A L n ω ≤ Alim ω ∧
      stoppedValueAtTop A M ω ≤ Alim ω := by
    filter_upwards [hgood] with ω ⟨hmonoω, hnnω, hlimω⟩ n
    have hleAlim : ∀ m, A m ω ≤ Alim ω := fun m => hmonoω.ge_of_tendsto hlimω m
    have hub : (min (↑n : WithTop ℕ) (L ω)).untopA ≤
        (min (↑n : WithTop ℕ) (M ω)).untopA :=
      WithTop.untopA_mono
        (ne_top_of_le_ne_top (by simp) (min_le_left _ _))
        (min_le_min le_rfl (hLM ω))
    have hLM_le : stoppedProcess A L n ω ≤ stoppedProcess A M n ω := by
      show A (min (↑n : WithTop ℕ) (L ω)).untopA ω ≤
        A (min (↑n : WithTop ℕ) (M ω)).untopA ω
      exact hmonoω hub
    have hM_n_le : stoppedProcess A M n ω ≤ stoppedValueAtTop A M ω := by
      by_cases htop : M ω = ⊤
      · have hval : stoppedValueAtTop A M ω = Alim ω := by
          show (if M ω = ⊤ then limUnder atTop (fun n => A n ω)
            else stoppedValue A M ω) = Alim ω
          rw [ite_eq_left htop]
          exact hlimω.limUnder_eq
        rw [hval]
        show A (min (↑n : WithTop ℕ) (M ω)).untopA ω ≤ Alim ω
        exact hleAlim _
      · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
        have hval : stoppedValueAtTop A M ω = A k ω := by
          show (if M ω = ⊤ then limUnder atTop (fun n => A n ω)
            else stoppedValue A M ω) = A k ω
          rw [ite_eq_right htop]
          show A (M ω).untopA ω = A k ω
          rw [← hk]
          rfl
        rw [hval]
        show A (min (↑n : WithTop ℕ) (M ω)).untopA ω ≤ A k ω
        apply hmonoω
        rw [WithTop.untopA_le_iff (ne_top_of_le_ne_top (by simp) (min_le_left _ _))]
        rw [← hk]
        exact min_le_right _ _
    have hL_le : stoppedProcess A L n ω ≤ Alim ω := by
      show A (min (↑n : WithTop ℕ) (L ω)).untopA ω ≤ Alim ω
      exact hleAlim _
    have hM_le_Alim : stoppedValueAtTop A M ω ≤ Alim ω := by
      by_cases htop : M ω = ⊤
      · have hval : stoppedValueAtTop A M ω = Alim ω := by
          show (if M ω = ⊤ then limUnder atTop (fun n => A n ω)
            else stoppedValue A M ω) = Alim ω
          rw [ite_eq_left htop]
          exact hlimω.limUnder_eq
        rw [hval]
      · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
        have hval : stoppedValueAtTop A M ω = A k ω := by
          show (if M ω = ⊤ then limUnder atTop (fun n => A n ω)
            else stoppedValue A M ω) = A k ω
          rw [ite_eq_right htop]
          show A (M ω).untopA ω = A k ω
          rw [← hk]
          rfl
        rw [hval]
        exact hleAlim k
    exact ⟨hLM_le, hM_n_le, hL_le, hM_le_Alim⟩
  -- Each term of the stopped process at `L` is `ℱ_L`-measurable and
  -- integrable, and bounded by the conditional expectation of the
  -- right-hand side.
  have hA_M_int : Integrable (stoppedValueAtTop A M) μ :=
    integrable_stoppedValueAtTop_predictablePart hsub hui hM
  have hstep : ∀ n, stoppedProcess A L n ≤ᵐ[μ]
      μ[stoppedValueAtTop A M | hL.measurableSpace] := by
    intro n
    have hσ : IsStoppingTime ℱ (fun ω => min (↑n : WithTop ℕ) (L ω)) :=
      (isStoppingTime_const ℱ n).min hL
    have hmeas : StronglyMeasurable[hL.measurableSpace] (stoppedProcess A L n) := by
      have h1 : Measurable[hσ.measurableSpace] (stoppedProcess A L n) := by
        have h2 : Measurable[hσ.measurableSpace]
            (stoppedValue A (fun ω => min (↑n : WithTop ℕ) (L ω))) :=
          measurable_stoppedValue
            stronglyAdapted_predictablePart'.isStronglyProgressive_of_discrete hσ
        exact h2
      have h3 : StronglyMeasurable[hσ.measurableSpace] (stoppedProcess A L n) :=
        h1.stronglyMeasurable
      exact h3.mono (IsStoppingTime.measurableSpace_mono hσ hL (fun ω => min_le_right _ _))
    have hint_L : Integrable (stoppedProcess A L n) μ := by
      have hae : AEStronglyMeasurable (stoppedProcess A L n) μ :=
        (hmeas.mono hL.measurableSpace_le).aestronglyMeasurable
      apply (hAlim_int.norm).mono' hae
      filter_upwards [hbound, hgood] with ω hω hgoodω
      obtain ⟨-, hnnω, -⟩ := hgoodω
      have h0 : 0 ≤ stoppedProcess A L n ω := by
        show 0 ≤ A (min (↑n : WithTop ℕ) (L ω)).untopA ω
        exact hnnω _
      rw [Real.norm_eq_abs, abs_of_nonneg h0, Real.norm_eq_abs,
        abs_of_nonneg (le_trans h0 (hω n).2.2.1)]
      exact (hω n).2.2.1
    have hint_M : Integrable (stoppedProcess A M n) μ := by
      have hae : AEStronglyMeasurable (stoppedProcess A M n) μ :=
        (stronglyAdapted_predictablePart'.stronglyMeasurable_stoppedProcess_of_discrete
          hM n).aestronglyMeasurable
      apply (hAlim_int.norm).mono' hae
      filter_upwards [hbound, hgood] with ω hω hgoodω
      obtain ⟨-, hnnω, -⟩ := hgoodω
      have h0 : 0 ≤ stoppedProcess A M n ω := by
        show 0 ≤ A (min (↑n : WithTop ℕ) (M ω)).untopA ω
        exact hnnω _
      rw [Real.norm_eq_abs, abs_of_nonneg h0, Real.norm_eq_abs,
        abs_of_nonneg (le_trans h0 ((hω n).2.1.trans (hω n).2.2.2))]
      exact (hω n).2.1.trans (hω n).2.2.2
    have h1 : stoppedProcess A L n =ᵐ[μ]
        μ[stoppedProcess A L n | hL.measurableSpace] :=
      Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable hL.measurableSpace_le hmeas hint_L).symm
    have h2 : μ[stoppedProcess A L n | hL.measurableSpace] ≤ᵐ[μ]
        μ[stoppedProcess A M n | hL.measurableSpace] :=
      condExp_mono hint_L hint_M (by
        filter_upwards [hbound] with ω hω
        exact (hω n).1)
    have h3 : μ[stoppedProcess A M n | hL.measurableSpace] ≤ᵐ[μ]
        μ[stoppedValueAtTop A M | hL.measurableSpace] :=
      condExp_mono hint_M hA_M_int (by
        filter_upwards [hbound] with ω hω
        exact (hω n).2.1)
    exact h1.le.trans (h2.trans h3)
  -- Pass to the limit in `n`.
  have hper : ∀ᵐ ω ∂μ, ∀ n, stoppedProcess A L n ω ≤
      (μ[stoppedValueAtTop A M | hL.measurableSpace]) ω :=
    ae_all_iff.mpr hstep
  filter_upwards [tendsto_stoppedProcess_to_stoppedValueAtTop hconv, hper]
    with ω hω hperω
  exact le_of_tendsto_of_tendsto hω tendsto_const_nhds (Filter.Eventually.of_forall hperω)

/-- **Conditional optional stopping for uniformly integrable
submartingales.** For stopping times `L ≤ M` (possibly infinite),
`f_L ≤ᵐ μ[f_M | ℱ_L]`. -/
theorem Submartingale.stoppedValueAtTop_le_condExp_stoppedValueAtTop
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    stoppedValueAtTop f L ≤ᵐ[μ] μ[stoppedValueAtTop f M | hL.measurableSpace] := by
  obtain ⟨hMt_mart, hMt_UI⟩ := uniformIntegrable_martingalePart hsub hui
  have hAdd_L := stoppedValueAtTop_decomp hsub hui (τ := L)
  have hAdd_M := stoppedValueAtTop_decomp hsub hui (τ := M)
  have hMt_cond :=
    hMt_mart.stoppedValueAtTop_ae_eq_condExp_stoppedValueAtTop
      (hMt_mart.uniformIntegrable_stoppedProcess_of_uniformIntegrable hMt_UI M hM) hL hM hLM
  have hA_cond := predictablePart_stoppedValueAtTop_le_condExp hsub hui hL hM hLM
  have hsum : μ[stoppedValueAtTop (martingalePart f ℱ μ) M | hL.measurableSpace] +
        μ[stoppedValueAtTop (predictablePart f ℱ μ) M | hL.measurableSpace] =ᵐ[μ]
      μ[stoppedValueAtTop (martingalePart f ℱ μ) M +
        stoppedValueAtTop (predictablePart f ℱ μ) M | hL.measurableSpace] :=
    (condExp_add (integrable_stoppedValueAtTop_martingalePart hsub hui hM)
      (integrable_stoppedValueAtTop_predictablePart hsub hui hM) _).symm
  exact hAdd_L.le.trans
    ((hMt_cond.le.add_le_add hA_cond).trans
      (hsum.le.trans (condExp_congr_ae hAdd_M.symm).le))

/-- **Expectation form of conditional optional stopping for uniformly
integrable submartingales.** For stopping times `L ≤ M` (possibly
infinite), `∫ f_L ≤ ∫ f_M`. -/
theorem Submartingale.integral_stoppedValueAtTop_mono_of_uniformIntegrable
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    ∫ ω, stoppedValueAtTop f L ω ∂μ ≤ ∫ ω, stoppedValueAtTop f M ω ∂μ := by
  have hcond := hsub.stoppedValueAtTop_le_condExp_stoppedValueAtTop hui hL hM hLM
  have hIntL : Integrable (stoppedValueAtTop f L) μ := by
    have hAdd := stoppedValueAtTop_decomp hsub hui (τ := L)
    exact ((integrable_stoppedValueAtTop_martingalePart hsub hui hL).add
      (integrable_stoppedValueAtTop_predictablePart hsub hui hL)).congr hAdd.symm
  have hIntM : Integrable (stoppedValueAtTop f M) μ := by
    have hAdd := stoppedValueAtTop_decomp hsub hui (τ := M)
    exact ((integrable_stoppedValueAtTop_martingalePart hsub hui hM).add
      (integrable_stoppedValueAtTop_predictablePart hsub hui hM)).congr hAdd.symm
  calc ∫ ω, stoppedValueAtTop f L ω ∂μ
      ≤ ∫ ω, (μ[stoppedValueAtTop f M | hL.measurableSpace]) ω ∂μ :=
        integral_mono_ae hIntL integrable_condExp hcond
    _ = ∫ ω, stoppedValueAtTop f M ω ∂μ :=
        integral_condExp hL.measurableSpace_le


end MeasureTheory
