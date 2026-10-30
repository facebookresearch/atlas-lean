/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.PSeries
public import MathlibExt.Probability.KolmogorovThreeSeries

import MathlibExt.Probability.PaleyZygmund
import MathlibExt.Probability.ThreeSeriesTailProb

/-!
# Kolmogorov three-series necessity, series (2)–(3)

The necessity direction of Kolmogorov's three-series theorem: if the
partial sums of an independent sequence `Xₙ` of real random variables
converge almost surely, then for every `A > 0` the truncations
`Yₙ = Xₙ · 1_{|Xₙ| ≤ A}` satisfy

* (series 2, corrected) the partial sums of the means `∑ₖ E[Yₖ]` converge
  (to some limit), and
* (series 3) the variances are summable: `Summable (fun n => Var[Yₙ])`.

## Source and statement correction

This ports the necessity direction from
`v1/Atlas/TheoryOfProbability/code/KolmogorovThreeSeries.lean`. There the
necessity rests on `summable_mean_and_variance_of_ae_tendsto_ax`, which is
left **unproved** in v1 — and its means half is **false as stated**.
Lean's `Summable` is unconditional convergence, and
`Summable.abs : Summable f → Summable (fun x => |f x|)` forces absolute
convergence. The deterministic sequence `X k = (-1)^k / (k + 1)` on any
probability space is a counterexample: its partial sums converge
(alternating harmonic series), its truncations at `A = 1` are the sequence
itself, its variances are all `0` (hence summable), but the means
`(-1)^k / (k + 1)` are not `Summable` — absolute summability would give
summability of the harmonic series. The theorem
`summable_mean_necessity_false` below formalizes exactly this
counterexample. What is true — and proved here — is that the partial sums
of the means *converge* (series convergence, not `Summable`), which is the
form the three-series theorem actually needs.

## Scope

* The variance half is proved by symmetrization: on the product space,
  the symmetrized variables `Zₙ(ω, ω') = Yₙ ω - Yₙ ω'` are centered and
  bounded; if their variances were not summable, Paley–Zygmund plus a
  fourth-moment bound (proved by induction for independent centered
  bounded sums, including the `E[S²Z²] = E[S²]E[Z²]` cross term) would
  give a uniform lower bound on block-tail probabilities, contradicting
  convergence in measure.
* The mean half centers the sequence and bounds its partial sums in `L¹`
  using the total variance. The canonical
  `ProbabilityTheory.ae_tendsto_sum_of_indep_centered_L1bdd` gives a.s.
  convergence; the mean partial sums are then the difference of two
  convergent series at a single sample point.
* Series (1) — summability of the tail probabilities
  `∑'ₙ μ {A < |Xₙ|}` — uses the public theorem
  `ProbabilityTheory.summable_tail_prob_of_ae_tendsto` in
  `MathlibExt/Probability/ThreeSeriesTailProb.lean`.
  The convergence-transfer helpers and the canonical `truncatedRV`
  come from `MathlibExt/Probability/KolmogorovThreeSeries.lean`.
  The truncation properties are added to that canonical API.

## Relation to Mathlib

The variance ingredients (`variance_eq_sub`, `IndepFun.variance_sum`) are
Mathlib. Centered convergence and its square-integral-to-`L¹` bound reuse
the canonical `KolmogorovThreeSeries` API; the symmetrization argument,
the fourth-moment induction, and the assembly are new.
-/

@[expose] public section

open MeasureTheory Filter Topology ProbabilityTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

namespace MathlibExt.Probability.ThreeSeriesNecessity

open ProbabilityTheory.KolmogorovThreeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The pair of the `n`-th coordinates of two independent copies. -/
def pairRV (Y : ℕ → Ω → ℝ) (n : ℕ) : Ω × Ω → ℝ × ℝ :=
  fun p => (Y n p.1, Y n p.2)

/-- The symmetrized variable `Z n (ω, ω') = Y n ω - Y n ω'`. -/
def symmRV (Y : ℕ → Ω → ℝ) (n : ℕ) : Ω × Ω → ℝ :=
  (fun p : ℝ × ℝ => p.1 - p.2) ∘ pairRV Y n

theorem measurable_pairRV {Y : ℕ → Ω → ℝ} (hY : ∀ n, Measurable (Y n)) (n : ℕ) :
    Measurable (pairRV Y n) :=
  Measurable.prodMk ((hY n).comp measurable_fst) ((hY n).comp measurable_snd)

theorem measurable_symmRV {Y : ℕ → Ω → ℝ} (hY : ∀ n, Measurable (Y n)) (n : ℕ) :
    Measurable (symmRV Y n) :=
  (measurable_fst.sub measurable_snd).comp (measurable_pairRV hY n)

theorem iIndepFun_pairRV {Y : ℕ → Ω → ℝ} (hY : ∀ n, Measurable (Y n))
    (hYindep : iIndepFun Y μ) : iIndepFun (pairRV Y) (μ.prod μ) := by
  classical
  let π : ℕ → Set (Set (Ω × Ω)) := fun n =>
    {s | ∃ B C : Set ℝ, MeasurableSet B ∧ MeasurableSet C ∧ s = pairRV Y n ⁻¹' (B ×ˢ C)}
  have hpi : ∀ n, IsPiSystem (π n) := by
    intro n s hs t ht _hne
    obtain ⟨B₁, C₁, hB₁, hC₁, rfl⟩ := hs
    obtain ⟨B₂, C₂, hB₂, hC₂, rfl⟩ := ht
    exact ⟨B₁ ∩ B₂, C₁ ∩ C₂, hB₁.inter hB₂, hC₁.inter hC₂, by
      rw [← Set.preimage_inter, ← Set.prod_inter_prod]⟩
  have hgen : ∀ n, MeasurableSpace.comap (pairRV Y n) (inferInstance : MeasurableSpace (ℝ × ℝ)) =
      generateFrom (π n) := by
    intro n
    have hrect : (inferInstance : MeasurableSpace (ℝ × ℝ)) =
        generateFrom (Set.image2 (· ×ˢ ·) {s : Set ℝ | MeasurableSet s} {t : Set ℝ | MeasurableSet t}) :=
      generateFrom_prod.symm
    have h2 : MeasurableSpace.comap (pairRV Y n) (inferInstance : MeasurableSpace (ℝ × ℝ)) =
        MeasurableSpace.comap (pairRV Y n)
          (generateFrom (Set.image2 (· ×ˢ ·) {s : Set ℝ | MeasurableSet s} {t : Set ℝ | MeasurableSet t})) := by
      rw [hrect]
    rw [h2, MeasurableSpace.comap_generateFrom]
    congr 1
    ext s
    simp only [π, Set.mem_image, Set.mem_image2, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ⟨B, hB, C, hC, rfl⟩, rfl⟩
      exact ⟨B, C, hB, hC, rfl⟩
    · rintro ⟨B, C, hB, hC, rfl⟩
      exact ⟨B ×ˢ C, ⟨B, hB, C, hC, rfl⟩, rfl⟩
  have hle : ∀ n, MeasurableSpace.comap (pairRV Y n) (inferInstance : MeasurableSpace (ℝ × ℝ))
      ≤ (inferInstance : MeasurableSpace (Ω × Ω)) := by
    intro n
    exact (measurable_iff_comap_le (f := pairRV Y n)
      (m₁ := (inferInstance : MeasurableSpace (Ω × Ω)))
      (m₂ := (inferInstance : MeasurableSpace (ℝ × ℝ)))).mp (measurable_pairRV hY n)
  have hind : iIndepSets π (μ.prod μ) := by
    rw [iIndepSets_iff]
    intro s f hf
    have hchoose : ∀ i, ∃ B C : Set ℝ, MeasurableSet B ∧ MeasurableSet C ∧
        (i ∈ s → f i = pairRV Y i ⁻¹' (B ×ˢ C)) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨B, C, hB, hC, hEq⟩ := hf i hi
        exact ⟨B, C, hB, hC, fun _ => hEq⟩
      · exact ⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty, fun h => (hi h).elim⟩
    choose B C hB hC hfB using hchoose
    have hInter : (⋂ i ∈ s, f i) = (⋂ i ∈ s, Y i ⁻¹' B i) ×ˢ (⋂ i ∈ s, Y i ⁻¹' C i) := by
      ext ⟨a, b⟩
      simp only [Set.mem_iInter, Set.mem_prod, Set.mem_preimage]
      constructor
      · intro h
        constructor
        · intro i hi
          exact (Set.mem_prod.mp (hfB i hi ▸ h i hi)).1
        · intro i hi
          exact (Set.mem_prod.mp (hfB i hi ▸ h i hi)).2
      · rintro ⟨h1, h2⟩ i hi
        rw [hfB i hi]
        exact Set.mem_prod.mpr ⟨h1 i hi, h2 i hi⟩
    rw [hInter, Measure.prod_prod,
      hYindep.measure_inter_preimage_eq_mul s (fun i _ => hB i),
      hYindep.measure_inter_preimage_eq_mul s (fun i _ => hC i),
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hfB i hi]
    rw [show pairRV Y i ⁻¹' (B i ×ˢ C i) = (Y i ⁻¹' B i) ×ˢ (Y i ⁻¹' C i) from by
      ext p; exact Iff.rfl]
    rw [Measure.prod_prod]
  have hIndep : iIndep (fun n => MeasurableSpace.comap (pairRV Y n) (inferInstance : MeasurableSpace (ℝ × ℝ))) (μ.prod μ) :=
    iIndepSets.iIndep hle π hpi (fun n => hgen n) hind
  exact (iIndepFun_iff_iIndep _ _ _).mpr hIndep

theorem iIndepFun_symmRV {Y : ℕ → Ω → ℝ} (hY : ∀ n, Measurable (Y n))
    (hYindep : iIndepFun Y μ) : iIndepFun (symmRV Y) (μ.prod μ) := by
  have h := iIndepFun_pairRV hY hYindep
  exact h.comp (fun _ p => p.1 - p.2) (fun _ => measurable_fst.sub measurable_snd)


/-- Paley–Zygmund lower bound for a real random variable: if `E[S²] ≥ v > 1/4`
and `E[S⁴] < ∞`, then `P(|S| > 1/2) ≥ (v - 1/4)² / E[S⁴]`. -/
private theorem paley_zygmund_measure_abs_gt_half {S : Ω → ℝ}
    (hSmeas : Measurable S)
    (_hS2 : Integrable (fun ω => (S ω) ^ 2) μ)
    (hS4 : Integrable (fun ω => (S ω) ^ 4) μ)
    {v : ℝ} (hv : 1 / 4 < v) (hvS : v ≤ ∫ ω, (S ω) ^ 2 ∂μ) :
    (v - 1 / 4) ^ 2 ≤ (∫ ω, (S ω) ^ 4 ∂μ) * (μ {ω | (1:ℝ) / 2 < |S ω|}).toReal := by
  let m := ∫ ω, (S ω) ^ 2 ∂μ
  have hm : 0 < m := by
    dsimp [m]
    linarith [hv, hvS]
  have hZ2 : MemLp (fun ω => (S ω) ^ 2) 2 μ :=
    (memLp_two_iff_integrable_sq (hSmeas.pow_const 2).aestronglyMeasurable).mpr
      (hS4.congr (ae_of_all μ fun ω => by ring))
  have hθ0 : 0 ≤ (1 / 4 : ℝ) / m := div_nonneg (by norm_num) hm.le
  have hθ1 : (1 / 4 : ℝ) / m ≤ 1 := by
    apply (div_le_iff₀ hm).mpr
    simpa only [one_mul] using hv.le.trans hvS
  have hθm : ((1 / 4 : ℝ) / m) * m = 1 / 4 := div_mul_cancel₀ _ hm.ne'
  have hPZ := ProbabilityTheory.paley_zygmund (Z := fun ω => (S ω) ^ 2)
    (θ := (1 / 4 : ℝ) / m) (ae_of_all μ fun ω => sq_nonneg (S ω)) hZ2 hθ0 hθ1
  change (1 - (1 / 4 : ℝ) / m) ^ 2 * m ^ 2 ≤
    (∫ ω, ((S ω) ^ 2) ^ 2 ∂μ) *
      μ.real {ω | ((1 / 4 : ℝ) / m) * m < (S ω) ^ 2} at hPZ
  have hleft : (1 - (1 / 4 : ℝ) / m) ^ 2 * m ^ 2 = (m - 1 / 4) ^ 2 := by
    rw [← mul_pow, sub_mul, one_mul, hθm]
  have hfour : (∫ ω, ((S ω) ^ 2) ^ 2 ∂μ) = ∫ ω, (S ω) ^ 4 ∂μ :=
    integral_congr_ae (ae_of_all μ fun ω => by ring)
  have hevent : {ω | (1 / 4 : ℝ) < (S ω) ^ 2} =
      {ω | (1 / 2 : ℝ) < |S ω|} := by
    ext ω
    change (1 / 4 : ℝ) < (S ω) ^ 2 ↔ (1 / 2 : ℝ) < |S ω|
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, sq_lt_sq,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [hleft, hθm, hfour, hevent] at hPZ
  have hmono : (v - 1 / 4) ^ 2 ≤ (m - 1 / 4) ^ 2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hv.le) (sub_le_sub_right hvS _) 2
  exact hmono.trans hPZ



theorem integrable_of_measurable_abs_le {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable (max C 0) (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact (hC ω).trans (le_max_left _ _))

omit [IsProbabilityMeasure μ] in
/-- If `f` and `g` are independent, the expectation of a product of functions of
`f` and `g` factors. -/
theorem integral_mul_of_indep_comp {f g : Ω → ℝ} (h : IndepFun f g μ)
    {φ ψ : ℝ → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hf : AEStronglyMeasurable (φ ∘ f) μ) (hg : AEStronglyMeasurable (ψ ∘ g) μ) :
    ∫ ω, φ (f ω) * ψ (g ω) ∂μ = (∫ ω, φ (f ω) ∂μ) * (∫ ω, ψ (g ω) ∂μ) := by
  have h' := (h.comp hφ hψ).integral_fun_mul_eq_mul_integral hf hg
  simpa only [Function.comp_apply] using h'

/-- Fourth-moment induction for sums of independent centered bounded random
variables: `E[S⁴] ≤ 3 E[S²]² + B² E[S²]`, together with the variance-of-sum
identity and `E[S] = 0`. -/
theorem integral_pow_four_le {Z : ℕ → Ω → ℝ} (hZmeas : ∀ n, Measurable (Z n))
    (hZindep : iIndepFun Z μ) {B : ℝ} (hB : 0 ≤ B) (hZbdd : ∀ n ω, |Z n ω| ≤ B)
    (hZmean : ∀ n, ∫ ω, Z n ω ∂μ = 0) {m n : ℕ} (hmn : m ≤ n) :
    (∫ ω, (∑ k ∈ Finset.Ico m n, Z k ω) ^ 4 ∂μ ≤
      3 * (∫ ω, (∑ k ∈ Finset.Ico m n, Z k ω) ^ 2 ∂μ) ^ 2 +
        B ^ 2 * (∫ ω, (∑ k ∈ Finset.Ico m n, Z k ω) ^ 2 ∂μ)) ∧
    (∫ ω, (∑ k ∈ Finset.Ico m n, Z k ω) ^ 2 ∂μ =
      ∑ k ∈ Finset.Ico m n, ∫ ω, (Z k ω) ^ 2 ∂μ) ∧
    (∫ ω, (∑ k ∈ Finset.Ico m n, Z k ω) ∂μ = 0) := by
  induction n, hmn using Nat.le_induction with
  | base =>
    simp
  | succ n hmn ih =>
    obtain ⟨h4, h2, h0⟩ := ih
    -- Notation for the partial sum up to `n` and the next increment.
    set S : Ω → ℝ := fun ω => ∑ k ∈ Finset.Ico m n, Z k ω with hSdef
    have hSmeas : Measurable S := by
      apply Finset.measurable_sum
      intro k _
      exact hZmeas k
    have hSbound : ∀ ω, |S ω| ≤ (n - m : ℝ) * B := by
      intro ω
      calc |S ω| ≤ ∑ k ∈ Finset.Ico m n, |Z k ω| := by
            apply Finset.abs_sum_le_sum_abs
        _ ≤ (Finset.Ico m n).card • B := by
            apply Finset.sum_le_card_nsmul
            intro k _
            exact hZbdd k ω
        _ = (n - m : ℝ) * B := by
            rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hmn]
    have hInd : IndepFun S (Z n) μ := by
      have h := hZindep.indepFun_finsetSum_of_notMem (s := Finset.Ico m n) (i := n) hZmeas
        (by simp [Finset.mem_Ico])
      have hfun : (∑ j ∈ Finset.Ico m n, Z j) = (fun ω => ∑ k ∈ Finset.Ico m n, Z k ω) := by
        funext ω; exact Finset.sum_apply _ _ _
      rw [hfun, ← hSdef] at h
      exact h
    -- Integral identities for the step.
    have hSZ : ∫ ω, S ω * Z n ω ∂μ = 0 := by
      have h := integral_mul_of_indep_comp hInd measurable_id measurable_id
        hSmeas.aestronglyMeasurable (hZmeas n).aestronglyMeasurable
      simp only [id_eq] at h
      rw [h, h0, hZmean n]
      simp
    have hS3Z : ∫ ω, (S ω) ^ 3 * Z n ω ∂μ = 0 := by
      have h := integral_mul_of_indep_comp hInd (by fun_prop : Measurable (fun x : ℝ => x ^ 3)) measurable_id
        ((by fun_prop : Measurable (fun x : ℝ => x ^ 3)).comp hSmeas).aestronglyMeasurable
        (hZmeas n).aestronglyMeasurable
      simp only [id_eq] at h
      rw [h, hZmean n]
      simp
    have hS2Z2 : ∫ ω, (S ω) ^ 2 * (Z n ω) ^ 2 ∂μ =
        (∫ ω, (S ω) ^ 2 ∂μ) * (∫ ω, (Z n ω) ^ 2 ∂μ) := by
      exact integral_mul_of_indep_comp hInd (by fun_prop : Measurable (fun x : ℝ => x ^ 2)) (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
        ((by fun_prop : Measurable (fun x : ℝ => x ^ 2)).comp hSmeas).aestronglyMeasurable
        ((by fun_prop : Measurable (fun x : ℝ => x ^ 2)).comp (hZmeas n)).aestronglyMeasurable
    have hSZ3 : ∫ ω, S ω * (Z n ω) ^ 3 ∂μ = 0 := by
      have h := integral_mul_of_indep_comp hInd measurable_id (by fun_prop : Measurable (fun x : ℝ => x ^ 3))
        hSmeas.aestronglyMeasurable
        ((by fun_prop : Measurable (fun x : ℝ => x ^ 3)).comp (hZmeas n)).aestronglyMeasurable
      simp only [id_eq] at h
      rw [h, h0]
      simp
    have hZ4le : ∫ ω, (Z n ω) ^ 4 ∂μ ≤ B ^ 2 * (∫ ω, (Z n ω) ^ 2 ∂μ) := by
      have hpoint : ∀ ω, (Z n ω) ^ 4 ≤ B ^ 2 * (Z n ω) ^ 2 := by
        intro ω
        have h1 : (Z n ω) ^ 2 ≤ B ^ 2 := by
          rw [← sq_abs (Z n ω)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hZbdd n ω) 2
        calc (Z n ω) ^ 4 = (Z n ω) ^ 2 * (Z n ω) ^ 2 := by ring
          _ ≤ B ^ 2 * (Z n ω) ^ 2 := by
              apply mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      have hI1 : Integrable (fun ω => (Z n ω) ^ 4) μ :=
        integrable_of_measurable_abs_le ((hZmeas n).pow_const 4) (fun ω => by
          have : |(Z n ω) ^ 4| ≤ B ^ 4 := by
            rw [abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) (hZbdd n ω) 4
          exact this)
      have hI2 : Integrable (fun ω => B ^ 2 * (Z n ω) ^ 2) μ :=
        (integrable_of_measurable_abs_le ((hZmeas n).pow_const 2) (fun ω => by
          have : |(Z n ω) ^ 2| ≤ B ^ 2 := by
            rw [abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) (hZbdd n ω) 2
          exact this)).const_mul _
      calc ∫ ω, (Z n ω) ^ 4 ∂μ ≤ ∫ ω, B ^ 2 * (Z n ω) ^ 2 ∂μ :=
            integral_mono_ae hI1 hI2 (Filter.Eventually.of_forall hpoint)
        _ = B ^ 2 * (∫ ω, (Z n ω) ^ 2 ∂μ) := integral_const_mul _ _
    -- The three conclusions for `n + 1`.
    have hNB : 0 ≤ (n - m : ℝ) * B :=
      mul_nonneg (by exact_mod_cast Nat.zero_le _) hB
    have hIntS : Integrable S μ :=
      integrable_of_measurable_abs_le hSmeas (fun ω => hSbound ω)
    have hIntZ : Integrable (Z n) μ :=
      integrable_of_measurable_abs_le (hZmeas n) (fun ω => hZbdd n ω)
    have hIntS2 : Integrable (fun ω => (S ω) ^ 2) μ :=
      integrable_of_measurable_abs_le (hSmeas.pow_const 2) (fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hSbound ω) 2)
    have hIntZ2 : Integrable (fun ω => (Z n ω) ^ 2) μ :=
      integrable_of_measurable_abs_le ((hZmeas n).pow_const 2) (fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hZbdd n ω) 2)
    have hIntSZ : Integrable (fun ω => S ω * Z n ω) μ :=
      integrable_of_measurable_abs_le (hSmeas.mul (hZmeas n)) (fun ω => by
        rw [abs_mul]
        calc |S ω| * |Z n ω| ≤ ((n - m : ℝ) * B) * B :=
              mul_le_mul (hSbound ω) (hZbdd n ω) (abs_nonneg _) hNB)
    have hIntS4 : Integrable (fun ω => (S ω) ^ 4) μ :=
      integrable_of_measurable_abs_le (hSmeas.pow_const 4) (fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hSbound ω) 4)
    have hIntS3Z : Integrable (fun ω => (S ω) ^ 3 * Z n ω) μ :=
      integrable_of_measurable_abs_le ((hSmeas.pow_const 3).mul (hZmeas n)) (fun ω => by
        calc |(S ω) ^ 3 * Z n ω| = |S ω| ^ 3 * |Z n ω| := by rw [abs_mul, abs_pow]
          _ ≤ ((n - m : ℝ) * B) ^ 3 * B :=
              mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hSbound ω) 3) (hZbdd n ω)
                (abs_nonneg _) (pow_nonneg hNB 3))
    have hIntS2Z2 : Integrable (fun ω => (S ω) ^ 2 * (Z n ω) ^ 2) μ :=
      integrable_of_measurable_abs_le ((hSmeas.pow_const 2).mul ((hZmeas n).pow_const 2)) (fun ω => by
        calc |(S ω) ^ 2 * (Z n ω) ^ 2| = |S ω| ^ 2 * |Z n ω| ^ 2 := by rw [abs_mul, abs_pow, abs_pow]
          _ ≤ ((n - m : ℝ) * B) ^ 2 * B ^ 2 :=
              mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hSbound ω) 2)
                (pow_le_pow_left₀ (abs_nonneg _) (hZbdd n ω) 2) (by positivity)
                (pow_nonneg hNB 2))
    have hIntSZ3 : Integrable (fun ω => S ω * (Z n ω) ^ 3) μ :=
      integrable_of_measurable_abs_le (hSmeas.mul ((hZmeas n).pow_const 3)) (fun ω => by
        calc |S ω * (Z n ω) ^ 3| = |S ω| * |Z n ω| ^ 3 := by rw [abs_mul, abs_pow]
          _ ≤ ((n - m : ℝ) * B) * B ^ 3 :=
              mul_le_mul (hSbound ω) (pow_le_pow_left₀ (abs_nonneg _) (hZbdd n ω) 3)
                (by positivity) hNB)
    have hIntZ4 : Integrable (fun ω => (Z n ω) ^ 4) μ :=
      integrable_of_measurable_abs_le ((hZmeas n).pow_const 4) (fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hZbdd n ω) 4)
    -- Integral of the expanded fourth power.
    have hsum : ∫ ω, (S ω + Z n ω) ^ 4 ∂μ =
        (∫ ω, (S ω) ^ 4 ∂μ) + 4 * (∫ ω, (S ω) ^ 3 * Z n ω ∂μ) +
          6 * (∫ ω, (S ω) ^ 2 * (Z n ω) ^ 2 ∂μ) +
          4 * (∫ ω, S ω * (Z n ω) ^ 3 ∂μ) + (∫ ω, (Z n ω) ^ 4 ∂μ) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => (by ring :
        (S ω + Z n ω) ^ 4 = (S ω) ^ 4 + 4 * ((S ω) ^ 3 * Z n ω) +
          6 * ((S ω) ^ 2 * (Z n ω) ^ 2) + 4 * (S ω * (Z n ω) ^ 3) + (Z n ω) ^ 4))]
      have hA : Integrable (fun ω => (S ω) ^ 4 + 4 * ((S ω) ^ 3 * Z n ω)) μ :=
        hIntS4.add (hIntS3Z.const_mul 4)
      have hB' : Integrable (fun ω => (S ω) ^ 4 + 4 * ((S ω) ^ 3 * Z n ω) +
          6 * ((S ω) ^ 2 * (Z n ω) ^ 2)) μ :=
        hA.add (hIntS2Z2.const_mul 6)
      have hC : Integrable (fun ω => (S ω) ^ 4 + 4 * ((S ω) ^ 3 * Z n ω) +
          6 * ((S ω) ^ 2 * (Z n ω) ^ 2) + 4 * (S ω * (Z n ω) ^ 3)) μ :=
        hB'.add (hIntSZ3.const_mul 4)
      rw [integral_add hC hIntZ4, integral_add hB' (hIntSZ3.const_mul 4),
        integral_add hA (hIntS2Z2.const_mul 6), integral_add hIntS4 (hIntS3Z.const_mul 4)]
      simp only [integral_const_mul]
    -- Second moment of the step.
    have h2step : ∫ ω, (S ω + Z n ω) ^ 2 ∂μ =
        (∫ ω, (S ω) ^ 2 ∂μ) + (∫ ω, (Z n ω) ^ 2 ∂μ) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => (by ring :
        (S ω + Z n ω) ^ 2 = (S ω) ^ 2 + 2 * (S ω * Z n ω) + (Z n ω) ^ 2))]
      have hA2 : Integrable (fun ω => (S ω) ^ 2 + 2 * (S ω * Z n ω)) μ :=
        hIntS2.add (hIntSZ.const_mul 2)
      rw [integral_add hA2 hIntZ2, integral_add hIntS2 (hIntSZ.const_mul 2),
        integral_const_mul, hSZ]
      simp
    -- First moment of the step.
    have h0step : ∫ ω, (S ω + Z n ω) ∂μ = 0 := by
      rw [integral_add hIntS hIntZ, h0, hZmean n, add_zero]
    -- Assemble.
    have hI4 : (∫ ω, (∑ k ∈ Finset.Ico m (n + 1), Z k ω) ^ 4 ∂μ) =
        ∫ ω, (S ω + Z n ω) ^ 4 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        show (∑ k ∈ Finset.Ico m (n + 1), Z k ω) ^ 4 = (S ω + Z n ω) ^ 4
        rw [Finset.sum_Ico_succ_top hmn])
    have hI2 : (∫ ω, (∑ k ∈ Finset.Ico m (n + 1), Z k ω) ^ 2 ∂μ) =
        ∫ ω, (S ω + Z n ω) ^ 2 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        show (∑ k ∈ Finset.Ico m (n + 1), Z k ω) ^ 2 = (S ω + Z n ω) ^ 2
        rw [Finset.sum_Ico_succ_top hmn])
    have hI1 : (∫ ω, (∑ k ∈ Finset.Ico m (n + 1), Z k ω) ∂μ) =
        ∫ ω, (S ω + Z n ω) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        show ∑ k ∈ Finset.Ico m (n + 1), Z k ω = S ω + Z n ω
        rw [Finset.sum_Ico_succ_top hmn])
    refine ⟨?_, ?_, ?_⟩
    · rw [hI4, hI2, hsum, hS3Z, hSZ3, hS2Z2, h2step]
      have hv : 0 ≤ ∫ ω, (S ω) ^ 2 ∂μ :=
        integral_nonneg fun ω => sq_nonneg _
      have hw : 0 ≤ ∫ ω, (Z n ω) ^ 2 ∂μ :=
        integral_nonneg fun ω => sq_nonneg _
      nlinarith [h4, hZ4le, sq_nonneg (∫ ω, (Z n ω) ^ 2 ∂μ), hv, hw, hB]
    · rw [hI2, h2step, h2, Finset.sum_Ico_succ_top hmn]
    · rw [hI1, h0step]



/-- Interval selection: if the partial sums of a nonnegative sequence with
steps bounded by `D` are unbounded, then past any `m` there is an interval
`[m, n)` whose sum lies in `[1, 1 + D]`. -/
private theorem exists_Ico_sum_mem_Icc {w : ℕ → ℝ} {D : ℝ} (hw : ∀ n, 0 ≤ w n)
    (hwD : ∀ n, w n ≤ D)
    (hunbdd : ∀ C : ℝ, ∃ n, C < ∑ k ∈ Finset.range n, w k) (m : ℕ) :
    ∃ n, m ≤ n ∧ 1 ≤ ∑ k ∈ Finset.Ico m n, w k ∧ ∑ k ∈ Finset.Ico m n, w k ≤ 1 + D := by
  classical
  obtain ⟨N, hN⟩ := hunbdd ((∑ k ∈ Finset.range m, w k) + 1)
  have hNm : m ≤ N := by
    by_contra h
    push Not at h
    have hle : ∑ k ∈ Finset.range N, w k ≤ ∑ k ∈ Finset.range m, w k :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => by
        rw [Finset.mem_range] at hk ⊢; omega) (fun k _ _ => hw k)
    linarith
  have hex : ∃ j, (∑ k ∈ Finset.range m, w k) + 1 ≤ ∑ k ∈ Finset.range (m + j), w k := by
    refine ⟨N - m, ?_⟩
    have hmn : m + (N - m) = N := by omega
    rw [hmn]
    exact hN.le
  set j := Nat.find hex with hjdef
  have hspec : (∑ k ∈ Finset.range m, w k) + 1 ≤ ∑ k ∈ Finset.range (m + j), w k :=
    Nat.find_spec hex
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h] at hspec
      simp only [Nat.add_zero] at hspec
      linarith
    · exact h
  have hmin : ∑ k ∈ Finset.range (m + (j - 1)), w k < (∑ k ∈ Finset.range m, w k) + 1 := by
    have h := Nat.find_min hex (show j - 1 < j from by omega)
    push Not at h
    exact h
  have hsucc : ∑ k ∈ Finset.range (m + j), w k =
      ∑ k ∈ Finset.range (m + (j - 1)), w k + w (m + (j - 1)) := by
    have hmj : m + j = (m + (j - 1)) + 1 := by omega
    rw [hmj, Finset.sum_range_succ]
  refine ⟨m + j, by omega, ?_, ?_⟩
  · have hIco : ∑ k ∈ Finset.Ico m (m + j), w k =
        ∑ k ∈ Finset.range (m + j), w k - ∑ k ∈ Finset.range m, w k :=
      Finset.sum_Ico_eq_sub w (by omega : m ≤ m + j)
    rw [hIco]
    linarith [hspec]
  · have hIco : ∑ k ∈ Finset.Ico m (m + j), w k =
        ∑ k ∈ Finset.range (m + j), w k - ∑ k ∈ Finset.range m, w k :=
      Finset.sum_Ico_eq_sub w (by omega : m ≤ m + j)
    rw [hIco, hsucc]
    have hwle := hwD (m + (j - 1))
    linarith

/-- **Three-series necessity, second half of the variance step.** For a
uniformly bounded independent sequence whose partial sums converge almost
surely, the variances are summable. Proved by symmetrization: the
symmetrized sums are centered, so Paley–Zygmund gives a uniform lower
bound on block-tail probabilities, contradicting convergence in
measure unless the variances are summable. -/
theorem summable_variance_of_bounded_ae_tendsto {Y : ℕ → Ω → ℝ}
    (hYmeas : ∀ n, Measurable (Y n)) (hYindep : iIndepFun Y μ)
    {A : ℝ} (hA : 0 < A) (hYbdd : ∀ n ω, |Y n ω| ≤ A)
    (hYtend : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => Y i ω)) atTop (nhds (S ω))) :
    Summable (fun n => variance (Y n) μ) := by
  classical
  -- Symmetrized sequence on the product space.
  have hZmeas : ∀ n, Measurable (symmRV Y n) := fun n => measurable_symmRV hYmeas n
  have hZindep : iIndepFun (symmRV Y) (μ.prod μ) := iIndepFun_symmRV hYmeas hYindep
  have hZbdd : ∀ n p, |symmRV Y n p| ≤ 2 * A := by
    intro n p
    show |Y n p.1 - Y n p.2| ≤ 2 * A
    calc |Y n p.1 - Y n p.2| ≤ |Y n p.1| + |Y n p.2| := abs_sub _ _
      _ ≤ A + A := add_le_add (hYbdd n p.1) (hYbdd n p.2)
      _ = 2 * A := by ring
  have hYint : ∀ n, Integrable (Y n) μ := fun n =>
    integrable_of_measurable_abs_le (hYmeas n) (hYbdd n)
  have hZmean : ∀ n, ∫ p, symmRV Y n p ∂(μ.prod μ) = 0 := by
    intro n
    have hIntF : Integrable (fun p : Ω × Ω => Y n p.1) (μ.prod μ) := (hYint n).comp_fst μ
    have hIntS : Integrable (fun p : Ω × Ω => Y n p.2) (μ.prod μ) := (hYint n).comp_snd μ
    have hF : ∫ p : Ω × Ω, Y n p.1 ∂(μ.prod μ) = ∫ ω, Y n ω ∂μ := by
      rw [MeasureTheory.integral_prod _ hIntF]
      show ∫ x, ∫ y, Y n x ∂μ ∂μ = ∫ ω, Y n ω ∂μ
      have h2 : (fun x => ∫ y, Y n x ∂μ) = (fun x => Y n x) := by
        funext x
        rw [integral_const]; simp [Measure.real]
      rw [h2]
    have hS : ∫ p : Ω × Ω, Y n p.2 ∂(μ.prod μ) = ∫ ω, Y n ω ∂μ := by
      rw [MeasureTheory.integral_prod _ hIntS]
      show ∫ x, ∫ y, Y n y ∂μ ∂μ = ∫ ω, Y n ω ∂μ
      have h2 : (fun x => ∫ y, Y n y ∂μ) = (fun _ : Ω => ∫ ω, Y n ω ∂μ) := by
        funext x; rfl
      rw [h2, integral_const]; simp [Measure.real]
    show ∫ p, (Y n p.1 - Y n p.2) ∂(μ.prod μ) = 0
    rw [integral_sub hIntF hIntS, hF, hS, sub_self]
  -- The symmetrized partial sums converge in measure on the product space,
  -- at the `1/4` threshold, proved by squeezing with the `Y`-sums in each
  -- coordinate and the triangle inequality on `edist`.
  obtain ⟨S, hS⟩ := hYtend
  have hYinM : TendstoInMeasure μ (fun n ω => (Finset.range n).sum (fun i => Y i ω)) atTop S := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (Finset.measurable_sum _ (fun i _ => hYmeas i)).aestronglyMeasurable
    · exact hS
  have hZinM14 : Tendsto (fun n =>
      (μ.prod μ) {p | ENNReal.ofReal (1 / 4 : ℝ) ≤
        edist ((Finset.range n).sum (fun i => symmRV Y i p)) (S p.1 - S p.2)})
      atTop (𝓝 0) := by
    have hY18 : Tendsto (fun n => μ {ω | ENNReal.ofReal (1 / 8 : ℝ) ≤
        edist ((Finset.range n).sum (fun i => Y i ω)) (S ω)}) atTop (𝓝 0) :=
      hYinM (ENNReal.ofReal (1 / 8 : ℝ)) (ENNReal.ofReal_pos.mpr (by norm_num))
    have hY18add : Tendsto (fun n => μ {ω | ENNReal.ofReal (1 / 8 : ℝ) ≤
        edist ((Finset.range n).sum (fun i => Y i ω)) (S ω)} +
        μ {ω | ENNReal.ofReal (1 / 8 : ℝ) ≤
        edist ((Finset.range n).sum (fun i => Y i ω)) (S ω)}) atTop (𝓝 0) := by
      simpa only [add_zero] using hY18.add hY18
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hY18add (Filter.Eventually.of_forall fun _ => zero_le)
      (Filter.Eventually.of_forall fun n => ?_)
    show (μ.prod μ) {p | ENNReal.ofReal (1 / 4 : ℝ) ≤
        edist ((Finset.range n).sum (fun i => symmRV Y i p)) (S p.1 - S p.2)} ≤
      μ {ω | ENNReal.ofReal (1 / 8 : ℝ) ≤
        edist ((Finset.range n).sum (fun i => Y i ω)) (S ω)} +
      μ {ω | ENNReal.ofReal (1 / 8 : ℝ) ≤
        edist ((Finset.range n).sum (fun i => Y i ω)) (S ω)}
    calc (μ.prod μ) {p | ENNReal.ofReal (1 / 4 : ℝ) ≤
            edist ((Finset.range n).sum (fun i => symmRV Y i p)) (S p.1 - S p.2)}
        ≤ (μ.prod μ) ({ω | ENNReal.ofReal (1 / 8 : ℝ) ≤
            edist ((Finset.range n).sum (fun i => Y i ω)) (S ω)} ×ˢ Set.univ ∪
            Set.univ ×ˢ {ω | ENNReal.ofReal (1 / 8 : ℝ) ≤
            edist ((Finset.range n).sum (fun i => Y i ω)) (S ω)}) := by
          apply measure_mono
          intro p hp
          simp only [Set.mem_ofPred_eq] at hp
          by_contra hnot
          simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, true_and, and_true, not_or]
            at hnot
          obtain ⟨h1, h2⟩ := hnot
          simp only [Set.mem_ofPred_eq] at h1 h2
          have h1' : edist ((Finset.range n).sum (fun i => Y i p.1)) (S p.1) <
              ENNReal.ofReal (1 / 8 : ℝ) := not_le.mp h1
          have h2' : edist ((Finset.range n).sum (fun i => Y i p.2)) (S p.2) <
              ENNReal.ofReal (1 / 8 : ℝ) := not_le.mp h2
          have h1r : dist ((Finset.range n).sum (fun i => Y i p.1)) (S p.1) < 1 / 8 := by
            have h := h1'
            rw [edist_dist] at h
            exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < (1:ℝ)/8)).mp h
          have h2r : dist ((Finset.range n).sum (fun i => Y i p.2)) (S p.2) < 1 / 8 := by
            have h := h2'
            rw [edist_dist] at h
            exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < (1:ℝ)/8)).mp h
          have hdist : dist ((Finset.range n).sum (fun i => symmRV Y i p)) (S p.1 - S p.2) ≤
              dist ((Finset.range n).sum (fun i => Y i p.1)) (S p.1) +
              dist ((Finset.range n).sum (fun i => Y i p.2)) (S p.2) := by
            have hsum : (Finset.range n).sum (fun i => symmRV Y i p) =
                (Finset.range n).sum (fun i => Y i p.1) -
                (Finset.range n).sum (fun i => Y i p.2) := by
              have hcongr : (fun i => symmRV Y i p) = (fun i => Y i p.1 - Y i p.2) := by
                funext i; rfl
              rw [hcongr, Finset.sum_sub_distrib]
            rw [hsum, Real.dist_eq, Real.dist_eq, Real.dist_eq]
            have hring : ((Finset.range n).sum (fun i => Y i p.1) -
                (Finset.range n).sum (fun i => Y i p.2)) - (S p.1 - S p.2) =
                ((Finset.range n).sum (fun i => Y i p.1) - S p.1) -
                ((Finset.range n).sum (fun i => Y i p.2) - S p.2) := by ring
            rw [hring]
            exact abs_sub _ _
          have hlt : dist ((Finset.range n).sum (fun i => symmRV Y i p)) (S p.1 - S p.2) <
              1 / 4 := by
            refine lt_of_le_of_lt hdist ?_
            rw [show (1/4 : ℝ) = 1/8 + 1/8 by norm_num]
            exact add_lt_add h1r h2r
          have hp' : (1/4 : ℝ) ≤
              dist ((Finset.range n).sum (fun i => symmRV Y i p)) (S p.1 - S p.2) := by
            have h := hp
            rw [edist_dist] at h
            exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h
          exact lt_irrefl _ (lt_of_le_of_lt hp' hlt)
      _ ≤ (μ.prod μ) ({ω | ENNReal.ofReal (1 / 8 : ℝ) ≤
            edist ((Finset.range n).sum (fun i => Y i ω)) (S ω)} ×ˢ Set.univ) +
          (μ.prod μ) (Set.univ ×ˢ {ω | ENNReal.ofReal (1 / 8 : ℝ) ≤
            edist ((Finset.range n).sum (fun i => Y i ω)) (S ω)}) :=
        measure_union_le _ _
      _ = μ {ω | ENNReal.ofReal (1 / 8 : ℝ) ≤
            edist ((Finset.range n).sum (fun i => Y i ω)) (S ω)} +
          μ {ω | ENNReal.ofReal (1 / 8 : ℝ) ≤
            edist ((Finset.range n).sum (fun i => Y i ω)) (S ω)} := by
        rw [Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, one_mul]
  -- Variance of the symmetrized variables: `Var(Z n) = 2 Var(Y n)`.
  have hVarZ : ∀ n, variance (symmRV Y n) (μ.prod μ) = 2 * variance (Y n) μ := by
    intro n
    have hMemZ : MemLp (symmRV Y n) 2 (μ.prod μ) :=
      MemLp.of_bound (hZmeas n).aestronglyMeasurable (2 * A)
        (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs]; exact hZbdd n p)
    have hMemY : MemLp (Y n) 2 μ :=
      MemLp.of_bound (hYmeas n).aestronglyMeasurable A
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact hYbdd n ω)
    rw [variance_eq_sub hMemZ, variance_eq_sub hMemY, hZmean n]
    have hE2 : ∫ p, (symmRV Y n p) ^ 2 ∂(μ.prod μ) =
        2 * (∫ ω, (Y n ω) ^ 2 ∂μ) - 2 * (∫ ω, Y n ω ∂μ) * (∫ ω, Y n ω ∂μ) := by
      have hIntA : Integrable (fun p : Ω × Ω => (Y n p.1) ^ 2) (μ.prod μ) := by
        apply integrable_of_measurable_abs_le ((hYmeas n).comp measurable_fst |>.pow_const 2)
        intro p
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hYbdd n p.1) 2
      have hIntC : Integrable (fun p : Ω × Ω => (Y n p.2) ^ 2) (μ.prod μ) := by
        apply integrable_of_measurable_abs_le ((hYmeas n).comp measurable_snd |>.pow_const 2)
        intro p
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hYbdd n p.2) 2
      have hIntB : Integrable (fun p : Ω × Ω => (Y n p.1) * (Y n p.2)) (μ.prod μ) := by
        apply integrable_of_measurable_abs_le
          (((hYmeas n).comp measurable_fst).mul ((hYmeas n).comp measurable_snd))
        intro p
        simp only [Pi.mul_apply, Function.comp_apply]
        rw [abs_mul]
        have h1 := hYbdd n p.1
        have h2 := hYbdd n p.2
        calc |Y n p.1| * |Y n p.2| ≤ A * A := mul_le_mul h1 h2 (abs_nonneg _) hA.le
          _ = A ^ 2 := by ring
      have hInt2B : Integrable (fun p : Ω × Ω => 2 * (Y n p.1 * Y n p.2)) (μ.prod μ) :=
        hIntB.const_mul 2
      have hProd : ∫ p : Ω × Ω, Y n p.1 * Y n p.2 ∂(μ.prod μ) =
          (∫ ω, Y n ω ∂μ) * (∫ ω, Y n ω ∂μ) := by
        rw [MeasureTheory.integral_prod _ hIntB]
        show ∫ x, ∫ y, Y n x * Y n y ∂μ ∂μ = (∫ ω, Y n ω ∂μ) * (∫ ω, Y n ω ∂μ)
        have h2 : (fun x => ∫ y, Y n x * Y n y ∂μ) = (fun x => Y n x * ∫ y, Y n y ∂μ) := by
          funext x; exact integral_const_mul (Y n x) (fun y => Y n y)
        rw [h2, integral_mul_const]
      have hIA : ∫ p : Ω × Ω, (Y n p.1) ^ 2 ∂(μ.prod μ) = ∫ ω, (Y n ω) ^ 2 ∂μ := by
        rw [MeasureTheory.integral_prod _ hIntA]
        show ∫ x, ∫ y, (Y n x) ^ 2 ∂μ ∂μ = ∫ ω, (Y n ω) ^ 2 ∂μ
        have h2 : (fun x => ∫ y, (Y n x) ^ 2 ∂μ) = (fun x => (Y n x) ^ 2) := by
          funext x
          rw [integral_const]; simp [Measure.real]
        rw [h2]
      have hIC : ∫ p : Ω × Ω, (Y n p.2) ^ 2 ∂(μ.prod μ) = ∫ ω, (Y n ω) ^ 2 ∂μ := by
        rw [MeasureTheory.integral_prod _ hIntC]
        show ∫ x, ∫ y, (Y n y) ^ 2 ∂μ ∂μ = ∫ ω, (Y n ω) ^ 2 ∂μ
        have h2 : (fun x => ∫ y, (Y n y) ^ 2 ∂μ) = (fun _ : Ω => ∫ ω, (Y n ω) ^ 2 ∂μ) := by
          funext x; rfl
        rw [h2, integral_const]; simp [Measure.real]
      have hexp : (fun p : Ω × Ω => (symmRV Y n p) ^ 2) =
          (fun p => (Y n p.1) ^ 2 - 2 * (Y n p.1 * Y n p.2) + (Y n p.2) ^ 2) := by
        funext p
        show (Y n p.1 - Y n p.2) ^ 2 = _
        rw [sub_sq]; ring
      have hAdd : ∫ p, ((Y n p.1) ^ 2 - 2 * (Y n p.1 * Y n p.2) + (Y n p.2) ^ 2) ∂(μ.prod μ) =
          (∫ p, ((Y n p.1) ^ 2 - 2 * (Y n p.1 * Y n p.2)) ∂(μ.prod μ)) +
          ∫ p, (Y n p.2) ^ 2 ∂(μ.prod μ) :=
        integral_add (hIntA.sub hInt2B) hIntC
      have hSub : ∫ p, ((Y n p.1) ^ 2 - 2 * (Y n p.1 * Y n p.2)) ∂(μ.prod μ) =
          (∫ p, (Y n p.1) ^ 2 ∂(μ.prod μ)) - ∫ p, (2 * (Y n p.1 * Y n p.2)) ∂(μ.prod μ) :=
        integral_sub hIntA hInt2B
      rw [hexp, hAdd, hSub, integral_const_mul (2 : ℝ), hProd, hIA, hIC]
      ring
    rw [zero_pow (show (2:ℕ) ≠ 0 by norm_num), sub_zero]
    show ∫ p, (symmRV Y n p) ^ 2 ∂(μ.prod μ) =
      2 * (∫ ω, (Y n ω) ^ 2 ∂μ - (∫ ω, Y n ω ∂μ) ^ 2)
    rw [hE2]
    ring
  -- Individual variances are bounded by `A ^ 2`.
  have hVarY : ∀ n, variance (Y n) μ ≤ A ^ 2 := by
    intro n
    have hMemY : MemLp (Y n) 2 μ :=
      MemLp.of_bound (hYmeas n).aestronglyMeasurable A
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact hYbdd n ω)
    rw [variance_eq_sub hMemY]
    have h1 : ∫ ω, (Y n ω) ^ 2 ∂μ ≤ A ^ 2 := by
      have hInt2 : Integrable (fun ω => (Y n ω) ^ 2) μ :=
        integrable_of_measurable_abs_le ((hYmeas n).pow_const 2) (fun ω => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hYbdd n ω) 2)
      calc ∫ ω, (Y n ω) ^ 2 ∂μ ≤ ∫ _ω, A ^ 2 ∂μ := by
            apply integral_mono_ae hInt2 (integrable_const _)
            filter_upwards with ω
            exact sq_le_sq' (by linarith [neg_abs_le (Y n ω), hYbdd n ω]) (by
              linarith [le_abs_self (Y n ω), hYbdd n ω])
        _ = A ^ 2 := by
          rw [integral_const]; simp [Measure.real]
    have h2 : 0 ≤ (∫ ω, Y n ω ∂μ) ^ 2 := sq_nonneg _
    show ∫ ω, (Y n ω) ^ 2 ∂μ - (∫ ω, Y n ω ∂μ) ^ 2 ≤ A ^ 2
    linarith
  -- Suppose the variances are not summable, and derive a contradiction.
  by_contra hnsum
  have hunbdd : ∀ C : ℝ, ∃ n, C < ∑ k ∈ Finset.range n, variance (symmRV Y k) (μ.prod μ) := by
    intro C
    by_contra hle
    push Not at hle
    have hSumbdd : ∀ n, ∑ k ∈ Finset.range n, variance (Y k) μ ≤ C / 2 := by
      intro n
      have h := hle n
      rw [Finset.sum_congr rfl (fun k _ => hVarZ k), ← Finset.mul_sum] at h
      linarith
    exact hnsum (summable_of_sum_range_le (fun n => variance_nonneg _ _) hSumbdd)
  -- Paley–Zygmund constants: block variance in `[1, 1 + D]`, `D = 2 A ^ 2`.
  set D : ℝ := 2 * A ^ 2 with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  have hVarZbdd : ∀ n, variance (symmRV Y n) (μ.prod μ) ≤ D := by
    intro n
    rw [hVarZ n, hDdef]
    have := hVarY n
    linarith
  have hK : (0:ℝ) < 3 * (1 + D) ^ 2 + (2 * A) ^ 2 * (1 + D) := by
    have h1 : (1:ℝ) ≤ (1 + D) ^ 2 := by
      calc (1:ℝ) = (1:ℝ) ^ 2 := by norm_num
        _ ≤ (1 + D) ^ 2 := by
          apply pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have h2 : (0:ℝ) ≤ (2 * A) ^ 2 * (1 + D) := by
      apply mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  set K : ℝ := 3 * (1 + D) ^ 2 + (2 * A) ^ 2 * (1 + D) with hKdef
  have hKpos : 0 < K := hK
  set c : ℝ := (9 / 16) / K with hcdef
  have hcpos : 0 < c := div_pos (by norm_num) hKpos
  -- Convergence in measure gives the threshold `N`.
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hZinM14
    (ENNReal.ofReal (c / 4)) (ENNReal.ofReal_pos.mpr (div_pos hcpos (by norm_num)))
  -- An interval `[N, n)` with block variance in `[1, 1 + D]`.
  obtain ⟨n, hNn, h1, h2⟩ := exists_Ico_sum_mem_Icc (fun n => variance_nonneg _ _)
    hVarZbdd hunbdd N
  -- The block sum and its second and fourth moments.
  set Sblk : Ω × Ω → ℝ := fun p => ∑ k ∈ Finset.Ico N n, symmRV Y k p with hSblkdef
  have hSmeas : Measurable Sblk :=
    Finset.measurable_sum _ (fun k _ => hZmeas k)
  have hMom := integral_pow_four_le (Z := symmRV Y) (μ := μ.prod μ) (B := 2 * A)
    hZmeas hZindep (by linarith : (0:ℝ) ≤ 2 * A) hZbdd hZmean hNn
  -- `∫ Sblk ^ 2 = ∑_{Ico} Var(Z)`, hence in `[1, 1 + D]`.
  have hVarBlock : ∫ p, (Sblk p) ^ 2 ∂(μ.prod μ) =
      ∑ k ∈ Finset.Ico N n, variance (symmRV Y k) (μ.prod μ) := by
    show ∫ p, (∑ k ∈ Finset.Ico N n, symmRV Y k p) ^ 2 ∂(μ.prod μ) = _
    rw [hMom.2.1]
    apply Finset.sum_congr rfl
    intro k _
    have hMemZ : MemLp (symmRV Y k) 2 (μ.prod μ) :=
      MemLp.of_bound (hZmeas k).aestronglyMeasurable (2 * A)
        (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs]; exact hZbdd k p)
    rw [variance_eq_sub hMemZ, hZmean k]
    simp
  have hv1 : (1:ℝ) ≤ ∫ p, (Sblk p) ^ 2 ∂(μ.prod μ) := by rw [hVarBlock]; exact h1
  have hv2 : ∫ p, (Sblk p) ^ 2 ∂(μ.prod μ) ≤ 1 + D := by rw [hVarBlock]; exact h2
  -- The fourth moment bound.
  have hSInt2 : Integrable (fun p => (Sblk p) ^ 2) (μ.prod μ) := by
    apply integrable_of_measurable_abs_le (C := ((n - N : ℝ) * (2 * A)) ^ 2) (hSmeas.pow_const 2)
    intro p
    rw [abs_pow]
    have hSB : |Sblk p| ≤ (n - N : ℝ) * (2 * A) := by
      have hbd : ∀ k ∈ Finset.Ico N n, |symmRV Y k p| ≤ 2 * A := fun k _ => hZbdd k p
      calc |Sblk p| = |∑ k ∈ Finset.Ico N n, symmRV Y k p| := by rfl
        _ ≤ ∑ k ∈ Finset.Ico N n, |symmRV Y k p| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.Ico N n, (2 * A) := Finset.sum_le_sum hbd
        _ = (n - N : ℝ) * (2 * A) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hNn]
    exact pow_le_pow_left₀ (abs_nonneg _) hSB 2
  have hSInt4 : Integrable (fun p => (Sblk p) ^ 4) (μ.prod μ) := by
    apply integrable_of_measurable_abs_le (C := ((n - N : ℝ) * (2 * A)) ^ 4) (hSmeas.pow_const 4)
    intro p
    rw [abs_pow]
    have hSB : |Sblk p| ≤ (n - N : ℝ) * (2 * A) := by
      have hbd : ∀ k ∈ Finset.Ico N n, |symmRV Y k p| ≤ 2 * A := fun k _ => hZbdd k p
      calc |Sblk p| = |∑ k ∈ Finset.Ico N n, symmRV Y k p| := by rfl
        _ ≤ ∑ k ∈ Finset.Ico N n, |symmRV Y k p| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.Ico N n, (2 * A) := Finset.sum_le_sum hbd
        _ = (n - N : ℝ) * (2 * A) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hNn]
    exact pow_le_pow_left₀ (abs_nonneg _) hSB 4
  have hE4 : ∫ p, (Sblk p) ^ 4 ∂(μ.prod μ) ≤
      3 * (∫ p, (Sblk p) ^ 2 ∂(μ.prod μ)) ^ 2 +
      (2 * A) ^ 2 * (∫ p, (Sblk p) ^ 2 ∂(μ.prod μ)) := by
    show ∫ p, (∑ k ∈ Finset.Ico N n, symmRV Y k p) ^ 4 ∂(μ.prod μ) ≤
      3 * (∫ p, (∑ k ∈ Finset.Ico N n, symmRV Y k p) ^ 2 ∂(μ.prod μ)) ^ 2 +
      (2 * A) ^ 2 * (∫ p, (∑ k ∈ Finset.Ico N n, symmRV Y k p) ^ 2 ∂(μ.prod μ))
    exact hMom.1
  -- Paley–Zygmund: `(v - 1/4) ^ 2 ≤ E[Sblk ^ 4] * P(|Sblk| > 1/2)`.
  have hPZ := paley_zygmund_measure_abs_gt_half (μ := μ.prod μ) (S := Sblk) hSmeas hSInt2 hSInt4
    (v := ∫ p, (Sblk p) ^ 2 ∂(μ.prod μ)) (by linarith) le_rfl
  -- Hence `(ν {1/2 < |Sblk|}).toReal ≥ c`.
  have hPc : ENNReal.ofReal c ≤ (μ.prod μ) {p | (1:ℝ)/2 < |Sblk p|} := by
    have hstep : (9 / 16 : ℝ) ≤ K *
        ((μ.prod μ) {p | (1:ℝ)/2 < |Sblk p|}).toReal := by
      have h914 : (9 / 16 : ℝ) ≤ (∫ p, (Sblk p) ^ 2 ∂(μ.prod μ) - 1 / 4) ^ 2 := by
        have h34 : (0:ℝ) ≤ ∫ p, (Sblk p) ^ 2 ∂(μ.prod μ) - 1 / 4 := by linarith
        calc (9 / 16 : ℝ) = (3 / 4) ^ 2 := by norm_num
          _ ≤ (∫ p, (Sblk p) ^ 2 ∂(μ.prod μ) - 1 / 4) ^ 2 := by
            apply pow_le_pow_left₀ (by norm_num) (by linarith) 2
      have hE4b : ∫ p, (Sblk p) ^ 4 ∂(μ.prod μ) ≤ K := by
        rw [hKdef]
        have hv0 : (0:ℝ) ≤ ∫ p, (Sblk p) ^ 2 ∂(μ.prod μ) := by linarith
        have h3 : 3 * (∫ p, (Sblk p) ^ 2 ∂(μ.prod μ)) ^ 2 ≤ 3 * (1 + D) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
          apply pow_le_pow_left₀ hv0 hv2 2
        have hB : (2 * A) ^ 2 * (∫ p, (Sblk p) ^ 2 ∂(μ.prod μ)) ≤ (2 * A) ^ 2 * (1 + D) :=
          mul_le_mul_of_nonneg_left hv2 (sq_nonneg _)
        linarith [hE4, h3, hB]
      calc (9 / 16 : ℝ) ≤ (∫ p, (Sblk p) ^ 2 ∂(μ.prod μ) - 1 / 4) ^ 2 := h914
        _ ≤ (∫ p, (Sblk p) ^ 4 ∂(μ.prod μ)) *
            ((μ.prod μ) {p | (1:ℝ)/2 < |Sblk p|}).toReal := hPZ
        _ ≤ K * ((μ.prod μ) {p | (1:ℝ)/2 < |Sblk p|}).toReal :=
          mul_le_mul_of_nonneg_right hE4b ENNReal.toReal_nonneg
    have hstep2 : c ≤ ((μ.prod μ) {p | (1:ℝ)/2 < |Sblk p|}).toReal := by
      rw [hcdef]
      rw [div_le_iff₀ hKpos]
      rw [mul_comm]
      exact hstep
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hstep2
  -- But `{1/2 < |Sblk|}` is contained in the two convergence-in-measure sets.
  have hsub : {p | (1:ℝ)/2 < |Sblk p|} ⊆
      {p | ENNReal.ofReal (1 / 4 : ℝ) ≤
        edist ((Finset.range n).sum (fun i => symmRV Y i p)) (S p.1 - S p.2)} ∪
      {p | ENNReal.ofReal (1 / 4 : ℝ) ≤
        edist ((Finset.range N).sum (fun i => symmRV Y i p)) (S p.1 - S p.2)} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hnot
    obtain ⟨hn, hm⟩ := hnot
    have hn' : edist ((Finset.range n).sum (fun i => symmRV Y i p)) (S p.1 - S p.2) <
        ENNReal.ofReal (1 / 4 : ℝ) := not_le.mp hn
    have hm' : edist ((Finset.range N).sum (fun i => symmRV Y i p)) (S p.1 - S p.2) <
        ENNReal.ofReal (1 / 4 : ℝ) := not_le.mp hm
    have hn'' : |(Finset.range n).sum (fun i => symmRV Y i p) - (S p.1 - S p.2)| < 1 / 4 := by
      have h := hn'
      rw [edist_dist] at h
      have h2 := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < (1:ℝ)/4)).mp h
      rwa [Real.dist_eq] at h2
    have hm'' : |(Finset.range N).sum (fun i => symmRV Y i p) - (S p.1 - S p.2)| < 1 / 4 := by
      have h := hm'
      rw [edist_dist] at h
      have h2 := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < (1:ℝ)/4)).mp h
      rwa [Real.dist_eq] at h2
    have hSdiff : Sblk p = (Finset.range n).sum (fun i => symmRV Y i p) -
        (Finset.range N).sum (fun i => symmRV Y i p) := by
      show (∑ k ∈ Finset.Ico N n, symmRV Y k p) =
        (Finset.range n).sum (fun i => symmRV Y i p) - (Finset.range N).sum (fun i => symmRV Y i p)
      rw [Finset.sum_Ico_eq_sub _ hNn]
    rw [hSdiff] at hp
    have htri : |(Finset.range n).sum (fun i => symmRV Y i p) -
        (Finset.range N).sum (fun i => symmRV Y i p)| ≤
        |(Finset.range n).sum (fun i => symmRV Y i p) - (S p.1 - S p.2)| +
        |(Finset.range N).sum (fun i => symmRV Y i p) - (S p.1 - S p.2)| := by
      have hring : (Finset.range n).sum (fun i => symmRV Y i p) -
          (Finset.range N).sum (fun i => symmRV Y i p) =
          ((Finset.range n).sum (fun i => symmRV Y i p) - (S p.1 - S p.2)) -
          ((Finset.range N).sum (fun i => symmRV Y i p) - (S p.1 - S p.2)) := by ring
      rw [hring]
      exact abs_sub _ _
    linarith [htri, hp]
  have hUlt : (μ.prod μ) {p | (1:ℝ)/2 < |Sblk p|} < ENNReal.ofReal c := by
    have hle : (μ.prod μ) {p | (1:ℝ)/2 < |Sblk p|} ≤
        (μ.prod μ) {p | ENNReal.ofReal (1 / 4 : ℝ) ≤
          edist ((Finset.range n).sum (fun i => symmRV Y i p)) (S p.1 - S p.2)} +
        (μ.prod μ) {p | ENNReal.ofReal (1 / 4 : ℝ) ≤
          edist ((Finset.range N).sum (fun i => symmRV Y i p)) (S p.1 - S p.2)} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    have hNn' : (μ.prod μ) {p | ENNReal.ofReal (1 / 4 : ℝ) ≤
          edist ((Finset.range n).sum (fun i => symmRV Y i p)) (S p.1 - S p.2)} ≤
        ENNReal.ofReal (c / 4) := hN n hNn
    have hNN : (μ.prod μ) {p | ENNReal.ofReal (1 / 4 : ℝ) ≤
          edist ((Finset.range N).sum (fun i => symmRV Y i p)) (S p.1 - S p.2)} ≤
        ENNReal.ofReal (c / 4) := hN N le_rfl
    have hsumc : ENNReal.ofReal (c / 4) + ENNReal.ofReal (c / 4) = ENNReal.ofReal (c / 2) := by
      rw [← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ c / 4) (by linarith : (0:ℝ) ≤ c / 4)]
      congr 1; ring
    have hlt : ENNReal.ofReal (c / 2) < ENNReal.ofReal c := by
      rw [ENNReal.ofReal_lt_ofReal_iff (by linarith : (0:ℝ) < c)]
      linarith
    have hle2 : (μ.prod μ) {p | ENNReal.ofReal (1 / 4 : ℝ) ≤
          edist ((Finset.range n).sum (fun i => symmRV Y i p)) (S p.1 - S p.2)} +
        (μ.prod μ) {p | ENNReal.ofReal (1 / 4 : ℝ) ≤
          edist ((Finset.range N).sum (fun i => symmRV Y i p)) (S p.1 - S p.2)} ≤
        ENNReal.ofReal (c / 2) := by
      rw [← hsumc]
      exact add_le_add hNn' hNN
    exact lt_of_le_of_lt (le_trans hle hle2) hlt
  exact (not_lt_of_ge hPc hUlt).elim

/-- **Mean step of three-series necessity.** For a uniformly bounded
independent sequence with summable variances whose partial sums converge
almost surely, the partial sums of the means converge (to some limit).
Proved by centering and applying the canonical centered-sum convergence
theorem with an `L¹` bound from the total variance. The mean partial sums
are the difference of the two convergent series at a single sample point. -/
theorem tendsto_sum_integral_of_bounded_ae_tendsto {Y : ℕ → Ω → ℝ}
    (hYmeas : ∀ n, Measurable (Y n)) (hYindep : iIndepFun Y μ)
    {A : ℝ} (hYbdd : ∀ n ω, |Y n ω| ≤ A)
    (hVar : Summable (fun n => variance (Y n) μ))
    (hYtend : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => Y i ω)) atTop (nhds (S ω))) :
    ∃ L : ℝ, Tendsto (fun n => ∑ k ∈ Finset.range n, ∫ ω, Y k ω ∂μ) atTop (nhds L) := by
  classical
  have hYint : ∀ n, Integrable (Y n) μ := fun n =>
    Integrable.of_bound (hYmeas n).aestronglyMeasurable A
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hYbdd n ω)
  -- Means, centered variables, and centered partial sums.
  set m : ℕ → ℝ := fun n => ∫ ω, Y n ω ∂μ with hmdef
  set C : ℕ → Ω → ℝ := fun n ω => Y n ω - m n with hCdef
  set f : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range (n + 1), C k ω with hfdef
  -- Bridge between the pointwise lambda and the Pi-sum form.
  have hPi : ∀ n, f n = ∑ k ∈ Finset.range (n + 1), C k := fun n =>
    funext fun ω => (Finset.sum_apply _ _ _).symm
  have hCmeas : ∀ n, Measurable (C n) := fun n => (hYmeas n).sub measurable_const
  have hCindep : iIndepFun C μ := by
    have h := hYindep.comp (fun n (y : ℝ) => y - m n)
      (fun _ => measurable_id'.sub measurable_const)
    exact h
  have hCint : ∀ n, Integrable (C n) μ := fun n =>
    (hYint n).sub (integrable_const (m n))
  have hCmean : ∀ n, ∫ ω, C n ω ∂μ = 0 := by
    intro n
    have h1 : ∫ ω, C n ω ∂μ = ∫ ω, Y n ω ∂μ - m n := by
      show ∫ ω, (Y n ω - m n) ∂μ = ∫ ω, Y n ω ∂μ - m n
      rw [integral_sub (hYint n) (integrable_const (m n))]
      simp [integral_const, Measure.real]
    rw [h1]
    exact sub_self _
  have hm_abs : ∀ n, |m n| ≤ A := by
    intro n
    have h1 : |m n| ≤ ∫ ω, |Y n ω| ∂μ := by
      calc |m n| = ‖∫ ω, Y n ω ∂μ‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ ω, ‖Y n ω‖ ∂μ := norm_integral_le_integral_norm _
        _ = ∫ ω, |Y n ω| ∂μ := by simp only [Real.norm_eq_abs]
    have h2 : ∫ ω, |Y n ω| ∂μ ≤ A := by
      calc ∫ ω, |Y n ω| ∂μ ≤ ∫ _ω, A ∂μ := by
            apply integral_mono_ae (hYint n).norm (integrable_const A)
            filter_upwards with ω
            exact hYbdd n ω
        _ = A := by rw [integral_const]; simp [Measure.real]
    exact h1.trans h2
  have hCbd : ∀ n ω, |C n ω| ≤ 2 * A := by
    intro n ω
    show |Y n ω - m n| ≤ 2 * A
    calc |Y n ω - m n| ≤ |Y n ω| + |m n| := abs_sub _ _
      _ ≤ A + A := add_le_add (hYbdd n ω) (hm_abs n)
      _ = 2 * A := by ring
  have hCmemLp : ∀ k, MemLp (C k) 2 μ := fun k =>
    MemLp.of_bound (hCmeas k).aestronglyMeasurable (2 * A)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hCbd k ω)
  have hfbound : ∀ n ω, |f n ω| ≤ ((Finset.range (n + 1)).card : ℝ) * (2 * A) := by
    intro n ω
    show |∑ k ∈ Finset.range (n + 1), C k ω| ≤ ((Finset.range (n + 1)).card : ℝ) * (2 * A)
    calc |∑ k ∈ Finset.range (n + 1), C k ω| ≤ ∑ k ∈ Finset.range (n + 1), |C k ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range (n + 1), (2 * A) :=
        Finset.sum_le_sum (fun k _ => hCbd k ω)
      _ = ((Finset.range (n + 1)).card : ℝ) * (2 * A) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hfMemLp : ∀ n, MemLp (f n) 2 μ := fun n =>
    MemLp.of_bound (integrable_finsetSum _ (fun k _ => hCint k)).aestronglyMeasurable
      (((Finset.range (n + 1)).card : ℝ) * (2 * A))
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hfbound n ω)
  -- The centered sums are `L¹`-bounded by the square root of the total variance.
  have hEfn : ∀ n, ∫ ω, f n ω ∂μ = 0 := by
    intro n
    show ∫ ω, (∑ k ∈ Finset.range (n + 1), C k ω) ∂μ = 0
    rw [integral_finsetSum _ (fun k _ => hCint k)]
    exact Finset.sum_eq_zero (fun k _ => hCmean k)
  have hVarC : ∀ k, variance (C k) μ = variance (Y k) μ := by
    intro k
    show variance (fun ω => Y k ω - m k) μ = variance (Y k) μ
    exact variance_sub_const (hYmeas k).aestronglyMeasurable (m k)
  have hVarSum : ∀ n, variance (f n) μ =
      ∑ k ∈ Finset.range (n + 1), variance (C k) μ := by
    intro n
    rw [hPi n]
    have hpair : Set.Pairwise ↑(Finset.range (n + 1)) (fun i j => C i ⟂ᵢ[μ] C j) := by
      intro i hi j hj hij
      have hYij := hYindep.indepFun (show i ≠ j from hij)
      exact hYij.comp
        (measurable_id'.sub measurable_const) (measurable_id'.sub measurable_const)
    exact IndepFun.variance_sum (fun k _ => hCmemLp k) hpair
  have hVarfn : ∀ n, ∫ ω, (f n ω) ^ 2 ∂μ =
      ∑ k ∈ Finset.range (n + 1), variance (Y k) μ := by
    intro n
    have hI : ∫ ω, (f n ω) ^ 2 ∂μ = variance (f n) μ := by
      rw [variance_eq_sub (hfMemLp n), hEfn n]
      simp [Pi.pow_apply]
    rw [hI, hVarSum n]
    exact Finset.sum_congr rfl (fun k _ => hVarC k)
  have hV : ∀ n, ∫ ω, ‖f n ω‖ ^ (2 : ℝ) ∂μ ≤
      ∑' k, variance (Y k) μ := by
    intro n
    have hEq : ∫ ω, ‖f n ω‖ ^ (2 : ℝ) ∂μ = ∫ ω, (f n ω) ^ 2 ∂μ := by
      apply integral_congr_ae (ae_of_all _ fun ω => ?_)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs,
        sq_abs]
    rw [hEq, hVarfn n]
    exact hVar.sum_le_tsum _ (fun i _ => variance_nonneg _ _)
  have hBdd : ∀ n, eLpNorm (f n) 1 μ ≤
      ENNReal.ofReal (Real.sqrt (∑' k, variance (Y k) μ)) := by
    intro n
    exact ProbabilityTheory.eLpNorm_one_le_sqrt_integral_sq (hfMemLp n) (hV n)
  have hCenteredAe : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) :=
    ProbabilityTheory.ae_tendsto_sum_of_indep_centered_L1bdd
      (fun n => (hCmeas n).stronglyMeasurable) hCindep hCmean hCint
      (R := ⟨Real.sqrt (∑' k, variance (Y k) μ), Real.sqrt_nonneg _⟩)
      (fun n => by
        have h := hBdd n
        rwa [ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg _)] at h)
  -- Extract a single sample point where both the centered sums and the
  -- original sums converge.
  obtain ⟨S, hS⟩ := hYtend
  have hboth : ∀ᵐ ω ∂μ, (∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c)) ∧
      Tendsto (fun n => ∑ i ∈ Finset.range n, Y i ω) atTop (nhds (S ω)) :=
    (hCenteredAe.and hS)
  obtain ⟨ω₀, hω₀⟩ := hboth.exists
  obtain ⟨c, hc⟩ := hω₀.1
  -- The mean partial sums over `range (n + 1)` converge; shift back by one.
  have hM : ∀ n, (∑ k ∈ Finset.range (n + 1), m k) =
      (∑ i ∈ Finset.range (n + 1), Y i ω₀) - f n ω₀ := by
    intro n
    have hfn : f n ω₀ = ∑ k ∈ Finset.range (n + 1), (Y k ω₀ - m k) := by
      show (∑ k ∈ Finset.range (n + 1), C k ω₀) = _
      apply Finset.sum_congr rfl
      intro k _
      rfl
    rw [hfn, Finset.sum_sub_distrib, eq_sub_iff_add_eq, add_sub_cancel]
  have hM' : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), m k) atTop (nhds (S ω₀ - c)) := by
    have hYshift : Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), Y i ω₀) atTop (nhds (S ω₀)) :=
      (tendsto_add_atTop_iff_nat 1).mpr hω₀.2
    exact (hYshift.sub hc).congr (fun n => (hM n).symm)
  have hMfin : Tendsto (fun n => ∑ k ∈ Finset.range n, m k) atTop (nhds (S ω₀ - c)) :=
    (tendsto_add_atTop_iff_nat 1).mp hM'
  exact ⟨S ω₀ - c, hMfin⟩

/-- **Kolmogorov three-series necessity, series (2)–(3).** If the partial
sums of an independent sequence `Xₙ` converge almost surely, then for
every `A > 0` the truncations `Yₙ = Xₙ · 1_{|Xₙ| ≤ A}` have convergent
mean partial sums and summable variances. This is the corrected form of
v1's `summable_mean_and_variance_of_ae_tendsto_ax`: v1 claimed the means
themselves are `Summable`, which is false (see
`summable_mean_necessity_false`); only convergence of the mean partial
sums holds. Series (1) uses the public theorem from
`ThreeSeriesTailProb`. -/
theorem three_series_necessity_mean_variance {X : ℕ → Ω → ℝ}
    (hXmeas : ∀ n, Measurable (X n)) (hXindep : iIndepFun X μ)
    {A : ℝ} (hA : 0 < A)
    (hXtend : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => X i ω)) atTop (nhds (S ω))) :
    (∃ L : ℝ, Tendsto (fun n => ∑ k ∈ Finset.range n,
      ∫ ω, truncatedRV X A k ω ∂μ) atTop (nhds L)) ∧
    Summable (fun n => variance (truncatedRV X A n) μ) := by
  have h1 := ProbabilityTheory.summable_tail_prob_of_ae_tendsto hXmeas hXindep hA hXtend
  have hEv :=
    ProbabilityTheory.KolmogorovThreeSeries.ae_eventually_truncation_eq (X := X) (A := A) h1
  have hYtend :=
    ProbabilityTheory.KolmogorovThreeSeries.ae_tendsto_of_ae_eventually_eq_and_ae_tendsto hEv hXtend
  have hYmeas := measurable_truncatedRV hXmeas A
  have hYindep := iIndepFun_truncatedRV hXindep A
  have hYbdd : ∀ n ω, |truncatedRV X A n ω| ≤ A := fun n ω =>
    abs_truncatedRV_le hA.le n ω
  have hVar := summable_variance_of_bounded_ae_tendsto hYmeas hYindep hA hYbdd hYtend
  exact ⟨tendsto_sum_integral_of_bounded_ae_tendsto hYmeas hYindep hYbdd hVar hYtend, hVar⟩

/-- **The `Summable`-means necessity claim in v1 is false.** The
deterministic sequence `X k ω = (-1)^k / (k + 1)` on the one-point
probability space `(Unit, dirac ())` has converging partial sums, is
constant (hence measurable and independent), agrees with its truncations
at `A = 1`, and has all variances `0` — yet its means
`∫ truncatedRV X 1 k = (-1)^k / (k + 1)` are not `Summable`, since
`Summable.abs` would force summability of the harmonic series. This is
why the ported necessity theorem above states convergence of the mean
partial sums rather than `Summable` of the means. The statement records
convergence of both the original and the truncated partial sums: the
truncated form is the hypothesis of v1's (false) unproved lemma, and the original
form is what the corrected assembly theorem needs. -/
theorem summable_mean_necessity_false :
    ∃ (X : ℕ → Unit → ℝ) (A : ℝ), 0 < A ∧
      (∀ n, Measurable (X n)) ∧ iIndepFun X (Measure.dirac ()) ∧
      (∃ S : Unit → ℝ, ∀ᵐ ω ∂(Measure.dirac ()),
        Tendsto (fun n => (Finset.range n).sum (fun i => X i ω))
          atTop (nhds (S ω))) ∧
      (∃ S : Unit → ℝ, ∀ᵐ ω ∂(Measure.dirac ()),
        Tendsto (fun n => (Finset.range n).sum (fun i => truncatedRV X A i ω))
          atTop (nhds (S ω))) ∧
      ¬ Summable (fun n => ∫ ω, truncatedRV X A n ω ∂(Measure.dirac ())) := by
  classical
  refine ⟨fun n _ => (-1 : ℝ) ^ n / (n + 1 : ℝ), 1, one_pos, fun _ => measurable_const,
    ?_, ?_, ?_, ?_⟩
  · -- Constants are independent: the preimage of a set under a constant
    -- function is `univ` or `∅`, and both sides of the independence
    -- criterion are `1` or `0` accordingly.
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    have hpre : ∀ i : ℕ, (fun _ : Unit => (-1 : ℝ) ^ i / (i + 1 : ℝ)) ⁻¹' sets i =
        if (-1 : ℝ) ^ i / (i + 1 : ℝ) ∈ sets i then Set.univ else ∅ := by
      intro i
      by_cases h : (-1 : ℝ) ^ i / (i + 1 : ℝ) ∈ sets i
      · rw [ite_eq_left h]
        ext x
        simp [h]
      · rw [ite_eq_right h]
        ext x
        simp [h]
    by_cases hall : ∀ i ∈ S, (-1 : ℝ) ^ i / (i + 1 : ℝ) ∈ sets i
    · have hL : (⋂ i ∈ S, (fun _ : Unit => (-1 : ℝ) ^ i / (i + 1 : ℝ)) ⁻¹' sets i) =
          Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        rw [Set.mem_iInter₂]
        intro i hi
        rw [hpre i, ite_eq_left (hall i hi)]
        exact Set.mem_univ x
      rw [hL, Measure.dirac_apply_of_mem (Set.mem_univ ())]
      rw [Finset.prod_congr rfl (fun i hi => by
        rw [hpre i, ite_eq_left (hall i hi), Measure.dirac_apply_of_mem (Set.mem_univ ())]),
        Finset.prod_const_one]
    · push Not at hall
      obtain ⟨j, hj, hjn⟩ := hall
      have hL : (⋂ i ∈ S, (fun _ : Unit => (-1 : ℝ) ^ i / (i + 1 : ℝ)) ⁻¹' sets i) = ∅ := by
        apply Set.eq_empty_of_subset_empty
        calc (⋂ i ∈ S, (fun _ : Unit => (-1 : ℝ) ^ i / (i + 1 : ℝ)) ⁻¹' sets i)
            ⊆ (fun _ : Unit => (-1 : ℝ) ^ j / (j + 1 : ℝ)) ⁻¹' sets j :=
              Set.iInter₂_subset j hj
          _ = ∅ := by rw [hpre j, ite_eq_right hjn]
      rw [hL, measure_empty]
      symm
      apply Finset.prod_eq_zero hj
      rw [hpre j, ite_eq_right hjn, measure_empty]
  · -- The original partial sums converge (alternating harmonic series),
    -- which is what the corrected assembly theorem needs as input.
    obtain ⟨l, hl⟩ := Antitone.tendsto_alternating_series_of_tendsto_zero
      (f := fun k : ℕ => 1 / (k + 1 : ℝ)) (by
        intro a b hab
        refine one_div_le_one_div_of_le (by positivity) ?_
        have h : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        linarith)
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine ⟨fun _ => l, ?_⟩
    rw [ae_dirac_eq, Filter.eventually_pure]
    exact hl.congr (fun n => Finset.sum_congr rfl (fun i _ => mul_one_div _ _))
  · -- The alternating harmonic series converges; truncations at `A = 1`
    -- agree with the sequence since `|(-1)^k / (k + 1)| = 1 / (k + 1) ≤ 1`.
    obtain ⟨l, hl⟩ := Antitone.tendsto_alternating_series_of_tendsto_zero
      (f := fun k : ℕ => 1 / (k + 1 : ℝ)) (by
        intro a b hab
        refine one_div_le_one_div_of_le (by positivity) ?_
        have h : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        linarith)
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine ⟨fun _ => l, ?_⟩
    rw [ae_dirac_eq, Filter.eventually_pure]
    have hEq : ∀ n, (Finset.range n).sum (fun i =>
        truncatedRV (fun n _ => (-1 : ℝ) ^ n / (n + 1 : ℝ)) 1 i ()) =
        (Finset.range n).sum (fun i => (-1 : ℝ) ^ i * (1 / (i + 1 : ℝ))) := by
      intro n
      apply Finset.sum_congr rfl
      intro i _
      have htr : truncatedRV (fun n _ => (-1 : ℝ) ^ n / (n + 1 : ℝ)) 1 i () =
          (-1 : ℝ) ^ i / (i + 1 : ℝ) := by
        rw [truncatedRV_apply]
        show (if |(-1 : ℝ) ^ i / (i + 1 : ℝ)| ≤ 1 then (-1 : ℝ) ^ i / (i + 1 : ℝ)
          else 0) = (-1 : ℝ) ^ i / (i + 1 : ℝ)
        rw [ite_eq_left (by
          rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
            abs_of_pos (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
          exact div_le_one_of_le₀ (by
            have h : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith) (by positivity))]
      rw [htr, mul_one_div]
    exact hl.congr (fun n => (hEq n).symm)
  · -- The means are the alternating harmonic terms, which are not summable.
    have hInt : ∀ n, ∫ ω, truncatedRV (fun n _ => (-1 : ℝ) ^ n / (n + 1 : ℝ)) 1 n ω
        ∂(Measure.dirac ()) = (-1 : ℝ) ^ n / (n + 1 : ℝ) := by
      intro n
      rw [MeasureTheory.integral_dirac]
      rw [truncatedRV_apply]
      show (if |(-1 : ℝ) ^ n / (n + 1 : ℝ)| ≤ 1 then (-1 : ℝ) ^ n / (n + 1 : ℝ)
        else 0) = (-1 : ℝ) ^ n / (n + 1 : ℝ)
      rw [ite_eq_left (by
        rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        exact div_le_one_of_le₀ (by
          have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) (by positivity))]
    simp only [hInt]
    intro h
    have h2 : Summable (fun k : ℕ => 1 / (k + 1 : ℝ)) := by
      refine h.abs.congr (fun k => ?_)
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    have h3 : Summable (fun k : ℕ => 1 / (k : ℝ)) := by
      have hh := (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ)) (k := 1)).mp
      simp only [Nat.cast_add, Nat.cast_one] at hh
      exact hh h2
    exact Real.not_summable_one_div_natCast h3

end MathlibExt.Probability.ThreeSeriesNecessity

end
