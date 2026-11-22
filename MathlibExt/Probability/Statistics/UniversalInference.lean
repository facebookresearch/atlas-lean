/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.PiWithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Universal inference: the split likelihood ratio

Wasserman, Ramdas and Balakrishnan, *Universal inference*, Proc. Natl. Acad. Sci. USA 117 (2020)
16880–16890 (cited here from arXiv:1912.11436v4, 21 October 2022), split the sample into two
independent parts `D₁` and `D₀`. Any estimator `θ̂₁` is computed from `D₁`, and the likelihood
`L₀` is computed from `D₀`. The split likelihood ratio statistic is `T(θ) = L₀(θ̂₁) / L₀(θ)`.
Its key property is that a likelihood ratio has mean at most one under the denominator:
`E_{θ*}[L₀(ψ) / L₀(θ*)] ≤ 1` for every fixed `ψ`. Markov's inequality then gives, with no
regularity conditions and in finite samples:

* the universal confidence set `C = {θ : T(θ) ≤ 1/α}` covers the true parameter with probability
  at least `1 - α` (their Theorem 1);
* the split likelihood ratio test, which rejects `H₀ : θ* ∈ Θ₀` when
  `U = L₀(θ̂₁) / L₀(θ̂₀) > 1/α` with `θ̂₀` the maximum likelihood estimator over `Θ₀`, has type I
  error at most `α` (their Theorem 3).

The statements are given for a general dominated model on the sample space of `D₀`: densities
`q θ` with respect to a measure `ν` with `∫ q θ dν ≤ 1` (the paper's Remark 2 notes this
generality), and then for `D₀` an i.i.d. sample of size `m` from densities `p θ`, with
`L₀(θ) = ∏ᵢ p θ (yᵢ)`, as in the paper. `D₁` takes values in an arbitrary measurable space `𝒲`
with law `ρ`, and the joint law of `(D₁, D₀)` is the product `ρ ⊗ P_{θ*}` (independence of the
two halves).

Ratios are written multiplicatively in `ℝ≥0∞`: `T(θ) ≤ 1/α` is `L₀(θ̂₁) ≤ α⁻¹ * L₀(θ)` and
`U > 1/α` is `α⁻¹ * L₀(θ̂₀) < L₀(θ̂₁)`. This fixes the convention `0/0 = 0` for the ratios
(a parameter with `L₀(θ̂₁) = L₀(θ) = 0` is kept in the set, and the test does not reject when
`L₀(θ̂₁) = L₀(θ̂₀) = 0`). The convention does not affect the coverage and type I error
statements, for which it matters only on samples of probability zero under the true parameter;
it does decide which other parameters belong to the set (when `L₀(θ̂₁) = 0`, every `θ` with
`L₀(θ) = 0` is in it, which can happen with positive probability). For the
test only the inequality `L₀(θ) ≤ L₀(θ̂₀)` for `θ ∈ Θ₀` is assumed, which every maximiser of the
likelihood over `Θ₀` satisfies. The crossfit variants and the sequential (anytime-valid)
version are not formalized here.

## Main definitions

* `universalConfidenceSet q α θ₁ y`: `{θ | q θ₁ y ≤ α⁻¹ * q θ y}`.

## Main results

* `withDensity_inv_mul_lt_le`: Markov's inequality for a likelihood ratio, the fixed-`ψ` step.
* `measure_not_mem_universalConfidenceSet_le`, `measure_not_mem_universalConfidenceSet_le_pi`:
  Theorem 1 (finite-sample coverage), general and i.i.d.
* `measure_splitLRT_reject_le`, `measure_splitLRT_reject_le_pi`: Theorem 3 (type I error of
  the split likelihood ratio test), general and i.i.d.

## Relation to `MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.UniversalInference`

That module proves the same Theorems 1 and 3 (`measure_not_mem_universalConfidenceSet_le`,
`measure_splitLRTRejects_le`) for real-valued densities, by showing that the split likelihood
ratio is an e-value (`isEValue_splitLR`), and adds a valid p-value and boundary variants. This
module uses `ℝ≥0∞` densities and Markov's inequality directly, and adds the i.i.d. forms (`_pi`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Probability.Statistics.UniversalInference

variable {Θ 𝒴 𝒲 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝒴] [MeasurableSpace 𝒲]

/-- **Markov's inequality for a likelihood ratio.** Let `q₀` and `q₁` be measurable densities
with respect to `ν`, with `∫ q₁ dν ≤ 1`. Under the law `ν.withDensity q₀`, the probability that
the likelihood ratio `q₁ / q₀` exceeds `1/α`, written `α⁻¹ * q₀ < q₁`, is at most `α`, for every
`0 < α < ∞`. This is the bound `P_{θ*}(T_n(θ*) > 1/α) ≤ α E_{θ*}[T_n(θ*)] ≤ α` of display (7) of
Wasserman, Ramdas and Balakrishnan (arXiv:1912.11436v4) for a fixed alternative `ψ`, proved
without dividing: on the event, `q₀ ≤ α q₁`. -/
theorem withDensity_inv_mul_lt_le (ν : Measure 𝒴) {q₀ q₁ : 𝒴 → ℝ≥0∞} (hq₀ : Measurable q₀)
    (hq₁ : Measurable q₁) (h1 : ∫⁻ y, q₁ y ∂ν ≤ 1) {α : ℝ≥0∞} (hα0 : α ≠ 0) (hαtop : α ≠ ∞) :
    ν.withDensity q₀ {y | α⁻¹ * q₀ y < q₁ y} ≤ α := by
  have hA : MeasurableSet {y | α⁻¹ * q₀ y < q₁ y} :=
    measurableSet_lt (hq₀.const_mul _) hq₁
  rw [withDensity_apply _ hA]
  calc ∫⁻ y in {y | α⁻¹ * q₀ y < q₁ y}, q₀ y ∂ν
      ≤ ∫⁻ y in {y | α⁻¹ * q₀ y < q₁ y}, α * q₁ y ∂ν := by
        refine setLIntegral_mono (hq₁.const_mul _) fun y hy => ?_
        calc q₀ y = α * (α⁻¹ * q₀ y) := by
              rw [← mul_assoc, ENNReal.mul_inv_cancel hα0 hαtop, one_mul]
          _ ≤ α * q₁ y := by gcongr; exact le_of_lt hy
    _ ≤ ∫⁻ y, α * q₁ y ∂ν := setLIntegral_le_lintegral _ _
    _ = α * ∫⁻ y, q₁ y ∂ν := lintegral_const_mul α hq₁
    _ ≤ α * 1 := by gcongr
    _ = α := mul_one α

/-- **Universal confidence set.** For densities `q θ` of the second half of the sample, an
estimate `θ₁` computed from the first half, and an observed second half `y`, the universal set
is `{θ | q θ₁ y ≤ α⁻¹ * q θ y}`, i.e. `{θ : T(θ) ≤ 1/α}` with `T(θ) = L₀(θ̂₁) / L₀(θ)`
(Wasserman, Ramdas and Balakrishnan, arXiv:1912.11436v4, equations (3)–(4)), written without
division. -/
def universalConfidenceSet (q : Θ → 𝒴 → ℝ≥0∞) (α : ℝ≥0∞) (θ₁ : Θ) (y : 𝒴) : Set Θ :=
  {θ | q θ₁ y ≤ α⁻¹ * q θ y}

/-- **Finite-sample validity of the universal confidence set.** Let `q θ` be densities with
respect to `ν` on the sample space of `D₀`, jointly measurable in `(θ, y)`, with
`∫ q θ dν ≤ 1` for every `θ`. Let `D₁` have law `ρ` (a probability measure) independently of
`D₀`, whose law is `ν.withDensity (q θ*)`, and let `θ̂₁` be any measurable estimator computed from
`D₁`. Then for `0 < α < ∞` the universal set misses `θ*` with probability at most `α`
(Wasserman, Ramdas and Balakrishnan, arXiv:1912.11436v4, Theorem 1, in the generality of their
Remark 2). -/
theorem measure_not_mem_universalConfidenceSet_le (ν : Measure 𝒴) [SFinite ν]
    (ρ : Measure 𝒲) [IsProbabilityMeasure ρ] {q : Θ → 𝒴 → ℝ≥0∞}
    (hq : Measurable (Function.uncurry q)) (hq1 : ∀ θ, ∫⁻ y, q θ y ∂ν ≤ 1)
    {θhat₁ : 𝒲 → Θ} (hθhat₁ : Measurable θhat₁) (θstar : Θ) {α : ℝ≥0∞} (hα0 : α ≠ 0)
    (hαtop : α ≠ ∞) :
    (ρ.prod (ν.withDensity (q θstar)))
        {p | θstar ∉ universalConfidenceSet q α (θhat₁ p.1) p.2} ≤ α := by
  have hqθ : ∀ θ, Measurable (q θ) := fun θ => hq.comp (measurable_const.prodMk measurable_id)
  have hS : MeasurableSet {p : 𝒲 × 𝒴 | θstar ∉ universalConfidenceSet q α (θhat₁ p.1) p.2} := by
    simp only [universalConfidenceSet, Set.mem_ofPred_eq, not_le]
    exact measurableSet_lt (((hqθ θstar).comp measurable_snd).const_mul _)
      (hq.comp ((hθhat₁.comp measurable_fst).prodMk measurable_snd))
  rw [Measure.prod_apply hS]
  calc ∫⁻ w, ν.withDensity (q θstar)
          (Prod.mk w ⁻¹' {p | θstar ∉ universalConfidenceSet q α (θhat₁ p.1) p.2}) ∂ρ
      ≤ ∫⁻ _w, α ∂ρ := by
        refine lintegral_mono fun w => ?_
        have : Prod.mk w ⁻¹' {p : 𝒲 × 𝒴 | θstar ∉ universalConfidenceSet q α (θhat₁ p.1) p.2} =
            {y | α⁻¹ * q θstar y < q (θhat₁ w) y} := by
          ext y
          simp [universalConfidenceSet]
        rw [this]
        exact withDensity_inv_mul_lt_le ν (hqθ θstar) (hqθ (θhat₁ w)) (hq1 _) hα0 hαtop
    _ = α := by rw [lintegral_const, measure_univ, mul_one]

/-- **Type I error of the split likelihood ratio test.** In the setting of
`measure_not_mem_universalConfidenceSet_le`, let `Θ₀` be a null set containing the true parameter
`θ*`, and let `θ̂₀` map each second half `y` to a parameter whose likelihood dominates that of
every element of `Θ₀` (for instance the maximum likelihood estimator over `Θ₀`). The split
likelihood ratio test rejects when `U = q (θ̂₁) y / q (θ̂₀ y) y > 1/α`. Its rejection probability is
at most `α` (Wasserman, Ramdas and Balakrishnan, arXiv:1912.11436v4, Theorem 3, in the generality
of their Remark 2). -/
theorem measure_splitLRT_reject_le (ν : Measure 𝒴) [SFinite ν]
    (ρ : Measure 𝒲) [IsProbabilityMeasure ρ] {q : Θ → 𝒴 → ℝ≥0∞}
    (hq : Measurable (Function.uncurry q)) (hq1 : ∀ θ, ∫⁻ y, q θ y ∂ν ≤ 1)
    {θhat₁ : 𝒲 → Θ} (hθhat₁ : Measurable θhat₁) {Θ₀ : Set Θ} {θhat₀ : 𝒴 → Θ}
    (hθhat₀ : ∀ y, ∀ θ ∈ Θ₀, q θ y ≤ q (θhat₀ y) y) {θstar : Θ} (hθstar : θstar ∈ Θ₀)
    {α : ℝ≥0∞} (hα0 : α ≠ 0) (hαtop : α ≠ ∞) :
    (ρ.prod (ν.withDensity (q θstar))) {p | α⁻¹ * q (θhat₀ p.2) p.2 < q (θhat₁ p.1) p.2} ≤ α := by
  refine le_trans (measure_mono fun p hp => ?_)
    (measure_not_mem_universalConfidenceSet_le ν ρ hq hq1 hθhat₁ θstar hα0 hαtop)
  simp only [universalConfidenceSet, Set.mem_ofPred_eq, not_le] at hp ⊢
  exact lt_of_le_of_lt (by gcongr; exact hθhat₀ p.2 θstar hθstar) hp

section IID

variable {m : ℕ}

private theorem iid_setup (ν : Measure 𝒴) [SigmaFinite ν] {p : Θ → 𝒴 → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) (hp1 : ∀ θ, ∫⁻ y, p θ y ∂ν ≤ 1) (θstar : Θ) :
    Measurable (Function.uncurry fun θ (y : Fin m → 𝒴) => ∏ i, p θ (y i)) ∧
      (∀ θ, ∫⁻ y, ∏ i, p θ (y i) ∂Measure.pi (fun _ : Fin m => ν) ≤ 1) ∧
      Measure.pi (fun _ : Fin m => ν.withDensity (p θstar)) =
        (Measure.pi fun _ : Fin m => ν).withDensity fun y => ∏ i, p θstar (y i) := by
  have hpθ : ∀ θ, Measurable (p θ) := fun θ => hp.comp (measurable_const.prodMk measurable_id)
  refine ⟨?_, fun θ => ?_, ?_⟩
  · exact Finset.measurable_prod _ fun i _ =>
      hp.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  · rw [lintegral_fintype_prod_eq_prod (μ := fun _ : Fin m => ν) (fun _ => hpθ θ)]
    exact Finset.prod_le_one fun _ _ => hp1 θ
  · have : IsFiniteMeasure (ν.withDensity (p θstar)) :=
      isFiniteMeasure_withDensity (ne_top_of_le_ne_top ENNReal.one_ne_top (hp1 θstar))
    exact Measure.pi_withDensity (μ := fun _ : Fin m => ν) (fun _ => hpθ θstar)

/-- **Universal confidence set for an i.i.d. sample.** Let `p θ` be probability densities (or
sub-densities, `∫ p θ dν ≤ 1`) with respect to a σ-finite measure `ν`, jointly measurable in
`(θ, y)`. Let `D₀ = (Y_1, …, Y_m)` be i.i.d. with density `p θ*`, independent of `D₁ ∼ ρ`, and let
`θ̂₁` be any measurable estimator computed from `D₁`. With the split likelihood
`L₀(θ) = ∏ᵢ p θ (Yᵢ)`, the universal set `{θ : L₀(θ̂₁) ≤ α⁻¹ L₀(θ)}` misses `θ*` with probability
at most `α`, for every `0 < α < ∞` (Wasserman, Ramdas and Balakrishnan, arXiv:1912.11436v4,
Theorem 1). -/
theorem measure_not_mem_universalConfidenceSet_le_pi (ν : Measure 𝒴) [SigmaFinite ν]
    (ρ : Measure 𝒲) [IsProbabilityMeasure ρ] {p : Θ → 𝒴 → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) (hp1 : ∀ θ, ∫⁻ y, p θ y ∂ν ≤ 1)
    {θhat₁ : 𝒲 → Θ} (hθhat₁ : Measurable θhat₁) (θstar : Θ) {α : ℝ≥0∞} (hα0 : α ≠ 0)
    (hαtop : α ≠ ∞) :
    (ρ.prod (Measure.pi fun _ : Fin m => ν.withDensity (p θstar)))
        {w | θstar ∉ universalConfidenceSet (fun θ (y : Fin m → 𝒴) => ∏ i, p θ (y i)) α
          (θhat₁ w.1) w.2} ≤ α := by
  obtain ⟨hq, hq1, hpi⟩ := iid_setup (m := m) ν hp hp1 θstar
  rw [hpi]
  exact measure_not_mem_universalConfidenceSet_le _ ρ hq hq1 hθhat₁ θstar hα0 hαtop

/-- **Split likelihood ratio test for an i.i.d. sample.** In the setting of
`measure_not_mem_universalConfidenceSet_le_pi`, let `Θ₀` contain the true parameter `θ*` and let
`θ̂₀` be a maximiser of the split likelihood `L₀` over `Θ₀` (only `L₀(θ) ≤ L₀(θ̂₀)` for `θ ∈ Θ₀` is
used). The split likelihood ratio test, which rejects `H₀ : θ* ∈ Θ₀` when
`L₀(θ̂₁) / L₀(θ̂₀) > 1/α`, has type I error at most `α`, for every `0 < α < ∞` (Wasserman, Ramdas
and Balakrishnan, arXiv:1912.11436v4, Theorem 3). -/
theorem measure_splitLRT_reject_le_pi (ν : Measure 𝒴) [SigmaFinite ν]
    (ρ : Measure 𝒲) [IsProbabilityMeasure ρ] {p : Θ → 𝒴 → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) (hp1 : ∀ θ, ∫⁻ y, p θ y ∂ν ≤ 1)
    {θhat₁ : 𝒲 → Θ} (hθhat₁ : Measurable θhat₁) {Θ₀ : Set Θ} {θhat₀ : (Fin m → 𝒴) → Θ}
    (hθhat₀ : ∀ y, ∀ θ ∈ Θ₀, ∏ i, p θ (y i) ≤ ∏ i, p (θhat₀ y) (y i)) {θstar : Θ}
    (hθstar : θstar ∈ Θ₀) {α : ℝ≥0∞} (hα0 : α ≠ 0) (hαtop : α ≠ ∞) :
    (ρ.prod (Measure.pi fun _ : Fin m => ν.withDensity (p θstar)))
        {w | α⁻¹ * ∏ i, p (θhat₀ w.2) (w.2 i) < ∏ i, p (θhat₁ w.1) (w.2 i)} ≤ α := by
  obtain ⟨hq, hq1, hpi⟩ := iid_setup (m := m) ν hp hp1 θstar
  rw [hpi]
  exact measure_splitLRT_reject_le (q := fun θ (y : Fin m → 𝒴) => ∏ i, p θ (y i)) _ ρ hq hq1
    hθhat₁ hθhat₀ hθstar hα0 hαtop

end IID

end MathlibExt.Probability.Statistics.UniversalInference
