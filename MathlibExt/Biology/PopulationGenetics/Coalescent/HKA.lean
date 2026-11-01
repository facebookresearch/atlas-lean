/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Tajima
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The Hudson–Kreitman–Aguadé (HKA) test: expectations and variances

The HKA test (Hudson, Kreitman & Aguadé 1987) compares polymorphism within two species `A`, `B`
with divergence between them at `L ≥ 2` loci. Time is in units of `2N` generations, `N` the
size of species `A`; species `B` has size `f N` and their common ancestral population, which
split `T` time units ago, has size `N (1 + f) / 2`. Locus `i` has scaled mutation rate
`θ_i = 4 N u_i`. With `n_A`, `n_B` sampled genes and `C(n) = ∑_{j=1}^{n-1} 1/j = a₁`,
`C₂(n) = ∑_{j=1}^{n-1} 1/j² = a₂`, the neutral expectations are

* `E S_i^A = θ_i C(n_A)`, `Var S_i^A = θ_i C(n_A) + θ_i² C₂(n_A)`;
* `E S_i^B = f θ_i C(n_B)`, `Var S_i^B = f θ_i C(n_B) + (f θ_i)² C₂(n_B)`;
* `E D_i = θ_i (T + (1 + f) / 2)`, `Var D_i = E D_i + (θ_i (1 + f) / 2)²`,

where `S` counts segregating sites and `D_i` is the number of differences between one gene
from each species. The polymorphism moments are Watterson's (`KingmanTimes.integral_segSites`,
`KingmanTimes.variance_segSites`): the genealogy of species `B` is a Kingman coalescent run at
speed `1 / f`, so in the time units of a standard Kingman coalescent its mutation parameter is
`f θ_i`. For the divergence, the two genes' lineages coalesce at time `T + τ`, with
`τ ~ Exp(2 / (1 + f))` the coalescence time of two lineages in the ancestral population, and
given the genealogy `D_i` is Poisson with mean `θ_i (T + τ)` (stated through its conditional
mean and variance); `integral_hkaDivergence` and `variance_hkaDivergence` derive the two
moments.

The HKA statistic is the sum over loci of the three squared standardized deviations. At the
true parameters it has mean `3 L` (`integral_hkaStatistic`). HKA estimate the `L + 2`
parameters by the moment equations `hkaEquations` (which the expected counts satisfy at the
true parameters, `hkaEquations_expected`) and refer the statistic to a `χ²` law with `2L - 2`
degrees of freedom; that law is an approximation and is not formalized.

The identities hold for all real parameters where stated; the biological domain is `θ_i > 0`,
`T ≥ 0`, `f > 0`, `n_A, n_B ≥ 2`.

## Main results

* `hkaPolyMean`, `hkaPolyVar`, `hkaDivMean`, `hkaDivVar`: the HKA expectations and variances.
* `integral_hkaDivergence`, `variance_hkaDivergence`: `E D = θ (T + (1 + f) / 2)` and
  `Var D = E D + (θ (1 + f) / 2)²`.
* `hkaStatistic`, `integral_hkaStatistic`: the HKA statistic has mean `3 L` at the truth.
* `hkaEquations`, `hkaEquations_expected`: HKA's estimating equations.

## References

* R. R. Hudson, M. Kreitman and M. Aguadé, *A test of neutral molecular evolution based on
  nucleotide data*, Genetics 116 (1987), 153–159.
* G. A. Watterson, *On the number of segregating sites in genetical models without
  recombination*, Theor. Popul. Biol. 7 (1975), 256–276.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-- HKA's expected number of segregating sites `θ C(n)` in a sample of `n` genes with scaled
mutation rate `θ` (use `f θ` for species `B`). -/
def hkaPolyMean (θ : ℝ) (n : ℕ) : ℝ := θ * tajimaA1 n

/-- HKA's variance of the number of segregating sites, `θ C(n) + θ² C₂(n)`. -/
def hkaPolyVar (θ : ℝ) (n : ℕ) : ℝ := θ * tajimaA1 n + θ ^ 2 * tajimaA2 n

/-- HKA's expected divergence `θ (T + (1 + f) / 2)`. -/
def hkaDivMean (θ T f : ℝ) : ℝ := θ * (T + (1 + f) / 2)

/-- HKA's variance of the divergence, `θ (T + (1 + f) / 2) + (θ (1 + f) / 2)²`. -/
def hkaDivVar (θ T f : ℝ) : ℝ := hkaDivMean θ T f + (θ * (1 + f) / 2) ^ 2

/-- The ancestral coalescence time has mean `(1 + f) / 2`, so `E[θ (T + τ)] = θ (T + (1+f)/2)`. -/
private theorem integral_mean_hka {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {τ : Ω → ℝ} {θ T f : ℝ} (hf : -1 < f)
    (hτ : HasLaw τ (expMeasure (2 / (1 + f))) μ) :
    μ[fun ω => θ * (T + τ ω)] = hkaDivMean θ T f := by
  have hr : 0 < 2 / (1 + f) := div_pos two_pos (by linarith)
  have hτi := hτ.integrable_of_expMeasure hr
  rw [integral_const_mul, integral_add (integrable_const T) hτi, integral_const,
    hτ.integral_eq_inv_of_expMeasure hr, inv_div]
  simp [hkaDivMean]

/-- **Expected divergence** (Hudson, Kreitman & Aguadé 1987): if the ancestral coalescence time
`τ` is exponential with rate `2 / (1 + f)` and, given the genealogy σ-algebra `m`, the
divergence `D` has conditional mean `θ (T + τ)`, then `E D = θ (T + (1 + f) / 2)`
(for `f > -1`). No integrability hypothesis on `D` is needed: if `D` were not integrable its
conditional expectation would be `0` (Mathlib's convention), and the hypothesis would force
`θ = 0`, where the identity reads `0 = 0`. -/
theorem integral_hkaDivergence {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {D τ : Ω → ℝ}
    {θ T f : ℝ} (hf : -1 < f) (hτ : HasLaw τ (expMeasure (2 / (1 + f))) μ)
    (hmean : μ[D | m] =ᵐ[μ] fun ω => θ * (T + τ ω)) :
    μ[D] = hkaDivMean θ T f := by
  rw [← integral_condExp hm, integral_congr_ae hmean, integral_mean_hka hf hτ]

/-- **Variance of the divergence** (Hudson, Kreitman & Aguadé 1987): under the hypotheses of
`integral_hkaDivergence`, if moreover `D` is square integrable with conditional variance
`θ (T + τ)` given `m` (as for a Poisson count), then
`Var D = θ (T + (1 + f) / 2) + (θ (1 + f) / 2)²`. -/
theorem variance_hkaDivergence {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {D τ : Ω → ℝ}
    {θ T f : ℝ} (hf : -1 < f) (hτ : HasLaw τ (expMeasure (2 / (1 + f))) μ)
    (hD : MemLp D 2 μ) (hmean : μ[D | m] =ᵐ[μ] fun ω => θ * (T + τ ω))
    (hvar : Var[D; μ | m] =ᵐ[μ] fun ω => θ * (T + τ ω)) :
    Var[D; μ] = hkaDivVar θ T f := by
  have hr : 0 < 2 / (1 + f) := div_pos two_pos (by linarith)
  have hτm : AEMeasurable τ μ := hτ.aemeasurable
  rw [← integral_condVar_add_variance_condExp hm hD, integral_congr_ae hvar,
    variance_congr hmean, integral_mean_hka hf hτ]
  have hvar' : Var[fun ω => θ * (T + τ ω); μ] = θ ^ 2 * ((1 + f) / 2) ^ 2 := by
    have h1 : (fun ω => θ * (T + τ ω)) = fun ω => θ * τ ω + θ * T := by
      funext ω
      ring
    rw [h1, variance_add_const (hτm.const_mul θ).aestronglyMeasurable, variance_const_mul,
      hτ.variance_eq_of_expMeasure hr, inv_div]
  rw [hvar', hkaDivVar]
  ring

/-- The **HKA statistic** for `L` loci with polymorphism counts `SA i`, `SB i`, divergences
`D i`, parameters `θ i`, `T`, `f` and sample sizes `nA`, `nB`: the sum over loci of the
squared standardized deviations of the three counts from their HKA expectations. -/
def hkaStatistic {L : ℕ} (nA nB : ℕ) (θ : Fin L → ℝ) (T f : ℝ) (SA SB D : Fin L → ℝ) : ℝ :=
  ∑ i, ((SA i - hkaPolyMean (θ i) nA) ^ 2 / hkaPolyVar (θ i) nA +
    (SB i - hkaPolyMean (f * θ i) nB) ^ 2 / hkaPolyVar (f * θ i) nB +
    (D i - hkaDivMean (θ i) T f) ^ 2 / hkaDivVar (θ i) T f)

/-- HKA's variances are positive in the biological domain: `θ > 0`, `n ≥ 2`. -/
theorem hkaPolyVar_pos {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (hn : 2 ≤ n) : 0 < hkaPolyVar θ n := by
  have ha1 : 0 < tajimaA1 n := by
    rw [tajimaA1_eq_harmonic]
    exact_mod_cast harmonic_pos (by omega)
  have ha2 : 0 ≤ tajimaA2 n := sum_nonneg fun i _ => by positivity
  unfold hkaPolyVar
  positivity

/-- HKA's divergence variance is positive for `θ > 0`, `T ≥ 0`, `f > -1`. -/
theorem hkaDivVar_pos {θ T f : ℝ} (hθ : 0 < θ) (hT : 0 ≤ T) (hf : -1 < f) :
    0 < hkaDivVar θ T f := by
  have h : 0 < T + (1 + f) / 2 := by linarith
  unfold hkaDivVar hkaDivMean
  positivity

/-- **The HKA statistic has mean `3 L` at the true parameters**: if every count is square
integrable with the HKA mean and variance (as derived above under the neutral model), with
`θ i > 0`, `T ≥ 0`, `f > 0` and `nA, nB ≥ 2`, then `E X² = 3 L`. -/
theorem integral_hkaStatistic {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {L nA nB : ℕ} {θ : Fin L → ℝ} {T f : ℝ}
    (hθ : ∀ i, 0 < θ i) (hT : 0 ≤ T) (hf : 0 < f) (hnA : 2 ≤ nA) (hnB : 2 ≤ nB)
    {SA SB D : Fin L → Ω → ℝ} (hSA : ∀ i, MemLp (SA i) 2 μ) (hSB : ∀ i, MemLp (SB i) 2 μ)
    (hD : ∀ i, MemLp (D i) 2 μ)
    (eSA : ∀ i, μ[SA i] = hkaPolyMean (θ i) nA)
    (eSB : ∀ i, μ[SB i] = hkaPolyMean (f * θ i) nB)
    (eD : ∀ i, μ[D i] = hkaDivMean (θ i) T f)
    (vSA : ∀ i, Var[SA i; μ] = hkaPolyVar (θ i) nA)
    (vSB : ∀ i, Var[SB i; μ] = hkaPolyVar (f * θ i) nB)
    (vD : ∀ i, Var[D i; μ] = hkaDivVar (θ i) T f) :
    μ[fun ω => hkaStatistic nA nB θ T f (fun i => SA i ω) (fun i => SB i ω)
      (fun i => D i ω)] = 3 * (L : ℝ) := by
  have key : ∀ (X : Ω → ℝ) (c v : ℝ), MemLp X 2 μ → μ[X] = c → Var[X; μ] = v → 0 < v →
      Integrable (fun ω => (X ω - c) ^ 2 / v) μ ∧ μ[fun ω => (X ω - c) ^ 2 / v] = 1 := by
    intro X c v hX hc hv hv0
    have hsq : Integrable (fun ω => (X ω - c) ^ 2) μ :=
      (hX.sub (memLp_const c)).integrable_sq
    refine ⟨hsq.div_const v, ?_⟩
    have hvi := variance_eq_integral (μ := μ) hX.aestronglyMeasurable.aemeasurable
    rw [integral_div, ← hc, ← hvi, hv, div_self hv0.ne']
  have hA := fun i => key (SA i) _ _ (hSA i) (eSA i) (vSA i) (hkaPolyVar_pos (hθ i) hnA)
  have hB := fun i => key (SB i) _ _ (hSB i) (eSB i) (vSB i)
    (hkaPolyVar_pos (mul_pos hf (hθ i)) hnB)
  have hDv := fun i => key (D i) _ _ (hD i) (eD i) (vD i) (hkaDivVar_pos (hθ i) hT (by linarith))
  have hint : ∀ i ∈ (univ : Finset (Fin L)), Integrable (fun ω =>
      (SA i ω - hkaPolyMean (θ i) nA) ^ 2 / hkaPolyVar (θ i) nA +
        (SB i ω - hkaPolyMean (f * θ i) nB) ^ 2 / hkaPolyVar (f * θ i) nB +
        (D i ω - hkaDivMean (θ i) T f) ^ 2 / hkaDivVar (θ i) T f) μ :=
    fun i _ => ((hA i).1.add (hB i).1).add (hDv i).1
  simp only [hkaStatistic]
  rw [integral_finsetSum _ hint]
  have h3 : ∀ i ∈ (univ : Finset (Fin L)), μ[fun ω =>
      (SA i ω - hkaPolyMean (θ i) nA) ^ 2 / hkaPolyVar (θ i) nA +
        (SB i ω - hkaPolyMean (f * θ i) nB) ^ 2 / hkaPolyVar (f * θ i) nB +
        (D i ω - hkaDivMean (θ i) T f) ^ 2 / hkaDivVar (θ i) T f] = 3 := by
    intro i _
    have h1 := integral_add ((hA i).1.add (hB i).1) (hDv i).1
    have h2 := integral_add (hA i).1 (hB i).1
    simp only [Pi.add_apply] at h1 h2
    beta_reduce
    rw [h1, h2, (hA i).2, (hB i).2, (hDv i).2]
    norm_num
  rw [sum_congr rfl h3, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **HKA's estimating equations** (Hudson, Kreitman & Aguadé 1987) for parameters
`θ i`, `T`, `f` given the counts: the totals over loci of polymorphism in `A`, in `B` and of
divergence match their expectations, and at each locus the total of the three counts matches
its expectation. (Only `L - 1` of the per-locus equations are independent of the totals.) -/
def hkaEquations {L : ℕ} (nA nB : ℕ) (θ : Fin L → ℝ) (T f : ℝ) (SA SB D : Fin L → ℝ) :
    Prop :=
  (∑ i, SA i = tajimaA1 nA * ∑ i, θ i) ∧ (∑ i, SB i = f * tajimaA1 nB * ∑ i, θ i) ∧
    (∑ i, D i = (T + (1 + f) / 2) * ∑ i, θ i) ∧
    ∀ i, SA i + SB i + D i = θ i * (T + (1 + f) / 2 + tajimaA1 nA + f * tajimaA1 nB)

/-- The true parameters solve HKA's estimating equations at the expected counts. -/
theorem hkaEquations_expected {L : ℕ} (nA nB : ℕ) (θ : Fin L → ℝ) (T f : ℝ) :
    hkaEquations nA nB θ T f (fun i => hkaPolyMean (θ i) nA)
      (fun i => hkaPolyMean (f * θ i) nB) (fun i => hkaDivMean (θ i) T f) := by
  refine ⟨?_, ?_, ?_, fun i => ?_⟩ <;>
    simp only [hkaPolyMean, hkaDivMean, mul_sum] <;>
    first
    | exact sum_congr rfl fun i _ => by ring
    | ring

end MathlibExt.Biology.PopulationGenetics.Coalescent
