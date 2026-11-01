/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Kingman
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The classic skyline plot: maximum-likelihood population sizes from coalescent intervals

In a sample genealogy of `n` genes, let `w_k` be the length of the coalescent interval during
which there are `k` lineages (`2 ≤ k ≤ n`). In the classic skyline plot (Pybus, Rambaut &
Harvey 2000) the population-size parameter `θ_k` is constant on each interval, and in the time
units of the genealogy each pair of lineages coalesces at rate `1 / θ_k`, so the intervals are
independent with `w_k ~ Exp(C(k, 2) / θ_k)` (`SkylineTimes`). The log-likelihood of `θ` is the
sum over intervals of `ℓ_k(θ_k) = log (C(k, 2) / θ_k) - C(k, 2) w_k / θ_k`, the log-density of
`Exp(C(k, 2) / θ_k)` at `w_k`, and

* for `w_k > 0` it has the unique maximizer `θ̂_k = C(k, 2) w_k` (the skyline estimate);
* the estimates are independent across intervals, unbiased (`E θ̂_k = θ_k`) and have variance
  `θ_k²`.

For a constant population (`θ_k = 1` in units of `2N` generations) `SkylineTimes` is
`KingmanTimes`. The domain is `θ_k > 0` (a structure field) and `w_k > 0`.

## Main results

* `skylineLogLik_le`, `skylineLogLik_eq_iff`: `θ = C(k, 2) w` is the unique maximizer of one
  interval's log-likelihood.
* `sum_skylineLogLik_le`, `sum_skylineLogLik_eq_iff`: the skyline estimates are the unique
  joint maximizer.
* `SkylineTimes.integral_skylineEstimate`, `SkylineTimes.variance_skylineEstimate`,
  `SkylineTimes.iIndepFun_skylineEstimate`: unbiasedness, variance `θ_k²`, independence.
* `SkylineTimes.ofPi`: a concrete model (non-vacuity).

## References

* O. G. Pybus, A. Rambaut and P. H. Harvey, *An integrated framework for the inference of viral
  population history from reconstructed genealogies*, Genetics 155 (2000), 1429–1437.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The coalescent intervals of a sample of `n` genes under the classic skyline model with
piecewise-constant population-size parameter `θ k` while there are `k` lineages: `T k` is
exponential with rate `C(k, 2) / θ k`, independently over `2 ≤ k ≤ n`. -/
structure SkylineTimes (μ : Measure Ω) (n : ℕ) (θ : ℕ → ℝ) where
  /-- `T k` is the length of the interval with `k` lineages. -/
  T : ℕ → Ω → ℝ
  /-- The population-size parameters are positive. -/
  θ_pos : ∀ k ∈ Icc 2 n, 0 < θ k
  /-- `T k` is exponential with rate `C(k, 2) / θ k`. -/
  hasLaw : ∀ k ∈ Icc 2 n, HasLaw (T k) (expMeasure (((k.choose 2 : ℕ) : ℝ) / θ k)) μ
  /-- The interval lengths are mutually independent. -/
  indep : iIndepFun (fun k : Icc 2 n => T k) μ

/-- The log-likelihood of `θ` for one coalescent interval of length `w` with `c = C(k, 2)`
pairs of lineages: the log-density `log (c / θ) - c w / θ` of `Exp(c / θ)` at `w`. -/
def skylineLogLik (c w θ : ℝ) : ℝ := Real.log (c / θ) - c * w / θ

/-- The likelihood gap `ℓ(θ) - ℓ(c w) = log u - u + 1` with `u = c w / θ`. -/
private theorem skylineLogLik_sub {c w θ : ℝ} (hc : 0 < c) (hw : 0 < w) (hθ : 0 < θ) :
    skylineLogLik c w θ - skylineLogLik c w (c * w) =
      Real.log (c * w / θ) - c * w / θ + 1 := by
  have hcw : 0 < c * w := mul_pos hc hw
  unfold skylineLogLik
  rw [Real.log_div hc.ne' hθ.ne', Real.log_div hc.ne' hcw.ne', Real.log_mul hc.ne' hw.ne',
    Real.log_div hcw.ne' hθ.ne', Real.log_mul hc.ne' hw.ne', div_self hcw.ne']
  ring

/-- **The skyline estimate maximizes the interval likelihood** (Pybus, Rambaut & Harvey 2000):
for `c, w, θ > 0`, `ℓ(θ) ≤ ℓ(c w)`. -/
theorem skylineLogLik_le {c w θ : ℝ} (hc : 0 < c) (hw : 0 < w) (hθ : 0 < θ) :
    skylineLogLik c w θ ≤ skylineLogLik c w (c * w) := by
  have h := skylineLogLik_sub hc hw hθ
  have hu := Real.log_le_sub_one_of_pos (div_pos (mul_pos hc hw) hθ)
  linarith

/-- **Uniqueness of the skyline maximizer**: for `c, w, θ > 0`, `ℓ(θ) = ℓ(c w)` iff
`θ = c w`. -/
theorem skylineLogLik_eq_iff {c w θ : ℝ} (hc : 0 < c) (hw : 0 < w) (hθ : 0 < θ) :
    skylineLogLik c w θ = skylineLogLik c w (c * w) ↔ θ = c * w := by
  have h := skylineLogLik_sub hc hw hθ
  constructor
  · intro heq
    by_contra hne
    have hu1 : c * w / θ ≠ 1 := by
      intro h1
      exact hne ((div_eq_one_iff_eq hθ.ne').mp h1).symm
    have hu := Real.log_lt_sub_one_of_pos (div_pos (mul_pos hc hw) hθ) hu1
    linarith
  · rintro rfl
    rfl

/-- **The skyline estimates jointly maximize the likelihood**: for positive `c i`, `w i`,
`θ i` over a finite set of intervals, `∑ ℓ_i(θ_i) ≤ ∑ ℓ_i(c_i w_i)`. -/
theorem sum_skylineLogLik_le {ι : Type*} (s : Finset ι) {c w θ : ι → ℝ}
    (hc : ∀ i ∈ s, 0 < c i) (hw : ∀ i ∈ s, 0 < w i) (hθ : ∀ i ∈ s, 0 < θ i) :
    ∑ i ∈ s, skylineLogLik (c i) (w i) (θ i) ≤ ∑ i ∈ s, skylineLogLik (c i) (w i) (c i * w i) :=
  sum_le_sum fun i hi => skylineLogLik_le (hc i hi) (hw i hi) (hθ i hi)

/-- **Uniqueness of the joint maximizer**: equality in `sum_skylineLogLik_le` holds iff
`θ i = c i w i` for every interval. -/
theorem sum_skylineLogLik_eq_iff {ι : Type*} (s : Finset ι) {c w θ : ι → ℝ}
    (hc : ∀ i ∈ s, 0 < c i) (hw : ∀ i ∈ s, 0 < w i) (hθ : ∀ i ∈ s, 0 < θ i) :
    ∑ i ∈ s, skylineLogLik (c i) (w i) (θ i) =
        ∑ i ∈ s, skylineLogLik (c i) (w i) (c i * w i) ↔ ∀ i ∈ s, θ i = c i * w i := by
  rw [sum_eq_sum_iff_of_le fun i hi => skylineLogLik_le (hc i hi) (hw i hi) (hθ i hi)]
  exact forall₂_congr fun i hi => skylineLogLik_eq_iff (hc i hi) (hw i hi) (hθ i hi)

/-- The classic skyline estimate `θ̂_k = C(k, 2) w_k` for the interval with `k` lineages. -/
def skylineEstimate (k : ℕ) (w : ℝ) : ℝ := ((k.choose 2 : ℕ) : ℝ) * w

namespace SkylineTimes

variable {μ : Measure Ω} {n : ℕ} {θ : ℕ → ℝ} (S : SkylineTimes μ n θ)

/-- The rate `C(k, 2) / θ k` of the interval with `k` lineages is positive. -/
private theorem rate_pos (S : SkylineTimes μ n θ) {k : ℕ} (hk : k ∈ Icc 2 n) :
    0 < ((k.choose 2 : ℕ) : ℝ) / θ k :=
  div_pos (KingmanTimes.choose_two_pos hk) (S.θ_pos k hk)

/-- **The skyline estimate is unbiased**: `E[C(k, 2) T k] = θ k`. -/
theorem integral_skylineEstimate {k : ℕ} (hk : k ∈ Icc 2 n) :
    μ[fun ω => skylineEstimate k (S.T k ω)] = θ k := by
  have hc := (KingmanTimes.choose_two_pos hk).ne'
  simp only [skylineEstimate]
  rw [integral_const_mul, (S.hasLaw k hk).integral_eq_inv_of_expMeasure (S.rate_pos hk)]
  field_simp

/-- **Variance of the skyline estimate**: `Var[C(k, 2) T k] = θ k²`. -/
theorem variance_skylineEstimate {k : ℕ} (hk : k ∈ Icc 2 n) :
    Var[fun ω => skylineEstimate k (S.T k ω); μ] = θ k ^ 2 := by
  have hc := (KingmanTimes.choose_two_pos hk).ne'
  simp only [skylineEstimate]
  rw [variance_const_mul, (S.hasLaw k hk).variance_eq_of_expMeasure (S.rate_pos hk)]
  field_simp

/-- **The skyline estimates are independent** across intervals. -/
theorem iIndepFun_skylineEstimate :
    iIndepFun (fun k : Icc 2 n => fun ω => skylineEstimate k (S.T k ω)) μ :=
  S.indep.comp (fun k x => skylineEstimate k x) fun _ => measurable_const.mul measurable_id

end SkylineTimes

/-- The canonical probability space for the skyline model: the product of the exponential laws
`Exp(C(k, 2) / θ k)`, `2 ≤ k ≤ n`. -/
def skylinePiMeasure (n : ℕ) (θ : ℕ → ℝ) (hθ : ∀ k ∈ Icc 2 n, 0 < θ k) :
    Measure (Icc 2 n → ℝ) :=
  haveI : ∀ k : Icc 2 n, IsProbabilityMeasure (expMeasure (((k : ℕ).choose 2 : ℕ) / θ k)) :=
    fun k => isProbabilityMeasure_expMeasure
      (div_pos (KingmanTimes.choose_two_pos k.2) (hθ k k.2))
  Measure.pi fun k : Icc 2 n => expMeasure (((k : ℕ).choose 2 : ℕ) / θ k)

/-- The coordinate projections of `skylinePiMeasure n θ` form a skyline model whenever the
`θ k` are positive; in particular `SkylineTimes` is inhabited. -/
def SkylineTimes.ofPi (n : ℕ) {θ : ℕ → ℝ} (hθ : ∀ k ∈ Icc 2 n, 0 < θ k) :
    SkylineTimes (skylinePiMeasure n θ hθ) n θ :=
  haveI : ∀ k : Icc 2 n, IsProbabilityMeasure (expMeasure (((k : ℕ).choose 2 : ℕ) / θ k)) :=
    fun k => isProbabilityMeasure_expMeasure
      (div_pos (KingmanTimes.choose_two_pos k.2) (hθ k k.2))
  { T := fun k ω => if h : k ∈ Icc 2 n then ω ⟨k, h⟩ else 0
    θ_pos := hθ
    hasLaw := fun k hk => by
      have hT : (fun ω : Icc 2 n → ℝ => if h : k ∈ Icc 2 n then ω ⟨k, h⟩ else 0)
          = fun ω => ω ⟨k, hk⟩ := by
        funext ω
        simp [hk]
      rw [hT]
      exact (measurePreserving_eval
        (fun i : Icc 2 n => expMeasure ((((i : ℕ).choose 2 : ℕ) : ℝ) / θ i)) ⟨k, hk⟩).hasLaw
    indep := by
      have hT : (fun k : Icc 2 n => fun ω : Icc 2 n → ℝ =>
          if h : (k : ℕ) ∈ Icc 2 n then ω ⟨k, h⟩ else 0) = fun k ω => id (ω k) := by
        funext k ω
        simp [k.2]
      rw [hT]
      exact iIndepFun_pi
        (μ := fun i : Icc 2 n => expMeasure ((((i : ℕ).choose 2 : ℕ) : ℝ) / θ i))
        (fun _ => aemeasurable_id) }

end MathlibExt.Biology.PopulationGenetics.Coalescent
