/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.GeneralDiffusion
public import MathlibExt.Biology.PopulationGenetics.Diffusion.Sojourn
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The Maruyama effect: alleles under selection are younger than neutral alleles

Kiezun et al. (2013) compare the age of deleterious and neutral alleles at the same population
frequency. Their Methods section follows Maruyama (1974) and Maruyama and Kimura (1975): for
the Wright–Fisher diffusion with genic selection, the mean time an allele now at frequency `x`
has spent at frequency `z` since its origin has an explicit density, symmetric in the
selection coefficient, and its integral (the mean age) is largest for neutral alleles.

Conventions (`MathlibExt/Biology/README.md`): time in units of `2N` generations, scaled
selection coefficient `σ = 2Ns` (the paper's `4Ns` is `2σ`), backward generator
`L_σ u = x (1 - x) / 2 · u'' + σ x (1 - x) · u'` (`generator`). The paper works in generations;
its densities are `2N` times the ones here (`maruyamaBelow_generations`,
`maruyamaAbove_generations`). As in `Sojourn`, only the analytic statements are formalized; the
diffusion process itself is not.

* `selectionGreen σ p x` is the Green's function `Ψ(p, x)` of `L_σ v = -g`, `v(0) = v(1) = 0`,
  written with Kimura's fixation probability `u = kimuraFixation σ`. It reduces to
  `neutralGreen` at `σ = 0`.
* `ageDensity σ p x z = Ψ(p, z) Ψ(z, x) / Ψ(p, x)` is the paper's conditional sojourn density
  `Ψ_z`. For `p ≤ z ≤ x` it equals the paper's closed form `Ψ₁ = maruyamaBelow σ z`, and for
  `p ≤ x ≤ z` the closed form `Ψ₂ = maruyamaAbove σ x z`; neither depends on `p`.
* `meanAge σ x = ∫₀^x Ψ₁ + ∫_x^1 Ψ₂` is the paper's mean age `a(x)`.

## Main results

* `generator_integral_selectionGreen`, `integral_selectionGreen_left`,
  `integral_selectionGreen_right`: for continuous `g`, `v(p) = ∫₀¹ Ψ(p, x) g(x) dx` solves
  `L_σ v = -g` on `(0, 1)` with `v(0) = v(1) = 0` (the paper's `δ`-equation in integrated form).
* `greenFunction_eq_selectionGreen`: the general Green kernel `greenFunction` of
  `GeneralDiffusion` at `b x = σ x (1 - x)`, `a x = x (1 - x)` is `selectionGreen σ`, so the
  general API (e.g. `diffusionGenerator_integral_greenFunction`) applies to it and there are
  no parallel Green-kernel representations.
* `generator_selectionGreen_of_lt`, `generator_selectionGreen_of_gt`,
  `continuous_selectionGreen_left`, `hasDerivWithinAt_selectionGreen_Iic`,
  `hasDerivWithinAt_selectionGreen_Ici`: `Ψ(·, x)` solves the homogeneous equation off the
  diagonal, is continuous, and its derivative jumps by `-2 / (x (1 - x))` at `p = x`.
* `ageDensity_of_le_of_le`, `ageDensity_of_le_of_ge`: the paper's closed forms.
* `maruyamaBelow_generations`, `maruyamaAbove_generations`: the paper's formulas verbatim, in
  generations.
* `meanAge_zero`: Kimura and Ohta's neutral mean age `-2 x log x / (1 - x)`.
* `maruyamaBelow_neg`, `maruyamaAbove_neg`, `meanAge_neg`: symmetry under `σ ↦ -σ`.
* `maruyamaBelow_lt`, `maruyamaAbove_lt`, `meanAge_lt`: **the Maruyama effect**. For `σ ≠ 0`
  both densities are strictly below their neutral values, so alleles under selection
  (advantageous or deleterious) are on average strictly younger than neutral alleles at the
  same frequency.
* `maruyamaBelow_lt_of_lt`, `maruyamaAbove_lt_of_lt`, `meanAge_lt_meanAge_of_lt`,
  `meanAge_lt_meanAge_of_abs_lt`: the stronger the selection, the younger the allele (shown
  numerically in Kiezun et al. 2013, Figure 1b).
* `lintegral_mul_eq_lintegral_sojourn_mul`: for any Chapman–Kolmogorov family of transition
  densities, `∫₀^∞ t w(p, x, t) dt = ∫₀¹ Ψ(p, y) Ψ(y, x) dy` (Tonelli), the identity that
  makes `ageDensity` a density of mean time.
* `tendsto_integral_ageDensity`: the mean age is the limit, as the initial frequency `p → 0⁺`,
  of the total conditional sojourn time `∫₀¹ ageDensity σ p x z dz`.

The comparisons with the neutral case use the hyperbolic forms (`maruyamaBelow_eq_sinh`,
`maruyamaAbove_eq_sinh`) and the inequality `(a + b) sinh a sinh b < a b sinh (a + b)` for
`a, b > 0`, which follows from `sinh t < t cosh t`. The monotonicity in `σ` uses that
`φ(t) = coth t - 1 / t`, the derivative of `log (sinh t / t)`, is positive and increasing on
`(0, ∞)`.

## References

* A. Kiezun, S. L. Pulit, L. C. Francioli, et al., *Deleterious alleles in the human genome are
  on average younger than neutral alleles of the same frequency*, PLoS Genet. 9 (2013)
  e1003301, Methods.
* T. Maruyama, *The age of a rare mutant gene in a large population*, Am. J. Hum. Genet. 26
  (1974) 669–673.
* T. Maruyama and M. Kimura, *Moments for sum of an arbitrary function of gene frequency along
  a stochastic path of gene frequency change*, Proc. Natl. Acad. Sci. USA 72 (1975) 1602–1604.
* M. Kimura and T. Ohta, *The age of a neutral mutant persisting in a finite population*,
  Genetics 75 (1973) 199–212.
* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), Chapter 4.
-/

@[expose] public section

open Real Set MeasureTheory Filter
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- The slope constant of Kimura's formula is positive. -/
theorem kimuraSlope_pos (σ : ℝ) : 0 < kimuraSlope σ := by
  unfold kimuraSlope
  split_ifs with h
  · exact one_pos
  rcases lt_or_gt_of_ne h with hσ | hσ
  · have : 1 < exp (-2 * σ) := one_lt_exp_iff.2 (by linarith)
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · have : exp (-2 * σ) < 1 := exp_lt_one_iff.2 (by linarith)
    exact div_pos (by linarith) (by linarith)

/-- Kimura's fixation probability is strictly increasing in the initial frequency. -/
theorem strictMono_kimuraFixation (σ : ℝ) : StrictMono (kimuraFixation σ) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_kimuraFixation σ) fun _ =>
    mul_pos (kimuraSlope_pos σ) (exp_pos _)

/-- An allele present at positive frequency has positive fixation probability. -/
theorem kimuraFixation_pos (σ : ℝ) {x : ℝ} (hx : 0 < x) : 0 < kimuraFixation σ x := by
  simpa using strictMono_kimuraFixation σ hx

/-- An allele at frequency below `1` is lost with positive probability. -/
theorem kimuraFixation_lt_one (σ : ℝ) {x : ℝ} (hx : x < 1) : kimuraFixation σ x < 1 := by
  simpa using strictMono_kimuraFixation σ hx

/-- The sojourn density (Green's function) of the Wright–Fisher diffusion with genic selection,
time in units of `2N` generations, `σ = 2Ns`. With `u = kimuraFixation σ` and
`u'(x) = kimuraSlope σ · e^{-2σx}`,

  `Ψ(p, x) = 2 u(min p x) (1 - u(max p x)) / (x (1 - x) u'(x))`,

which is `2 S(min p x) (S(1) - S(max p x)) / (S(1) x (1 - x) e^{-2σx})` in terms of the scale
function `S(y) = (1 - e^{-2σy}) / (2σ)` (`S(y) = y` if `σ = 0`). The neutral case is handled by
the neutral branches of `kimuraFixation` and `kimuraSlope` (`selectionGreen_zero`). It is
meaningful for `0 < x < 1`; at `x = 0, 1` the denominator vanishes and Lean's `/ 0` gives `0`
(a null set for integrals in `x`). In the diffusion reading (not formalized here), `Ψ(p, x) dx`
is the expected time an allele started at frequency `p` spends in `(x, x + dx)` before loss or
fixation (Ewens 2004, Chapter 4; the paper's `Ψ(p, x)` divided by `2N`). -/
noncomputable def selectionGreen (σ p x : ℝ) : ℝ :=
  2 * kimuraFixation σ (min p x) * (1 - kimuraFixation σ (max p x)) /
    (x * (1 - x) * (kimuraSlope σ * exp (-2 * σ * x)))

/-- For `σ = 0` and `0 < x < 1` the sojourn density is the neutral Green's function. -/
theorem selectionGreen_zero {p x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    selectionGreen 0 p x = neutralGreen p x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  simp only [selectionGreen, kimuraFixation_neutral, kimuraSlope, ↓reduceIte, mul_zero,
    zero_mul, exp_zero, mul_one, neutralGreen]
  split_ifs with h
  · rw [min_eq_right h, max_eq_left h]
    field_simp
  · rw [min_eq_left (not_le.1 h).le, max_eq_right (not_le.1 h).le]
    field_simp

/-- **The general Green kernel specializes to Kimura's sojourn density.** For genic selection
`b x = σ x (1 - x)`, `a x = x (1 - x)`, the general Green's function `greenFunction` is
`selectionGreen σ` on `[0, 1] × (0, 1)`. The scale function is `S(y) = u(y) / u'(0)` with
`u = kimuraFixation σ` and `u'(0) = kimuraSlope σ`, since both have derivative `ψ(y) = e^{-2σy}`
and vanish at `0`; substituting that and `S(1) = 1 / u'(0)` into `greenFunction` gives
`selectionGreen`. -/
theorem greenFunction_eq_selectionGreen (σ : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    greenFunction (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) p x =
      selectionGreen σ p x := by
  have hS_eq : ∀ y ∈ Icc (0 : ℝ) 1,
      scaleFunction (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) y =
        kimuraFixation σ y / kimuraSlope σ := by
    intro y hy
    have hψ : (∫ t in (0 : ℝ)..y,
        scaleDensity (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) t) =
        ∫ t in (0 : ℝ)..y, exp (-2 * σ * t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hy.1] at ht
      exact scaleDensity_wrightFisher σ ⟨ht.1, le_trans ht.2 hy.2⟩
    have hFTC : (∫ t in (0 : ℝ)..y, exp (-2 * σ * t)) =
        kimuraFixation σ y / kimuraSlope σ - kimuraFixation σ 0 / kimuraSlope σ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ)) (b := y)
        (f := fun z => kimuraFixation σ z / kimuraSlope σ)
        (f' := fun t => exp (-2 * σ * t)) hy.1
        ((continuous_kimuraFixation σ).continuousOn.div_const _)
        (fun z hz => by
          have h := (hasDerivAt_kimuraFixation σ z).div_const (kimuraSlope σ)
          rwa [mul_div_cancel_left₀ _ (kimuraSlope_pos σ).ne'] at h)
        ((by fun_prop : Continuous fun t : ℝ => exp (-2 * σ * t)).intervalIntegrable 0 y)
    calc scaleFunction (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) y
        = ∫ t in (0 : ℝ)..y,
            scaleDensity (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) t := rfl
      _ = ∫ t in (0 : ℝ)..y, exp (-2 * σ * t) := hψ
      _ = kimuraFixation σ y / kimuraSlope σ := by
          rw [hFTC, kimuraFixation_zero_right, zero_div, sub_zero]
  have hS1 : scaleFunction (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) 1 =
      1 / kimuraSlope σ := by
    rw [hS_eq 1 ⟨zero_le_one, le_rfl⟩, kimuraFixation_one_right, one_div]
  have hψx : scaleDensity (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) x =
      exp (-2 * σ * x) :=
    scaleDensity_wrightFisher σ ⟨hx.1.le, hx.2.le⟩
  have hmin : min p x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min hp.1 hx.1.le, le_trans (min_le_left _ _) hp.2⟩
  have hmax : max p x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_of_le_left hp.1, max_le hp.2 hx.2.le⟩
  have hslope : kimuraSlope σ ≠ 0 := (kimuraSlope_pos σ).ne'
  have hA : x * (1 - x) ≠ 0 := mul_ne_zero hx.1.ne' (sub_pos.2 hx.2).ne'
  have hexp : exp (-2 * σ * x) ≠ 0 := Real.exp_ne_zero _
  simp only [greenFunction, selectionGreen, hS_eq _ hmin, hS_eq _ hmax, hS1, hψx]
  field_simp
  ring

/-- `d/dx e^{c x} = c e^{c x}`. -/
private theorem hasDerivAt_exp_mul' (c x : ℝ) :
    HasDerivAt (fun y => exp (c * y)) (exp (c * x) * c) x := by
  simpa only [mul_one] using ((hasDerivAt_id' x).const_mul c).exp

/-- The difference quotients of Kimura's fixation probability at a point are continuous. -/
private theorem continuous_dslope_kimuraFixation (σ a : ℝ) :
    Continuous (dslope (kimuraFixation σ) a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = a
  · subst x
    exact continuousAt_dslope_same.mpr (hasDerivAt_kimuraFixation σ a).differentiableAt
  · exact (continuousAt_dslope_of_ne hx).mpr (continuous_kimuraFixation σ).continuousAt

/-- The integrand left of the starting point, `u(x) g(x) / (x (1 - x) u'(x))`, written with
`dslope` so that it is continuous on `(-∞, 1)`. -/
private noncomputable def greenLeft (σ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  dslope (kimuraFixation σ) 0 x * g x /
    ((1 - x) * (kimuraSlope σ * exp (-2 * σ * x)))

/-- The integrand right of the starting point, `(1 - u(x)) g(x) / (x (1 - x) u'(x))`, written
with `dslope` so that it is continuous on `(0, ∞)`. -/
private noncomputable def greenRight (σ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  dslope (kimuraFixation σ) 1 x * g x /
    (x * (kimuraSlope σ * exp (-2 * σ * x)))

/-- Continuity of the left integrand. -/
private theorem continuousOn_greenLeft (σ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (greenLeft σ g) (Iio 1) := by
  apply ((continuous_dslope_kimuraFixation σ 0).mul hg).continuousOn.div
    ((continuousOn_const.sub continuousOn_id).mul
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).continuousOn)
  intro x hx
  exact mul_ne_zero (sub_pos.mpr hx).ne'
    (mul_ne_zero (kimuraSlope_ne_zero σ) (exp_ne_zero _))

/-- Continuity of the right integrand. -/
private theorem continuousOn_greenRight (σ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (greenRight σ g) (Ioi 0) := by
  apply ((continuous_dslope_kimuraFixation σ 1).mul hg).continuousOn.div
    (continuousOn_id.mul
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).continuousOn)
  intro x hx
  exact mul_ne_zero (ne_of_gt hx)
    (mul_ne_zero (kimuraSlope_ne_zero σ) (exp_ne_zero _))

/-- Integrability of the left integrand. -/
private theorem intervalIntegrable_greenLeft (σ : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (greenLeft σ g) volume 0 q :=
  ContinuousOn.intervalIntegrable_of_Icc hq.1.le
    ((continuousOn_greenLeft σ hg).mono fun _ hx => hx.2.trans_lt hq.2)

/-- Integrability of the right integrand. -/
private theorem intervalIntegrable_greenRight (σ : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (greenRight σ g) volume q 1 :=
  ContinuousOn.intervalIntegrable_of_Icc hq.2.le
    ((continuousOn_greenRight σ hg).mono fun _ hx => hq.1.trans_le hx.1)

/-- The left integrand away from `0`. -/
private theorem greenLeft_eq (σ : ℝ) (g : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) :
    greenLeft σ g x = kimuraFixation σ x * g x /
      (x * (1 - x) * (kimuraSlope σ * exp (-2 * σ * x))) := by
  simp only [greenLeft, dslope_of_ne _ hx, slope_def_field,
    kimuraFixation_zero_right, sub_zero]
  field_simp

/-- The right integrand away from `1`. -/
private theorem greenRight_eq (σ : ℝ) (g : ℝ → ℝ) {x : ℝ} (hx : x ≠ 1) :
    greenRight σ g x = (1 - kimuraFixation σ x) * g x /
      (x * (1 - x) * (kimuraSlope σ * exp (-2 * σ * x))) := by
  simp only [greenRight, dslope_of_ne _ hx, slope_def_field, kimuraFixation_one_right]
  rw [show x - 1 = -(1 - x) by ring, show kimuraFixation σ x - 1 =
    -(1 - kimuraFixation σ x) by ring]
  field_simp

/-- Splitting the Green integral at the starting point `q ∈ (0, 1)`. -/
private theorem integral_selectionGreen_split (σ : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, selectionGreen σ q x * g x) =
      2 * (1 - kimuraFixation σ q) * (∫ x in (0 : ℝ)..q, greenLeft σ g x) +
      2 * kimuraFixation σ q * (∫ x in q..1, greenRight σ g x) := by
  have hl : EqOn (fun x => selectionGreen σ q x * g x)
      (fun x => 2 * (1 - kimuraFixation σ q) * greenLeft σ g x) (Ioo 0 q) := by
    intro x hx
    dsimp only
    rw [selectionGreen, min_eq_right hx.2.le, max_eq_left hx.2.le,
      greenLeft_eq σ g (ne_of_gt hx.1)]
    ring
  have hr : EqOn (fun x => selectionGreen σ q x * g x)
      (fun x => 2 * kimuraFixation σ q * greenRight σ g x) (Ioo q 1) := by
    intro x hx
    dsimp only
    rw [selectionGreen, min_eq_left hx.1.le, max_eq_right hx.1.le,
      greenRight_eq σ g (ne_of_lt hx.2)]
    ring
  have hil := (intervalIntegrable_greenLeft σ hg hq).const_mul
    (2 * (1 - kimuraFixation σ q))
  have hir := (intervalIntegrable_greenRight σ hg hq).const_mul (2 * kimuraFixation σ q)
  have hfl := hil.congr_uIoo (by simpa only [uIoo_of_le hq.1.le] using hl.symm)
  have hfr := hir.congr_uIoo (by simpa only [uIoo_of_le hq.2.le] using hr.symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals hfl hfr,
    intervalIntegral.integral_congr_Ioo_of_le hq.1.le hl,
    intervalIntegral.integral_congr_Ioo_of_le hq.2.le hr,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- FTC for the left piece. -/
private theorem hasDerivAt_integral_greenLeft (σ : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => ∫ x in (0 : ℝ)..t, greenLeft σ g x) (greenLeft σ g q) q := by
  have hc := continuousOn_greenLeft σ hg
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_greenLeft σ hg hq)
    (hc.stronglyMeasurableAtFilter isOpen_Iio q hq.2)
    (hc.continuousAt (Iio_mem_nhds hq.2))

/-- FTC for the right piece. -/
private theorem hasDerivAt_integral_greenRight (σ : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => ∫ x in t..1, greenRight σ g x) (-greenRight σ g q) q := by
  have hc := continuousOn_greenRight σ hg
  exact intervalIntegral.integral_hasDerivAt_left
    (intervalIntegrable_greenRight σ hg hq)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi q hq.1)
    (hc.continuousAt (Ioi_mem_nhds hq.1))

/-- The first derivative of the Green integral: the boundary terms cancel. -/
private theorem hasDerivAt_integral_selectionGreen (σ : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => ∫ x in (0 : ℝ)..1, selectionGreen σ t x * g x)
      (-2 * (kimuraSlope σ * exp (-2 * σ * q)) *
        (∫ x in (0 : ℝ)..q, greenLeft σ g x) +
      2 * (kimuraSlope σ * exp (-2 * σ * q)) *
        (∫ x in q..1, greenRight σ g x)) q := by
  have hu := hasDerivAt_kimuraFixation σ q
  have ha := hasDerivAt_integral_greenLeft σ hg hq
  have hb := hasDerivAt_integral_greenRight σ hg hq
  have hd : HasDerivAt
      (fun t => 2 * (1 - kimuraFixation σ t) *
        (∫ x in (0 : ℝ)..t, greenLeft σ g x) +
      2 * kimuraFixation σ t * (∫ x in t..1, greenRight σ g x))
      (-2 * (kimuraSlope σ * exp (-2 * σ * q)) *
        (∫ x in (0 : ℝ)..q, greenLeft σ g x) +
      2 * (kimuraSlope σ * exp (-2 * σ * q)) *
        (∫ x in q..1, greenRight σ g x)) q := by
    convert (((hu.const_sub 1).const_mul 2).mul ha).add ((hu.const_mul 2).mul hb) using 1
    rw [greenLeft_eq σ g (ne_of_gt hq.1), greenRight_eq σ g (ne_of_lt hq.2)]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with t ht
  exact integral_selectionGreen_split σ hg ht

/-- **Green's representation with selection** (Ewens 2004, Chapter 4; the integrated form of the
paper's `-δ(x - p) = s p (1 - p) ∂Ψ/∂p + p (1 - p) / (4N) ∂²Ψ/∂p²`). For continuous `g` and
`p ∈ (0, 1)`, `v(q) = ∫₀¹ Ψ(q, x) g(x) dx` solves `L_σ v = -g` at `p`; with
`integral_selectionGreen_left` and `integral_selectionGreen_right` (`v(0) = v(1) = 0`) this
generalizes `generator_integral_neutralGreen` to `σ ≠ 0`. In the diffusion reading (not
formalized here), `v(p)` is the expected value of `∫₀^T g(X_t) dt` up to absorption. -/
theorem generator_integral_selectionGreen (σ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    generator σ (fun q => ∫ x in (0 : ℝ)..1, selectionGreen σ q x * g x) p = -g p := by
  have hd : HasDerivAt (fun t => kimuraSlope σ * exp (-2 * σ * t))
      (-2 * σ * (kimuraSlope σ * exp (-2 * σ * p))) p := by
    convert (hasDerivAt_exp_mul' (-2 * σ) p).const_mul (kimuraSlope σ) using 1
    ring
  have ha := hasDerivAt_integral_greenLeft σ hg hp
  have hb := hasDerivAt_integral_greenRight σ hg hp
  have hw : HasDerivAt
      (fun t => -2 * (kimuraSlope σ * exp (-2 * σ * t)) *
        (∫ x in (0 : ℝ)..t, greenLeft σ g x) +
      2 * (kimuraSlope σ * exp (-2 * σ * t)) *
        (∫ x in t..1, greenRight σ g x))
      (4 * σ * (kimuraSlope σ * exp (-2 * σ * p)) *
        (∫ x in (0 : ℝ)..p, greenLeft σ g x) -
      4 * σ * (kimuraSlope σ * exp (-2 * σ * p)) *
        (∫ x in p..1, greenRight σ g x) -
      2 * (kimuraSlope σ * exp (-2 * σ * p)) *
        (greenLeft σ g p + greenRight σ g p)) p := by
    convert ((hd.const_mul (-2)).mul ha).add ((hd.const_mul 2).mul hb) using 1
    ring
  have he : deriv (fun q => ∫ x in (0 : ℝ)..1, selectionGreen σ q x * g x) =ᶠ[𝓝 p]
      (fun t => -2 * (kimuraSlope σ * exp (-2 * σ * t)) *
        (∫ x in (0 : ℝ)..t, greenLeft σ g x) +
      2 * (kimuraSlope σ * exp (-2 * σ * t)) *
        (∫ x in t..1, greenRight σ g x)) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with t ht
    exact (hasDerivAt_integral_selectionGreen σ hg ht).deriv
  rw [generator, he.deriv_eq, hw.deriv,
    (hasDerivAt_integral_selectionGreen σ hg hp).deriv,
    greenLeft_eq σ g (ne_of_gt hp.1), greenRight_eq σ g (ne_of_lt hp.2)]
  field_simp [ne_of_gt hp.1, (sub_pos.mpr hp.2).ne',
    kimuraSlope_ne_zero σ, exp_ne_zero]
  ring

/-- Boundary value at `0`: an absent allele spends no time in `(0, 1)`, so
`∫₀¹ Ψ(0, x) g(x) dx = 0` for every `g`. -/
theorem integral_selectionGreen_left (σ : ℝ) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, selectionGreen σ 0 x * g x = 0 := by
  refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
    (MeasureTheory.ae_of_all _ fun x hx => ?_)).trans (by simp)
  rw [uIoc_of_le zero_le_one] at hx
  simp [selectionGreen, min_eq_left hx.1.le]

/-- Boundary value at `1`: a fixed allele spends no time in `(0, 1)`, so
`∫₀¹ Ψ(1, x) g(x) dx = 0` for every `g`. -/
theorem integral_selectionGreen_right (σ : ℝ) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, selectionGreen σ 1 x * g x = 0 := by
  refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
    (MeasureTheory.ae_of_all _ fun x hx => ?_)).trans (by simp)
  rw [uIoc_of_le zero_le_one] at hx
  simp [selectionGreen, max_eq_left hx.2]

private theorem generator_congr {σ : ℝ} {f g : ℝ → ℝ} {p : ℝ} (h : f =ᶠ[𝓝 p] g) :
    generator σ f p = generator σ g p := by
  unfold generator
  rw [h.deriv.deriv_eq, h.deriv_eq]

private theorem generator_affine_kimuraFixation (σ a b p : ℝ) :
    generator σ (fun q => a + b * kimuraFixation σ q) p = 0 := by
  have hd : deriv (fun q => a + b * kimuraFixation σ q) =
      fun y => b * (kimuraSlope σ * exp (-2 * σ * y)) :=
    funext fun y => (((hasDerivAt_kimuraFixation σ y).const_mul b).const_add a).deriv
  have h2 : HasDerivAt (fun y => b * (kimuraSlope σ * exp (-2 * σ * y)))
      (b * (kimuraSlope σ * (exp (-2 * σ * p) * (-2 * σ)))) p := by
    have := ((hasDerivAt_id' p).const_mul (-2 * σ)).exp
    simp only [mul_one] at this
    exact (this.const_mul _).const_mul _
  rw [generator, hd, h2.deriv]
  ring

/-- Below the target frequency the sojourn density solves the homogeneous backward equation in
its first argument: `L_σ Ψ(·, x) = 0` at every `p < x` (pointwise form of the paper's
`-δ(x - p) = L_σ Ψ(·, x)`). -/
theorem generator_selectionGreen_of_lt (σ : ℝ) {p x : ℝ} (hpx : p < x) :
    generator σ (fun q => selectionGreen σ q x) p = 0 := by
  rw [generator_congr (g := fun q => 0 + 2 * (1 - kimuraFixation σ x) /
    (x * (1 - x) * (kimuraSlope σ * exp (-2 * σ * x))) * kimuraFixation σ q)]
  · exact generator_affine_kimuraFixation σ _ _ p
  · filter_upwards [Iio_mem_nhds hpx] with q hq
    simp only [selectionGreen, min_eq_left (le_of_lt hq), max_eq_right (le_of_lt hq)]
    ring

/-- Above the target frequency: `L_σ Ψ(·, x) = 0` at every `p > x`. -/
theorem generator_selectionGreen_of_gt (σ : ℝ) {p x : ℝ} (hxp : x < p) :
    generator σ (fun q => selectionGreen σ q x) p = 0 := by
  rw [generator_congr (g := fun q => 2 * kimuraFixation σ x /
    (x * (1 - x) * (kimuraSlope σ * exp (-2 * σ * x))) + -(2 * kimuraFixation σ x /
    (x * (1 - x) * (kimuraSlope σ * exp (-2 * σ * x)))) * kimuraFixation σ q)]
  · exact generator_affine_kimuraFixation σ _ _ p
  · filter_upwards [Ioi_mem_nhds hxp] with q hq
    simp only [selectionGreen, min_eq_right (le_of_lt hq), max_eq_left (le_of_lt hq)]
    ring

/-- The sojourn density is continuous in the starting frequency (in particular at `p = x`). -/
theorem continuous_selectionGreen_left (σ x : ℝ) : Continuous fun p => selectionGreen σ p x :=
  (((continuous_const.mul ((continuous_kimuraFixation σ).comp
    (continuous_id.min continuous_const))).mul (continuous_const.sub
    ((continuous_kimuraFixation σ).comp (continuous_id.max continuous_const)))).div_const _)

/-- Left derivative at the diagonal: `∂_p Ψ(x⁻, x) = 2 (1 - u(x)) / (x (1 - x))`. Together with
`hasDerivWithinAt_selectionGreen_Ici` this gives the jump `-2 / (x (1 - x))` of `∂_p Ψ` at
`p = x`, i.e. `L_σ Ψ(·, x) = -δ_x` in the distributional sense. -/
theorem hasDerivWithinAt_selectionGreen_Iic (σ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (fun p => selectionGreen σ p x)
      (2 * (1 - kimuraFixation σ x) / (x * (1 - x))) (Iic x) x := by
  have hK := (kimuraSlope_pos σ).ne'
  have hE := (exp_pos (-2 * σ * x)).ne'
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  have hc := ((hasDerivAt_kimuraFixation σ x).const_mul (2 * (1 - kimuraFixation σ x) /
    (x * (1 - x) * (kimuraSlope σ * exp (-2 * σ * x))))).hasDerivWithinAt (s := Iic x)
  refine (hc.congr (fun q hq => ?_) ?_).congr_deriv ?_
  · simp only [selectionGreen, min_eq_left (show q ≤ x from hq), max_eq_right (show q ≤ x from hq)]
    ring
  · simp only [selectionGreen, min_self, max_self]
    ring
  · field_simp

/-- Right derivative at the diagonal: `∂_p Ψ(x⁺, x) = -2 u(x) / (x (1 - x))`. -/
theorem hasDerivWithinAt_selectionGreen_Ici (σ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (fun p => selectionGreen σ p x)
      (-(2 * kimuraFixation σ x / (x * (1 - x)))) (Ici x) x := by
  have hK := (kimuraSlope_pos σ).ne'
  have hE := (exp_pos (-2 * σ * x)).ne'
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  have hc := (((hasDerivAt_kimuraFixation σ x).const_mul (-(2 * kimuraFixation σ x /
    (x * (1 - x) * (kimuraSlope σ * exp (-2 * σ * x)))))).const_add (2 * kimuraFixation σ x /
    (x * (1 - x) * (kimuraSlope σ * exp (-2 * σ * x))))).hasDerivWithinAt (s := Ici x)
  refine (hc.congr (fun q hq => ?_) ?_).congr_deriv ?_
  · simp only [selectionGreen, min_eq_right (show x ≤ q from hq), max_eq_left (show x ≤ q from hq)]
    ring
  · simp only [selectionGreen, min_self, max_self]
    ring
  · field_simp

/-- The Maruyama–Kimura conditional sojourn density (the paper's `Ψ_z(p, z)`): given the initial
frequency `p` and the current frequency `x`, the density of mean time spent at frequency `z`
along the path, `Ψ(p, z) Ψ(z, x) / Ψ(p, x)` (Maruyama and Kimura 1975; Kiezun et al. 2013,
Methods). Time in units of `2N` generations. -/
noncomputable def ageDensity (σ p x z : ℝ) : ℝ :=
  selectionGreen σ p z * selectionGreen σ z x / selectionGreen σ p x

/-- The paper's closed form `Ψ₁(z)` for `0 < z < x` (Kiezun et al. 2013, Methods), in units of
`2N` generations with `σ = 2Ns`:
`(e^{-2σ(1-z)} - 1)(e^{-2σz} - 1) / (σ z (1 - z) (1 - e^{-2σ}))`, and its continuous extension
`2` for `σ = 0`. It does not depend on the current frequency `x`. -/
noncomputable def maruyamaBelow (σ z : ℝ) : ℝ :=
  if σ = 0 then 2 else
    (exp (-2 * σ * (1 - z)) - 1) * (exp (-2 * σ * z) - 1) /
      (σ * z * (1 - z) * (1 - exp (-2 * σ)))

/-- The paper's closed form `Ψ₂(z)` for `x < z < 1` (Kiezun et al. 2013, Methods), in units of
`2N` generations with `σ = 2Ns`:
`(e^{-2σ(1-z)} - 1)(e^{2σ(1-z)} - 1)(1 - e^{2σx}) /
(σ z (1 - z)(e^{-2σ(1-x)} - 1)(1 - e^{2σ}))`, and its continuous extension
`2 x (1 - z) / ((1 - x) z)` for `σ = 0`. -/
noncomputable def maruyamaAbove (σ x z : ℝ) : ℝ :=
  if σ = 0 then 2 * x * (1 - z) / ((1 - x) * z) else
    (exp (-2 * σ * (1 - z)) - 1) * (exp (2 * σ * (1 - z)) - 1) * (1 - exp (2 * σ * x)) /
      (σ * z * (1 - z) * (exp (-2 * σ * (1 - x)) - 1) * (1 - exp (2 * σ)))

/-- The mean age of an allele at current frequency `x` (the paper's `a(x)`), in units of `2N`
generations: `∫₀^x Ψ₁(z) dz + ∫_x^1 Ψ₂(z) dz`. -/
noncomputable def meanAge (σ x : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..x, maruyamaBelow σ z) + ∫ z in x..1, maruyamaAbove σ x z

private theorem exp_ne_exp_of_ne {σ a b : ℝ} (hσ : σ ≠ 0) (hab : a ≠ b) :
    exp (-2 * σ * a) - exp (-2 * σ * b) ≠ 0 := by
  rw [sub_ne_zero, Ne, exp_eq_exp]
  intro h
  exact hab (mul_left_cancel₀ (by simpa using hσ : -2 * σ ≠ 0) h)

/-- `Ψ₁` through Kimura's fixation probability: `Ψ₁(z) = 2 u(z)(1 - u(z)) / (z (1 - z) u'(z))`
on `(0, 1)`. -/
theorem maruyamaBelow_eq {σ z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    maruyamaBelow σ z = 2 * kimuraFixation σ z * (1 - kimuraFixation σ z) /
      (z * (1 - z) * (kimuraSlope σ * exp (-2 * σ * z))) := by
  have h0 : z ≠ 0 := hz.1.ne'
  have h1 : 1 - z ≠ 0 := (sub_pos.2 hz.2).ne'
  by_cases hσ : σ = 0
  · subst hσ
    simp [maruyamaBelow, kimuraSlope]
    field_simp
  have hd := one_sub_exp_ne_zero hσ
  have hb := (exp_pos (-2 * σ * z)).ne'
  have e1 : exp (-2 * σ * (1 - z)) = exp (-2 * σ) / exp (-2 * σ * z) := by
    rw [← exp_sub]; ring_nf
  simp only [maruyamaBelow, kimuraFixation, kimuraSlope, hσ, ↓reduceIte, e1]
  generalize exp (-2 * σ) = A at *
  generalize exp (-2 * σ * z) = B at *
  have hd' : 1 - A ≠ 0 := hd
  field_simp
  ring

/-- `Ψ₂` through Kimura's fixation probability:
`Ψ₂(z) = 2 u(x)(1 - u(z))² / ((1 - u(x)) z (1 - z) u'(z))` on `(0, 1)`. -/
theorem maruyamaAbove_eq {σ x z : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    maruyamaAbove σ x z = 2 * kimuraFixation σ x * (1 - kimuraFixation σ z) ^ 2 /
      ((1 - kimuraFixation σ x) * z * (1 - z) * (kimuraSlope σ * exp (-2 * σ * z))) := by
  have h0 : z ≠ 0 := hz.1.ne'
  have h1 : 1 - z ≠ 0 := (sub_pos.2 hz.2).ne'
  have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  by_cases hσ : σ = 0
  · subst hσ
    simp [maruyamaAbove, kimuraSlope]
    field_simp
  have hd := one_sub_exp_ne_zero hσ
  have ha := (exp_pos (-2 * σ)).ne'
  have hb := (exp_pos (-2 * σ * z)).ne'
  have hc := (exp_pos (-2 * σ * x)).ne'
  have hxc : exp (-2 * σ * x) - exp (-2 * σ * 1) ≠ 0 := exp_ne_exp_of_ne hσ hx.2.ne
  rw [mul_one] at hxc
  have e1 : exp (-2 * σ * (1 - z)) = exp (-2 * σ) / exp (-2 * σ * z) := by
    rw [← exp_sub]; ring_nf
  have e2 : exp (2 * σ * (1 - z)) = exp (-2 * σ * z) / exp (-2 * σ) := by
    rw [← exp_sub]; ring_nf
  have e3 : exp (2 * σ * x) = 1 / exp (-2 * σ * x) := by
    rw [one_div, ← exp_neg]; ring_nf
  have e4 : exp (-2 * σ * (1 - x)) = exp (-2 * σ) / exp (-2 * σ * x) := by
    rw [← exp_sub]; ring_nf
  have e5 : exp (2 * σ) = 1 / exp (-2 * σ) := by
    rw [one_div, ← exp_neg]; ring_nf
  have hxc' : exp (-2 * σ) - exp (-2 * σ * x) ≠ 0 := fun h => hxc (by linarith)
  simp only [maruyamaAbove, kimuraFixation, kimuraSlope, hσ, ↓reduceIte, e1, e2, e3, e4, e5]
  generalize exp (-2 * σ) = A at *
  generalize exp (-2 * σ * z) = B at *
  generalize exp (-2 * σ * x) = C at *
  have hAC : A - C ≠ 0 := hxc'
  have hCA : C - A ≠ 0 := fun h => hAC (by linarith)
  have hA1 : A - 1 ≠ 0 := fun h => hd (by linarith)
  have hux : 1 - (1 - C) / (1 - A) = (C - A) / (1 - A) := by field_simp; ring
  have huz : 1 - (1 - B) / (1 - A) = (B - A) / (1 - A) := by field_simp; ring
  rw [hux, huz]
  field_simp
  ring

/-- **Closed form below the current frequency.** For `0 < p ≤ z ≤ x < 1` the conditional sojourn
density is the paper's `Ψ₁(z)`; it depends neither on `p` nor on `x`. -/
theorem ageDensity_of_le_of_le (σ : ℝ) {p x z : ℝ} (hp : 0 < p) (hpz : p ≤ z) (hzx : z ≤ x)
    (hx : x < 1) : ageDensity σ p x z = maruyamaBelow σ z := by
  have hz : z ∈ Ioo (0 : ℝ) 1 := ⟨hp.trans_le hpz, hzx.trans_lt hx⟩
  have hx0 : x ≠ 0 := (hz.1.trans_le hzx).ne'
  have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx).ne'
  have hup := (kimuraFixation_pos σ hp).ne'
  have hux := (sub_pos.2 (kimuraFixation_lt_one σ hx)).ne'
  have hK := (kimuraSlope_pos σ).ne'
  have hE := (exp_pos (-2 * σ * x)).ne'
  rw [maruyamaBelow_eq hz]
  simp only [ageDensity, selectionGreen, min_eq_left hpz, max_eq_right hpz, min_eq_left hzx,
    max_eq_right hzx, min_eq_left (hpz.trans hzx), max_eq_right (hpz.trans hzx)]
  field_simp

/-- **Closed form above the current frequency.** For `0 < p ≤ x ≤ z < 1` the conditional sojourn
density is the paper's `Ψ₂(z)`; it does not depend on `p`. -/
theorem ageDensity_of_le_of_ge (σ : ℝ) {p x z : ℝ} (hp : 0 < p) (hpx : p ≤ x) (hxz : x ≤ z)
    (hz : z < 1) : ageDensity σ p x z = maruyamaAbove σ x z := by
  have hx : x ∈ Ioo (0 : ℝ) 1 := ⟨hp.trans_le hpx, hxz.trans_lt hz⟩
  have hz' : z ∈ Ioo (0 : ℝ) 1 := ⟨hx.1.trans_le hxz, hz⟩
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  have hup := (kimuraFixation_pos σ hp).ne'
  have hux := (sub_pos.2 (kimuraFixation_lt_one σ hx.2)).ne'
  have hK := (kimuraSlope_pos σ).ne'
  have hE := (exp_pos (-2 * σ * x)).ne'
  rw [maruyamaAbove_eq hx hz']
  simp only [ageDensity, selectionGreen, min_eq_left (hpx.trans hxz),
    max_eq_right (hpx.trans hxz), min_eq_right hxz, max_eq_left hxz, min_eq_left hpx,
    max_eq_right hpx]
  field_simp

/-- **Paper units.** With `N` diploid individuals, selection coefficient `s ≠ 0` and time in
generations, the paper prints `Ψ₁(z) = (e^{-γ(1-z)} - 1)(e^{-γz} - 1) / (s z (1 - z)(1 - e^{-γ}))`
with `γ = 4Ns`; it equals `2N · maruyamaBelow (2Ns) z`. -/
theorem maruyamaBelow_generations {N s : ℝ} (hN : 0 < N) (hs : s ≠ 0) (z : ℝ) :
    2 * N * maruyamaBelow (2 * N * s) z =
      (exp (-(4 * N * s) * (1 - z)) - 1) * (exp (-(4 * N * s) * z) - 1) /
        (s * z * (1 - z) * (1 - exp (-(4 * N * s)))) := by
  have hσ : 2 * N * s ≠ 0 := by positivity
  have k1 : ∀ y, -2 * (2 * N * s) * y = -(4 * N * s) * y := fun y => by ring
  have k0 : -2 * (2 * N * s) = -(4 * N * s) := by ring
  simp only [maruyamaBelow, hσ, ↓reduceIte, k0]
  rw [show 2 * N * s * z * (1 - z) * (1 - exp (-(4 * N * s))) =
    2 * N * (s * z * (1 - z) * (1 - exp (-(4 * N * s)))) by ring, ← mul_div_assoc,
    mul_div_mul_left _ _ (by positivity : (2 * N : ℝ) ≠ 0)]

/-- **Paper units.** The paper's
`Ψ₂(z) = (e^{-γ(1-z)} - 1)(e^{γ(1-z)} - 1)(1 - e^{γx}) / (s z (1 - z)(e^{-γ(1-x)} - 1)(1 - e^{γ}))`,
`γ = 4Ns`, equals `2N · maruyamaAbove (2Ns) x z`. -/
theorem maruyamaAbove_generations {N s : ℝ} (hN : 0 < N) (hs : s ≠ 0) (x z : ℝ) :
    2 * N * maruyamaAbove (2 * N * s) x z =
      (exp (-(4 * N * s) * (1 - z)) - 1) * (exp (4 * N * s * (1 - z)) - 1) *
          (1 - exp (4 * N * s * x)) /
        (s * z * (1 - z) * (exp (-(4 * N * s) * (1 - x)) - 1) * (1 - exp (4 * N * s))) := by
  have hσ : 2 * N * s ≠ 0 := by positivity
  have k1 : ∀ y, -2 * (2 * N * s) * y = -(4 * N * s) * y := fun y => by ring
  have k0 : 2 * (2 * N * s) = 4 * N * s := by ring
  simp only [maruyamaAbove, hσ, ↓reduceIte, k1, k0]
  rw [show 2 * N * s * z * (1 - z) * (exp (-(4 * N * s) * (1 - x)) - 1) *
      (1 - exp (4 * N * s)) =
    2 * N * (s * z * (1 - z) * (exp (-(4 * N * s) * (1 - x)) - 1) * (1 - exp (4 * N * s)))
      by ring, ← mul_div_assoc, mul_div_mul_left _ _ (by positivity : (2 * N : ℝ) ≠ 0)]

/-- **Kimura and Ohta (1973).** The mean age of a neutral allele at frequency `x ∈ (0, 1)` is
`-2 x log x / (1 - x)` in units of `2N` generations (`-4N x ln x / (1 - x)` generations). -/
theorem meanAge_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    meanAge 0 x = -2 * x * log x / (1 - x) := by
  have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  have hcongr : ∫ z in x..1, maruyamaAbove 0 x z =
      ∫ z in x..1, (2 * x / (1 - x) * (1 / z) - 2 * x / (1 - x)) := by
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [uIcc_of_le hx.2.le] at hz
    have hz0 : z ≠ 0 := (hx.1.trans_le hz.1).ne'
    simp only [maruyamaAbove, ↓reduceIte]
    field_simp
  have hi : IntervalIntegrable (fun z : ℝ => 2 * x / (1 - x) * (1 / z)) volume x 1 :=
    (intervalIntegral.intervalIntegrable_one_div (fun z hz => by
      rw [uIcc_of_le hx.2.le] at hz; exact (hx.1.trans_le hz.1).ne') continuousOn_id).const_mul _
  simp only [meanAge, maruyamaBelow, ↓reduceIte, hcongr]
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_const_mul,
    integral_one_div_of_pos hx.1 one_pos, intervalIntegral.integral_const,
    intervalIntegral.integral_const, log_div one_ne_zero hx.1.ne', log_one]
  simp only [smul_eq_mul]
  field_simp
  ring

private theorem one_sub_exp_neg_two_mul (u : ℝ) : 1 - exp (-2 * u) = 2 * exp (-u) * sinh u := by
  have e : exp (-2 * u) = exp (-u) * exp (-u) := by rw [← exp_add]; ring_nf
  have e2 : exp (-u) * exp u = 1 := by rw [← exp_add]; simp
  rw [sinh_eq, e]
  linear_combination (-1 : ℝ) * e2

private theorem exp_two_mul_sub_one (u : ℝ) : exp (2 * u) - 1 = 2 * exp u * sinh u := by
  have e : exp (2 * u) = exp u * exp u := by rw [← exp_add]; ring_nf
  have e2 : exp (-u) * exp u = 1 := by rw [← exp_add]; simp
  rw [sinh_eq, e]
  linear_combination e2

/-- `Ψ₁` in hyperbolic form: `2 sinh(σz) sinh(σ(1 - z)) / (σ z (1 - z) sinh σ)` for `σ ≠ 0`. -/
theorem maruyamaBelow_eq_sinh {σ z : ℝ} (hσ : σ ≠ 0) (hz : z ∈ Ioo (0 : ℝ) 1) :
    maruyamaBelow σ z = 2 * sinh (σ * z) * sinh (σ * (1 - z)) / (σ * z * (1 - z) * sinh σ) := by
  have h0 : z ≠ 0 := hz.1.ne'
  have h1 : 1 - z ≠ 0 := (sub_pos.2 hz.2).ne'
  have hs : sinh σ ≠ 0 := fun h => hσ (sinh_eq_zero.1 h)
  have a1 := one_sub_exp_neg_two_mul (σ * (1 - z))
  have a2 := one_sub_exp_neg_two_mul (σ * z)
  have a3 := one_sub_exp_neg_two_mul σ
  have e : exp (-σ) = exp (-(σ * (1 - z))) * exp (-(σ * z)) := by rw [← exp_add]; ring_nf
  rw [show -2 * (σ * (1 - z)) = -2 * σ * (1 - z) by ring] at a1
  rw [show -2 * (σ * z) = -2 * σ * z by ring] at a2
  simp only [maruyamaBelow, hσ, ↓reduceIte]
  rw [show exp (-2 * σ * (1 - z)) - 1 = -(1 - exp (-2 * σ * (1 - z))) by ring,
    show exp (-2 * σ * z) - 1 = -(1 - exp (-2 * σ * z)) by ring, a1, a2, a3, e]
  have p1 := (exp_pos (-(σ * (1 - z)))).ne'
  have p2 := (exp_pos (-(σ * z))).ne'
  field_simp

/-- `Ψ₂` in hyperbolic form:
`2 sinh(σ(1 - z))² sinh(σx) / (σ sinh σ sinh(σ(1 - x)) z (1 - z))` for `σ ≠ 0`. -/
theorem maruyamaAbove_eq_sinh {σ x z : ℝ} (hσ : σ ≠ 0) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    maruyamaAbove σ x z = 2 * sinh (σ * (1 - z)) ^ 2 * sinh (σ * x) /
      (σ * sinh σ * sinh (σ * (1 - x)) * z * (1 - z)) := by
  have h0 : z ≠ 0 := hz.1.ne'
  have h1 : 1 - z ≠ 0 := (sub_pos.2 hz.2).ne'
  have hs : sinh σ ≠ 0 := fun h => hσ (sinh_eq_zero.1 h)
  have hsx : sinh (σ * (1 - x)) ≠ 0 := fun h =>
    mul_ne_zero hσ (sub_pos.2 hx.2).ne' (sinh_eq_zero.1 h)
  have a1 := one_sub_exp_neg_two_mul (σ * (1 - z))
  have a2 := exp_two_mul_sub_one (σ * (1 - z))
  have a3 := exp_two_mul_sub_one (σ * x)
  have a4 := one_sub_exp_neg_two_mul (σ * (1 - x))
  have a5 := exp_two_mul_sub_one σ
  rw [show -2 * (σ * (1 - z)) = -2 * σ * (1 - z) by ring] at a1
  rw [show 2 * (σ * (1 - z)) = 2 * σ * (1 - z) by ring] at a2
  rw [show 2 * (σ * x) = 2 * σ * x by ring] at a3
  rw [show -2 * (σ * (1 - x)) = -2 * σ * (1 - x) by ring] at a4
  have e1 : exp (-(σ * (1 - z))) * exp (σ * (1 - z)) = 1 := by rw [← exp_add]; simp
  have e2 : exp σ = exp (σ * x) * exp (σ * (1 - x)) := by rw [← exp_add]; ring_nf
  have e3 : exp (-(σ * (1 - x))) * exp (σ * (1 - x)) = 1 := by rw [← exp_add]; simp
  simp only [maruyamaAbove, hσ, ↓reduceIte]
  rw [show exp (-2 * σ * (1 - z)) - 1 = -(1 - exp (-2 * σ * (1 - z))) by ring,
    show 1 - exp (2 * σ * x) = -(exp (2 * σ * x) - 1) by ring,
    show exp (-2 * σ * (1 - x)) - 1 = -(1 - exp (-2 * σ * (1 - x))) by ring,
    show 1 - exp (2 * σ) = -(exp (2 * σ) - 1) by ring, a1, a2, a3, a4, a5, e2]
  have p1 := (exp_pos (σ * x)).ne'
  have p2 := (exp_pos (σ * (1 - x))).ne'
  have p3 := (exp_pos (-(σ * (1 - x)))).ne'
  rw [exp_neg (σ * (1 - z)), exp_neg (σ * (1 - x))]
  field_simp

/-- **Symmetry.** `Ψ₁` is the same for `σ` and `-σ`. -/
theorem maruyamaBelow_neg (σ : ℝ) {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    maruyamaBelow (-σ) z = maruyamaBelow σ z := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · simp
  rw [maruyamaBelow_eq_sinh (neg_ne_zero.2 hσ) hz, maruyamaBelow_eq_sinh hσ hz]
  simp only [neg_mul, sinh_neg]
  ring

/-- **Symmetry.** `Ψ₂` is the same for `σ` and `-σ`. -/
theorem maruyamaAbove_neg (σ : ℝ) {x z : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    maruyamaAbove (-σ) x z = maruyamaAbove σ x z := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · simp
  rw [maruyamaAbove_eq_sinh (neg_ne_zero.2 hσ) hx hz, maruyamaAbove_eq_sinh hσ hx hz]
  simp only [neg_mul, sinh_neg, neg_sq, mul_neg, neg_neg, neg_div_neg_eq]

private theorem sinh_lt_mul_cosh {t : ℝ} (ht : 0 < t) : sinh t < t * cosh t := by
  have hmono : StrictMonoOn (fun s => s * cosh s - sinh s) (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop) fun s hs => ?_
    rw [interior_Ici] at hs
    have hd : HasDerivAt (fun s => s * cosh s - sinh s) (s * sinh s) s := by
      convert ((hasDerivAt_id' s).mul (hasDerivAt_cosh s)).sub (hasDerivAt_sinh s) using 1
      ring
    rw [hd.deriv]
    exact mul_pos hs (sinh_pos_iff.2 hs)
  have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 ht.le) ht
  simp at this
  linarith

private theorem sinh_mul_sinh_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) * sinh a * sinh b < a * b * sinh (a + b) := by
  rw [sinh_add]
  have h1 := mul_lt_mul_of_pos_left (sinh_lt_mul_cosh hb) (mul_pos ha (sinh_pos_iff.2 ha))
  have h2 := mul_lt_mul_of_pos_left (sinh_lt_mul_cosh ha) (mul_pos hb (sinh_pos_iff.2 hb))
  nlinarith

private theorem mul_sinh_lt_mul_sinh {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    c * sinh a < a * sinh c := by
  have hca := sub_pos.2 hac
  have k := sinh_mul_sinh_lt ha hca
  rw [show a + (c - a) = c by ring] at k
  have hs : c - a < sinh (c - a) := self_lt_sinh_iff.2 hca
  have hsa := sinh_pos_iff.2 ha
  have h : c * sinh a * (c - a) < a * sinh c * (c - a) := by
    have := mul_lt_mul_of_pos_left hs (mul_pos (ha.trans hac) hsa)
    nlinarith
  exact lt_of_mul_lt_mul_right h hca.le

private theorem maruyamaBelow_lt_two {σ z : ℝ} (hσ : 0 < σ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    maruyamaBelow σ z < 2 := by
  have hz1 := sub_pos.2 hz.2
  have hs := sinh_pos_iff.2 hσ
  rw [maruyamaBelow_eq_sinh hσ.ne' hz, div_lt_iff₀ (mul_pos (mul_pos (mul_pos hσ hz.1) hz1) hs)]
  have k := sinh_mul_sinh_lt (mul_pos hσ hz.1) (mul_pos hσ hz1)
  rw [show σ * z + σ * (1 - z) = σ by ring] at k
  have : σ * (sinh (σ * z) * sinh (σ * (1 - z))) < σ * (σ * z * (1 - z) * sinh σ) := by
    linarith
  linarith [lt_of_mul_lt_mul_left this hσ.le]

private theorem maruyamaBelow_pos_of_pos {σ z : ℝ} (hσ : 0 < σ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 < maruyamaBelow σ z := by
  have hz1 := sub_pos.2 hz.2
  rw [maruyamaBelow_eq_sinh hσ.ne' hz]
  exact div_pos (mul_pos (mul_pos two_pos (sinh_pos_iff.2 (mul_pos hσ hz.1)))
    (sinh_pos_iff.2 (mul_pos hσ hz1))) (mul_pos (mul_pos (mul_pos hσ hz.1) hz1)
    (sinh_pos_iff.2 hσ))

/-- `Ψ₁` is positive on `(0, 1)`. -/
theorem maruyamaBelow_pos (σ : ℝ) {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : 0 < maruyamaBelow σ z := by
  rcases lt_trichotomy σ 0 with h | rfl | h
  · rw [← maruyamaBelow_neg σ hz]
    exact maruyamaBelow_pos_of_pos (neg_pos.2 h) hz
  · simp [maruyamaBelow]
  · exact maruyamaBelow_pos_of_pos h hz

/-- **Maruyama effect, below the current frequency.** For `σ ≠ 0`, `Ψ₁(z) < 2`, its neutral
value, for every `z ∈ (0, 1)`. -/
theorem maruyamaBelow_lt {σ z : ℝ} (hσ : σ ≠ 0) (hz : z ∈ Ioo (0 : ℝ) 1) :
    maruyamaBelow σ z < maruyamaBelow 0 z := by
  rw [show maruyamaBelow 0 z = 2 by simp [maruyamaBelow]]
  rcases lt_or_gt_of_ne hσ with h | h
  · rw [← maruyamaBelow_neg σ hz]
    exact maruyamaBelow_lt_two (neg_pos.2 h) hz
  · exact maruyamaBelow_lt_two h hz

private theorem maruyamaAbove_lt_of_pos {σ x z : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hxz : x < z)
    (hz : z < 1) : maruyamaAbove σ x z < maruyamaAbove 0 x z := by
  have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx, hxz.trans hz⟩
  have hz' : z ∈ Ioo (0 : ℝ) 1 := ⟨hx.trans hxz, hz⟩
  have hz0 := hz'.1
  have hz1 := sub_pos.2 hz
  have hx1 := sub_pos.2 hx'.2
  have hsa := sinh_pos_iff.2 (mul_pos hσ hz1)
  have hsb := sinh_pos_iff.2 (mul_pos hσ hx)
  have hsc := sinh_pos_iff.2 (mul_pos hσ hx1)
  have hs := sinh_pos_iff.2 hσ
  have h1 := mul_sinh_lt_mul_sinh (mul_pos hσ hz1) (by nlinarith : σ * (1 - z) < σ * (1 - x))
  have h2 := sinh_mul_sinh_lt (mul_pos hσ hx) (mul_pos hσ hx1)
  rw [show σ * x + σ * (1 - x) = σ by ring] at h2
  have hsq := pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
  have h3 := mul_lt_mul_of_pos_left hsq (mul_pos hσ hsb)
  have h4 := mul_lt_mul_of_pos_left h2 (by positivity : 0 < (σ * (1 - z)) ^ 2 * sinh (σ * (1 - x)))
  have h5 : σ ^ 3 * (1 - x) * ((1 - x) * sinh (σ * (1 - z)) ^ 2 * sinh (σ * x)) <
      σ ^ 3 * (1 - x) * (σ * (1 - z) ^ 2 * x * sinh (σ * (1 - x)) * sinh σ) := by
    nlinarith
  have h6 := lt_of_mul_lt_mul_left h5 (by positivity)
  rw [maruyamaAbove_eq_sinh hσ.ne' hx' hz']
  simp only [maruyamaAbove, ↓reduceIte]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_lt_mul_of_pos_left h6 (by positivity : (0 : ℝ) < 2 * z)]

/-- **Maruyama effect, above the current frequency.** For `σ ≠ 0` and `0 < x < z < 1`,
`Ψ₂(z)` is strictly below its neutral value `2 x (1 - z) / ((1 - x) z)`. -/
theorem maruyamaAbove_lt {σ x z : ℝ} (hσ : σ ≠ 0) (hx : 0 < x) (hxz : x < z) (hz : z < 1) :
    maruyamaAbove σ x z < maruyamaAbove 0 x z := by
  rcases lt_or_gt_of_ne hσ with h | h
  · rw [← maruyamaAbove_neg σ ⟨hx, hxz.trans hz⟩ ⟨hx.trans hxz, hz⟩]
    exact maruyamaAbove_lt_of_pos (neg_pos.2 h) hx hxz hz
  · exact maruyamaAbove_lt_of_pos h hx hxz hz

private theorem maruyamaAbove_pos_of_pos {σ x z : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hxz : x < z)
    (hz : z < 1) : 0 < maruyamaAbove σ x z := by
  have hz1 := sub_pos.2 hz
  have hx1 := sub_pos.2 (hxz.trans hz)
  rw [maruyamaAbove_eq_sinh hσ.ne' ⟨hx, hxz.trans hz⟩ ⟨hx.trans hxz, hz⟩]
  exact div_pos (mul_pos (mul_pos two_pos (pow_pos (sinh_pos_iff.2 (mul_pos hσ hz1)) 2))
    (sinh_pos_iff.2 (mul_pos hσ hx))) (mul_pos (mul_pos (mul_pos (mul_pos hσ
    (sinh_pos_iff.2 hσ)) (sinh_pos_iff.2 (mul_pos hσ hx1))) (hx.trans hxz)) hz1)

/-- `Ψ₂` is positive for `0 < x < z < 1`. -/
theorem maruyamaAbove_pos (σ : ℝ) {x z : ℝ} (hx : 0 < x) (hxz : x < z) (hz : z < 1) :
    0 < maruyamaAbove σ x z := by
  rcases lt_trichotomy σ 0 with h | rfl | h
  · rw [← maruyamaAbove_neg σ ⟨hx, hxz.trans hz⟩ ⟨hx.trans hxz, hz⟩]
    exact maruyamaAbove_pos_of_pos (neg_pos.2 h) hx hxz hz
  · simp only [maruyamaAbove, ↓reduceIte]
    have := sub_pos.2 hz
    have := sub_pos.2 (hxz.trans hz)
    have := hx.trans hxz
    positivity
  · exact maruyamaAbove_pos_of_pos h hx hxz hz

/-- At `z = 1` the closed form `Ψ₂` vanishes (a null set for the integral). -/
@[simp]
theorem maruyamaAbove_one_right (σ x : ℝ) : maruyamaAbove σ x 1 = 0 := by
  simp [maruyamaAbove]

/-- At `z = 1` the lower closed form vanishes for `σ ≠ 0`, and equals `2` for `σ = 0`. -/
private theorem maruyamaBelow_one_le (σ : ℝ) : ‖maruyamaBelow σ 1‖ ≤ 2 := by
  unfold maruyamaBelow
  split_ifs <;> simp

private theorem measurable_maruyamaBelow (σ : ℝ) : Measurable (maruyamaBelow σ) := by
  unfold maruyamaBelow
  split_ifs
  · exact measurable_const
  · fun_prop

private theorem measurable_maruyamaAbove (σ x : ℝ) : Measurable (maruyamaAbove σ x) := by
  unfold maruyamaAbove
  split_ifs <;> fun_prop

/-- `Ψ₁` is integrable on `[0, x]` (it is bounded by `2`). -/
theorem intervalIntegrable_maruyamaBelow (σ : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (maruyamaBelow σ) volume 0 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1]
  refine Measure.integrableOn_of_bounded (M := 2) measure_Ioc_lt_top.ne
    (measurable_maruyamaBelow σ).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun z hz => ?_)
  rcases (hz.2.trans hx.2).eq_or_lt with rfl | hz1
  · exact maruyamaBelow_one_le σ
  have hz' : z ∈ Ioo (0 : ℝ) 1 := ⟨hz.1, hz1⟩
  rw [Real.norm_of_nonneg (maruyamaBelow_pos σ hz').le]
  rcases eq_or_ne σ 0 with rfl | hσ
  · simp [maruyamaBelow]
  · exact (maruyamaBelow_lt hσ hz').le.trans (by simp [maruyamaBelow])

/-- `Ψ₂` is integrable on `[x, 1]` for `x ∈ (0, 1)` (it is bounded by `2 / (1 - x)`). -/
theorem intervalIntegrable_maruyamaAbove (σ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (maruyamaAbove σ x) volume x 1 := by
  have hx1 := sub_pos.2 hx.2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.2.le]
  refine Measure.integrableOn_of_bounded (M := 2 / (1 - x)) measure_Ioc_lt_top.ne
    (measurable_maruyamaAbove σ x).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun z hz => ?_)
  rcases hz.2.eq_or_lt with rfl | hz1
  · simp only [maruyamaAbove_one_right, norm_zero]
    positivity
  have hz0 : 0 < z := hx.1.trans hz.1
  have hneutral : maruyamaAbove 0 x z ≤ 2 / (1 - x) := by
    simp only [maruyamaAbove, ↓reduceIte]
    rw [div_le_div_iff₀ (by positivity) hx1]
    have h : x * (1 - z) < z := by nlinarith [hz.1, hx.1]
    nlinarith [mul_lt_mul_of_pos_left h hx1]
  rw [Real.norm_of_nonneg (maruyamaAbove_pos σ hx.1 hz.1 hz1).le]
  rcases eq_or_ne σ 0 with rfl | hσ
  · exact hneutral
  · exact (maruyamaAbove_lt hσ hx.1 hz.1 hz1).le.trans hneutral

/-- **Symmetry.** The mean age is the same for `σ` and `-σ`. -/
theorem meanAge_neg (σ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : meanAge (-σ) x = meanAge σ x := by
  unfold meanAge
  congr 1
  · refine intervalIntegral.integral_congr_ae (ae_of_all _ fun z hz => ?_)
    rw [uIoc_of_le hx.1.le] at hz
    exact maruyamaBelow_neg σ ⟨hz.1, hz.2.trans_lt hx.2⟩
  · refine intervalIntegral.integral_congr_ae (ae_of_all _ fun z hz => ?_)
    rw [uIoc_of_le hx.2.le] at hz
    rcases hz.2.eq_or_lt with rfl | hz1
    · simp
    · exact maruyamaAbove_neg σ hx ⟨hx.1.trans hz.1, hz1⟩

/-- **The Maruyama effect (Kiezun et al. 2013).** For `σ ≠ 0` and `x ∈ (0, 1)`, an allele under
selection, advantageous or deleterious, is on average strictly younger than a neutral allele at
the same frequency. -/
theorem meanAge_lt {σ x : ℝ} (hσ : σ ≠ 0) (hx : x ∈ Ioo (0 : ℝ) 1) :
    meanAge σ x < meanAge 0 x := by
  have hb0 := intervalIntegrable_maruyamaBelow 0 (Ioo_subset_Icc_self hx)
  have hbσ := intervalIntegrable_maruyamaBelow σ (Ioo_subset_Icc_self hx)
  have ha0 := intervalIntegrable_maruyamaAbove 0 hx
  have haσ := intervalIntegrable_maruyamaAbove σ hx
  have I1 := intervalIntegral.intervalIntegral_pos_of_pos_on (hb0.sub hbσ)
    (fun z hz => sub_pos.2 (maruyamaBelow_lt hσ ⟨hz.1, hz.2.trans hx.2⟩)) hx.1
  have I2 := intervalIntegral.intervalIntegral_pos_of_pos_on (ha0.sub haσ)
    (fun z hz => sub_pos.2 (maruyamaAbove_lt hσ hx.1 hz.1 hz.2)) hx.2
  rw [intervalIntegral.integral_sub hb0 hbσ] at I1
  rw [intervalIntegral.integral_sub ha0 haσ] at I2
  unfold meanAge
  linarith

/-- Mean value bound `u(z) ≤ z u'(z) e^{2|σ|}` for `z ∈ (0, 1]`. -/
private theorem kimuraFixation_le_mul (σ : ℝ) {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) :
    kimuraFixation σ z ≤ z * (kimuraSlope σ * exp (-2 * σ * z)) * exp (2 * |σ|) := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (kimuraFixation σ)
    (fun y => kimuraSlope σ * exp (-2 * σ * y)) hz.1
    (continuous_kimuraFixation σ).continuousOn
    (fun y _ => hasDerivAt_kimuraFixation σ y)
  simp only [kimuraFixation_zero_right, sub_zero] at hcd
  rw [eq_div_iff hz.1.ne'] at hcd
  rw [← hcd]
  have hK := kimuraSlope_pos σ
  have hexp : exp (-2 * σ * c) ≤ exp (-2 * σ * z) * exp (2 * |σ|) := by
    rw [← exp_add]
    refine exp_le_exp.2 ?_
    have h1 : σ * (z - c) ≤ |σ| * (z - c) :=
      mul_le_mul_of_nonneg_right (le_abs_self σ) (sub_pos.2 hc.2).le
    have h2 : |σ| * (z - c) ≤ |σ| := by
      have : z - c ≤ 1 := by linarith [hc.1, hz.2]
      nlinarith [abs_nonneg σ]
    linarith
  calc kimuraSlope σ * exp (-2 * σ * c) * z
      ≤ kimuraSlope σ * (exp (-2 * σ * z) * exp (2 * |σ|)) * z := by gcongr; exact hz.1.le
    _ = z * (kimuraSlope σ * exp (-2 * σ * z)) * exp (2 * |σ|) := by ring

/-- The conditional sojourn density below the initial frequency. -/
private theorem ageDensity_of_le_of_le' (σ : ℝ) {p x z : ℝ} (hz : 0 < z) (hzp : z ≤ p)
    (hpx : p ≤ x) (hx : x < 1) :
    ageDensity σ p x z = 2 * kimuraFixation σ z ^ 2 * (1 - kimuraFixation σ p) /
      (kimuraFixation σ p * (z * (1 - z) * (kimuraSlope σ * exp (-2 * σ * z)))) := by
  have hp := hz.trans_le hzp
  have hx0 : x ≠ 0 := (hp.trans_le hpx).ne'
  have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx).ne'
  have hup := (kimuraFixation_pos σ hp).ne'
  have hux := (sub_pos.2 (kimuraFixation_lt_one σ hx)).ne'
  have hK := (kimuraSlope_pos σ).ne'
  have hE := (exp_pos (-2 * σ * x)).ne'
  simp only [ageDensity, selectionGreen, min_eq_right hzp, max_eq_left hzp,
    min_eq_left (hzp.trans hpx), max_eq_right (hzp.trans hpx), min_eq_left hpx,
    max_eq_right hpx]
  field_simp

/-- A uniform bound below the initial frequency, for `z ≤ 1/2`. -/
private theorem norm_ageDensity_le (σ : ℝ) {p x z : ℝ} (hz : 0 < z) (hzp : z ≤ p)
    (hpx : p ≤ x) (hx : x < 1) (hz2 : z ≤ 1 / 2) :
    ‖ageDensity σ p x z‖ ≤ 4 * exp (2 * |σ|) := by
  have hp := hz.trans_le hzp
  have hz1 : 0 < 1 - z := by linarith
  have hu := kimuraFixation_pos σ hz
  have hup := kimuraFixation_pos σ hp
  have hle : kimuraFixation σ z ≤ kimuraFixation σ p := (strictMono_kimuraFixation σ).monotone hzp
  have hup1 := kimuraFixation_lt_one σ (hpx.trans_lt hx)
  have hD : 0 < kimuraSlope σ * exp (-2 * σ * z) := mul_pos (kimuraSlope_pos σ) (exp_pos _)
  have hm := kimuraFixation_le_mul σ ⟨hz, by linarith⟩
  rw [ageDensity_of_le_of_le' σ hz hzp hpx hx]
  have hnn : 0 ≤ 2 * kimuraFixation σ z ^ 2 * (1 - kimuraFixation σ p) /
      (kimuraFixation σ p * (z * (1 - z) * (kimuraSlope σ * exp (-2 * σ * z)))) := by
    have := sub_pos.2 hup1
    positivity
  rw [Real.norm_of_nonneg hnn, div_le_iff₀ (by positivity)]
  have he := exp_pos (2 * |σ|)
  -- `2 u_z² (1 - u_p) ≤ 2 u_z u_p ≤ 2 u_p z D e ≤ 4 e u_p z (1 - z) D`
  have h1 : 2 * kimuraFixation σ z ^ 2 * (1 - kimuraFixation σ p) ≤
      2 * kimuraFixation σ z * kimuraFixation σ p := by
    have : kimuraFixation σ z * (1 - kimuraFixation σ p) ≤ kimuraFixation σ p := by
      nlinarith
    nlinarith
  have h2 : 2 * kimuraFixation σ z * kimuraFixation σ p ≤
      2 * (z * (kimuraSlope σ * exp (-2 * σ * z)) * exp (2 * |σ|)) * kimuraFixation σ p := by
    nlinarith
  have h3 : 2 * (z * (kimuraSlope σ * exp (-2 * σ * z)) * exp (2 * |σ|)) * kimuraFixation σ p ≤
      4 * exp (2 * |σ|) * (kimuraFixation σ p * (z * (1 - z) *
        (kimuraSlope σ * exp (-2 * σ * z)))) := by
    have : 0 ≤ z * (kimuraSlope σ * exp (-2 * σ * z)) * exp (2 * |σ|) * kimuraFixation σ p :=
      by positivity
    nlinarith
  linarith

/-- **Mean age as the limit of conditional sojourn times** (Maruyama 1974; Kiezun et al. 2013,
Methods): for `x ∈ (0, 1)`, the total conditional sojourn time `∫₀¹ Ψ_z(p, z) dz` of a path
from initial frequency `p` to current frequency `x` tends to the mean age `a(x)` as `p → 0⁺`
(an allele arises at frequency close to `0`). -/
theorem tendsto_integral_ageDensity (σ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun p => ∫ z in (0 : ℝ)..1, ageDensity σ p x z) (𝓝[>] 0) (𝓝 (meanAge σ x)) := by
  set C := 4 * exp (2 * |σ|)
  have hC : 0 ≤ C := by positivity
  have hb := intervalIntegrable_maruyamaBelow σ (Ioo_subset_Icc_self hx)
  have ha := intervalIntegrable_maruyamaAbove σ hx
  -- the integral splits for small `p`
  have hsplit : ∀ᶠ p in 𝓝[>] (0 : ℝ), ‖(∫ z in (0 : ℝ)..1, ageDensity σ p x z) - meanAge σ x‖ ≤
      (C + 2) * p := by
    have hpos : Ioo (0 : ℝ) (min x (1 / 2)) ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (lt_min hx.1 (by norm_num))
    filter_upwards [hpos] with p hp
    have hpx : p < x := hp.2.trans_le (min_le_left _ _)
    have hp2 : p ≤ 1 / 2 := (hp.2.trans_le (min_le_right _ _)).le
    have hbnd : ∀ z ∈ uIoc (0 : ℝ) p, ‖ageDensity σ p x z‖ ≤ C := by
      intro z hz
      rw [uIoc_of_le hp.1.le] at hz
      exact norm_ageDensity_le σ hz.1 hz.2 hpx.le hx.2 (hz.2.trans hp2)
    have hbnd1 : ∀ z ∈ uIoc (0 : ℝ) p, ‖maruyamaBelow σ z‖ ≤ 2 := by
      intro z hz
      rw [uIoc_of_le hp.1.le] at hz
      have hz' : z ∈ Ioo (0 : ℝ) 1 := ⟨hz.1, hz.2.trans_lt (hpx.trans hx.2)⟩
      rw [Real.norm_of_nonneg (maruyamaBelow_pos σ hz').le]
      rcases eq_or_ne σ 0 with rfl | hσ
      · simp [maruyamaBelow]
      · exact (maruyamaBelow_lt hσ hz').le.trans (by simp [maruyamaBelow])
    have hmeas : Measurable fun z => ageDensity σ p x z := by
      unfold ageDensity selectionGreen
      have := continuous_kimuraFixation σ
      fun_prop
    have hi0 : IntervalIntegrable (fun z => ageDensity σ p x z) volume 0 p := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hp.1.le]
      exact Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
        hmeas.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioc fun z hz =>
          hbnd z (by rwa [uIoc_of_le hp.1.le]))
    have heq1 : EqOn (maruyamaBelow σ) (fun z => ageDensity σ p x z) (uIoo p x) := by
      intro z hz
      rw [uIoo_of_le hpx.le] at hz
      exact (ageDensity_of_le_of_le σ hp.1 hz.1.le hz.2.le hx.2).symm
    have heq2 : EqOn (maruyamaAbove σ x) (fun z => ageDensity σ p x z) (uIoo x 1) := by
      intro z hz
      rw [uIoo_of_le hx.2.le] at hz
      exact (ageDensity_of_le_of_ge σ hp.1 hpx.le hz.1.le hz.2).symm
    have hb' : IntervalIntegrable (maruyamaBelow σ) volume p x :=
      hb.mono_set (by
        rw [uIcc_of_le hx.1.le, uIcc_of_le hpx.le]; exact Icc_subset_Icc hp.1.le le_rfl)
    have hi1 := hb'.congr_uIoo heq1
    have hi2 := ha.congr_uIoo heq2
    have e1 : ∫ z in p..x, ageDensity σ p x z = ∫ z in p..x, maruyamaBelow σ z :=
      (intervalIntegral.integral_congr_uIoo heq1).symm
    have e2 : ∫ z in x..1, ageDensity σ p x z = ∫ z in x..1, maruyamaAbove σ x z :=
      (intervalIntegral.integral_congr_uIoo heq2).symm
    have hb0 : IntervalIntegrable (maruyamaBelow σ) volume 0 p :=
      hb.mono_set (by
        rw [uIcc_of_le hx.1.le, uIcc_of_le hp.1.le]; exact Icc_subset_Icc le_rfl hpx.le)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi0.trans hi1) hi2,
      ← intervalIntegral.integral_add_adjacent_intervals hi0 hi1, e1, e2, meanAge,
      ← intervalIntegral.integral_add_adjacent_intervals hb0 hb']
    have n1 := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    have n2 := intervalIntegral.norm_integral_le_of_norm_le_const hbnd1
    rw [sub_zero, abs_of_pos hp.1] at n1 n2
    calc ‖(∫ z in (0 : ℝ)..p, ageDensity σ p x z) + (∫ z in p..x, maruyamaBelow σ z) +
          (∫ z in x..1, maruyamaAbove σ x z) - ((∫ z in (0 : ℝ)..p, maruyamaBelow σ z) +
          (∫ z in p..x, maruyamaBelow σ z) + ∫ z in x..1, maruyamaAbove σ x z)‖
        = ‖(∫ z in (0 : ℝ)..p, ageDensity σ p x z) - ∫ z in (0 : ℝ)..p, maruyamaBelow σ z‖ := by
          ring_nf
      _ ≤ ‖∫ z in (0 : ℝ)..p, ageDensity σ p x z‖ + ‖∫ z in (0 : ℝ)..p, maruyamaBelow σ z‖ :=
          norm_sub_le _ _
      _ ≤ (C + 2) * p := by linarith
  have hlim : Tendsto (fun p : ℝ => (C + 2) * p) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun p : ℝ => (C + 2) * p) (𝓝 0) (𝓝 ((C + 2) * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' hsplit hlim)

/-- `φ(t) = coth t - 1 / t`, the derivative of `log (sinh t / t)`. -/
private noncomputable def cothSubInv (t : ℝ) : ℝ := cosh t / sinh t - 1 / t

/-- `φ` is positive on `(0, ∞)`, i.e. `tanh t < t`. -/
private theorem cothSubInv_pos {t : ℝ} (ht : 0 < t) : 0 < cothSubInv t := by
  have hs := sinh_pos_iff.2 ht
  have h := sinh_lt_mul_cosh ht
  unfold cothSubInv
  rw [sub_pos, div_lt_div_iff₀ ht hs]
  linarith

/-- `φ` is strictly increasing on `(0, ∞)`: `φ'(t) = 1 / t² - 1 / sinh² t > 0`. -/
private theorem strictMonoOn_cothSubInv : StrictMonoOn cothSubInv (Ioi 0) := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt cothSubInv (1 / t ^ 2 - 1 / sinh t ^ 2) t := by
    intro t ht
    have hs := (sinh_pos_iff.2 (mem_Ioi.1 ht)).ne'
    have ht0 := (mem_Ioi.1 ht).ne'
    have h1 := (hasDerivAt_cosh t).div (hasDerivAt_sinh t) hs
    have h2 := (hasDerivAt_inv ht0)
    convert h1.sub h2 using 1
    · funext s; simp [cothSubInv, one_div]
    · have := cosh_sq_sub_sinh_sq t
      field_simp
      linear_combination (t ^ 2) * this
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt) fun t ht => ?_
  rw [interior_Ioi] at ht
  rw [(hd t ht).deriv]
  have hpos := mem_Ioi.1 ht
  have hs := sinh_pos_iff.2 hpos
  have hlt : t < sinh t := self_lt_sinh_iff.2 hpos
  rw [sub_pos, one_div_lt_one_div (by positivity) (by positivity)]
  exact pow_lt_pow_left₀ hlt hpos.le two_ne_zero

/-- `d/dl log sinh (l a) = a φ(l a) + 1 / l`. -/
private theorem hasDerivAt_log_sinh_mul {a l : ℝ} (ha : 0 < a) (hl : 0 < l) :
    HasDerivAt (fun m => log (sinh (m * a))) (a * cothSubInv (l * a) + 1 / l) l := by
  have hs := (sinh_pos_iff.2 (mul_pos hl ha)).ne'
  have hin : HasDerivAt (fun m => m * a) a l := by simpa using (hasDerivAt_id l).mul_const a
  have h2 : HasDerivAt (fun m => sinh (m * a)) (cosh (l * a) * a) l :=
    (hasDerivAt_sinh _).comp l hin
  convert h2.log hs using 1
  unfold cothSubInv
  field_simp
  ring

/-- `log (Ψ₁ z (1 - z) / 2)` is strictly decreasing in `σ > 0`. -/
private theorem strictAntiOn_log_below {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (fun l => log (sinh (l * z)) + log (sinh (l * (1 - z))) -
      log (sinh (l * 1)) - log l) (Ioi 0) := by
  have hz1 := sub_pos.2 hz.2
  have hd : ∀ l ∈ Ioi (0 : ℝ), HasDerivAt (fun l => log (sinh (l * z)) +
      log (sinh (l * (1 - z))) - log (sinh (l * 1)) - log l)
      (z * cothSubInv (l * z) + (1 - z) * cothSubInv (l * (1 - z)) - cothSubInv l) l := by
    intro l hl
    have hl0 := mem_Ioi.1 hl
    convert (((hasDerivAt_log_sinh_mul hz.1 hl0).add (hasDerivAt_log_sinh_mul hz1 hl0)).sub
      (hasDerivAt_log_sinh_mul one_pos hl0)).sub (hasDerivAt_log hl0.ne') using 1
    rw [mul_one, one_div]
    ring
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun l hl => (hd l hl).continuousAt.continuousWithinAt) fun l hl => ?_
  rw [interior_Ioi] at hl
  rw [(hd l hl).deriv]
  have hl0 := mem_Ioi.1 hl
  have h1 := strictMonoOn_cothSubInv (mem_Ioi.2 (mul_pos hl0 hz.1)) hl
    (by nlinarith [hz.2] : l * z < l)
  have h2 := strictMonoOn_cothSubInv (mem_Ioi.2 (mul_pos hl0 hz1)) hl
    (by nlinarith [hz.1] : l * (1 - z) < l)
  nlinarith [mul_lt_mul_of_pos_left h1 hz.1, mul_lt_mul_of_pos_left h2 hz1]

/-- `log (Ψ₂ z (1 - z) / 2)` is strictly decreasing in `σ > 0`. -/
private theorem strictAntiOn_log_above {x z : ℝ} (hx : 0 < x) (hxz : x < z) (hz : z < 1) :
    StrictAntiOn (fun l => 2 * log (sinh (l * (1 - z))) + log (sinh (l * x)) - log l -
      log (sinh (l * 1)) - log (sinh (l * (1 - x)))) (Ioi 0) := by
  have hz1 := sub_pos.2 hz
  have hx1 := sub_pos.2 (hxz.trans hz)
  have hd : ∀ l ∈ Ioi (0 : ℝ), HasDerivAt (fun l => 2 * log (sinh (l * (1 - z))) +
      log (sinh (l * x)) - log l - log (sinh (l * 1)) - log (sinh (l * (1 - x))))
      (2 * (1 - z) * cothSubInv (l * (1 - z)) + x * cothSubInv (l * x) - cothSubInv l -
        (1 - x) * cothSubInv (l * (1 - x))) l := by
    intro l hl
    have hl0 := mem_Ioi.1 hl
    convert (((((hasDerivAt_log_sinh_mul hz1 hl0).const_mul 2).add
      (hasDerivAt_log_sinh_mul hx hl0)).sub (hasDerivAt_log hl0.ne')).sub
      (hasDerivAt_log_sinh_mul one_pos hl0)).sub (hasDerivAt_log_sinh_mul hx1 hl0) using 1
    rw [mul_one, one_div]
    ring
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun l hl => (hd l hl).continuousAt.continuousWithinAt) fun l hl => ?_
  rw [interior_Ioi] at hl
  rw [(hd l hl).deriv]
  have hl0 := mem_Ioi.1 hl
  have h1 := strictMonoOn_cothSubInv (mem_Ioi.2 (mul_pos hl0 hz1))
    (mem_Ioi.2 (mul_pos hl0 hx1)) (by nlinarith : l * (1 - z) < l * (1 - x))
  have h2 := strictMonoOn_cothSubInv (mem_Ioi.2 (mul_pos hl0 hx)) hl
    (by nlinarith : l * x < l)
  have h3 := strictMonoOn_cothSubInv (mem_Ioi.2 (mul_pos hl0 hx1)) hl
    (by nlinarith : l * (1 - x) < l)
  have h4 := cothSubInv_pos (mul_pos hl0 hx1)
  nlinarith [mul_lt_mul_of_pos_left h1 hz1, mul_lt_mul_of_pos_left h2 hx,
    mul_lt_mul_of_pos_left h3 hx1, mul_pos (sub_pos.2 hxz) h4]

/-- `Ψ₁` through logarithms of its hyperbolic factors, for `σ > 0`. -/
private theorem maruyamaBelow_eq_exp {σ z : ℝ} (hσ : 0 < σ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    maruyamaBelow σ z = 2 / (z * (1 - z)) * exp (log (sinh (σ * z)) +
      log (sinh (σ * (1 - z))) - log (sinh (σ * 1)) - log σ) := by
  have hz1 := sub_pos.2 hz.2
  rw [maruyamaBelow_eq_sinh hσ.ne' hz, exp_sub, exp_sub, exp_add,
    exp_log (sinh_pos_iff.2 (mul_pos hσ hz.1)), exp_log (sinh_pos_iff.2 (mul_pos hσ hz1)),
    exp_log (sinh_pos_iff.2 (by simpa using hσ)), exp_log hσ, mul_one]
  have := (sinh_pos_iff.2 hσ).ne'
  field_simp

/-- `Ψ₂` through logarithms of its hyperbolic factors, for `σ > 0`. -/
private theorem maruyamaAbove_eq_exp {σ x z : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hxz : x < z)
    (hz : z < 1) :
    maruyamaAbove σ x z = 2 / (z * (1 - z)) * exp (2 * log (sinh (σ * (1 - z))) +
      log (sinh (σ * x)) - log σ - log (sinh (σ * 1)) - log (sinh (σ * (1 - x)))) := by
  have hz1 := sub_pos.2 hz
  have hx1 := sub_pos.2 (hxz.trans hz)
  rw [maruyamaAbove_eq_sinh hσ.ne' ⟨hx, hxz.trans hz⟩ ⟨hx.trans hxz, hz⟩, exp_sub, exp_sub,
    exp_sub, exp_add, show (2 : ℝ) * log (sinh (σ * (1 - z))) = log (sinh (σ * (1 - z)) ^ 2) by
      rw [log_pow]; norm_num, exp_log (pow_pos (sinh_pos_iff.2 (mul_pos hσ hz1)) 2),
    exp_log (sinh_pos_iff.2 (mul_pos hσ hx)), exp_log hσ,
    exp_log (sinh_pos_iff.2 (by simpa using hσ)), exp_log (sinh_pos_iff.2 (mul_pos hσ hx1)),
    mul_one]
  have := (sinh_pos_iff.2 hσ).ne'
  have := (sinh_pos_iff.2 (mul_pos hσ hx1)).ne'
  have := (hx.trans hxz).ne'
  field_simp

/-- **Stronger selection, smaller `Ψ₁`.** For `0 ≤ σ < τ` and `z ∈ (0, 1)`,
`Ψ₁` at `τ` is strictly below `Ψ₁` at `σ`. -/
theorem maruyamaBelow_lt_of_lt {σ τ z : ℝ} (hσ : 0 ≤ σ) (hστ : σ < τ)
    (hz : z ∈ Ioo (0 : ℝ) 1) : maruyamaBelow τ z < maruyamaBelow σ z := by
  rcases hσ.eq_or_lt with rfl | hσ
  · exact maruyamaBelow_lt hστ.ne' hz
  have hτ := hσ.trans hστ
  rw [maruyamaBelow_eq_exp hσ hz, maruyamaBelow_eq_exp hτ hz]
  have := sub_pos.2 hz.2
  have := hz.1
  exact mul_lt_mul_of_pos_left (exp_lt_exp.2 (strictAntiOn_log_below hz hσ hτ hστ))
    (by positivity)

/-- **Stronger selection, smaller `Ψ₂`.** For `0 ≤ σ < τ` and `0 < x < z < 1`,
`Ψ₂` at `τ` is strictly below `Ψ₂` at `σ`. -/
theorem maruyamaAbove_lt_of_lt {σ τ x z : ℝ} (hσ : 0 ≤ σ) (hστ : σ < τ) (hx : 0 < x)
    (hxz : x < z) (hz : z < 1) : maruyamaAbove τ x z < maruyamaAbove σ x z := by
  rcases hσ.eq_or_lt with rfl | hσ
  · exact maruyamaAbove_lt hστ.ne' hx hxz hz
  have hτ := hσ.trans hστ
  rw [maruyamaAbove_eq_exp hσ hx hxz hz, maruyamaAbove_eq_exp hτ hx hxz hz]
  have := sub_pos.2 hz
  have := hx.trans hxz
  exact mul_lt_mul_of_pos_left
    (exp_lt_exp.2 (strictAntiOn_log_above hx hxz hz hσ hτ hστ)) (by positivity)

/-- **Stronger selection, younger alleles**: at a fixed frequency `x ∈ (0, 1)`, the mean age is
strictly decreasing in `σ ≥ 0`. Kiezun et al. (2013, Figure 1b) show this numerically from the
closed forms; here it is proved. -/
theorem meanAge_lt_meanAge_of_lt {σ τ x : ℝ} (hσ : 0 ≤ σ) (hστ : σ < τ)
    (hx : x ∈ Ioo (0 : ℝ) 1) : meanAge τ x < meanAge σ x := by
  have hbσ := intervalIntegrable_maruyamaBelow σ (Ioo_subset_Icc_self hx)
  have hbτ := intervalIntegrable_maruyamaBelow τ (Ioo_subset_Icc_self hx)
  have haσ := intervalIntegrable_maruyamaAbove σ hx
  have haτ := intervalIntegrable_maruyamaAbove τ hx
  have I1 := intervalIntegral.intervalIntegral_pos_of_pos_on (hbσ.sub hbτ)
    (fun z hz => sub_pos.2 (maruyamaBelow_lt_of_lt hσ hστ ⟨hz.1, hz.2.trans hx.2⟩)) hx.1
  have I2 := intervalIntegral.intervalIntegral_pos_of_pos_on (haσ.sub haτ)
    (fun z hz => sub_pos.2 (maruyamaAbove_lt_of_lt hσ hστ hx.1 hz.1 hz.2)) hx.2
  rw [intervalIntegral.integral_sub hbσ hbτ] at I1
  rw [intervalIntegral.integral_sub haσ haτ] at I2
  unfold meanAge
  linarith

/-- **Stronger selection, younger alleles**, for either sign of selection: if `|σ| < |τ|` then
an allele at frequency `x ∈ (0, 1)` under selection `τ` is on average strictly younger than one
under selection `σ`. -/
theorem meanAge_lt_meanAge_of_abs_lt {σ τ x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (h : |σ| < |τ|) :
    meanAge τ x < meanAge σ x := by
  have habs : ∀ ρ, meanAge |ρ| x = meanAge ρ x := fun ρ => by
    rcases abs_choice ρ with h | h <;> rw [h]
    exact meanAge_neg ρ hx
  rw [← habs σ, ← habs τ]
  exact meanAge_lt_meanAge_of_lt (abs_nonneg σ) h hx

section Tonelli

open scoped ENNReal

/-- `∫₀^∞ t f(t) dt = ∫₀^∞ ∫₀^∞ f(s + r) dr ds` in `ℝ≥0∞` (Tonelli). -/
private theorem weighted_time_integral (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t * f t =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ r in Ioi (0 : ℝ), f (s + r) := by
  classical
  have hm : Measurable (fun q : ℝ × ℝ =>
      (Iio q.1).indicator (fun _ => f q.1) q.2) := by
    change Measurable ({q : ℝ × ℝ | q.2 < q.1}.indicator (fun q => f q.1))
    exact (hf.comp measurable_fst).indicator (measurableSet_lt measurable_snd measurable_fst)
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        (Iio t).indicator (fun _ => f t) s := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [lintegral_indicator measurableSet_Iio, setLIntegral_const,
        Measure.restrict_apply measurableSet_Iio]
      have hi : Iio t ∩ Ioi (0 : ℝ) = Ioo 0 t := by
        ext s
        simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
        exact and_comm
      rw [hi, Real.volume_Ioo, sub_zero, mul_comm]
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ),
        (Iio t).indicator (fun _ => f t) s :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi s, f t := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      dsimp only
      have he : (fun t => (Iio t).indicator (fun _ => f t) s) =
          (Ioi s).indicator f := by
        funext t
        simp only [indicator, mem_Iio, mem_Ioi]
      rw [he, lintegral_indicator measurableSet_Ioi,
        Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hs.le)]
    _ = _ := by
      apply lintegral_congr
      intro s
      have he : (fun r : ℝ => s + r) ⁻¹' Ioi s = Ioi 0 := by
        ext r
        simp
      simpa only [he] using
        ((measurePreserving_add_left (volume : Measure ℝ) s).setLIntegral_comp_preimage
          (s := Ioi s) measurableSet_Ioi hf).symm

/-- **Mean time as a sum of sojourn times** (the identity behind Maruyama and Kimura 1975). For
a jointly measurable family of transition densities `w p x t ≥ 0` on `(0, 1)` satisfying the
Chapman–Kolmogorov equation for positive times,
`∫₀^∞ t w(p, x, t) dt = ∫₀¹ Ψ(p, y) Ψ(y, x) dy` with `Ψ(p, x) = ∫₀^∞ w(p, x, t) dt`, in
`ℝ≥0∞`. Dividing by `Ψ(p, x)` reads `∫₀¹ Ψ(p, y) Ψ(y, x) / Ψ(p, x) dy` (the integral of
`ageDensity` when `Ψ = selectionGreen σ`) as a mean time. The statement is abstract: no
diffusion is constructed, and `w` is not required to be the Wright–Fisher transition density. -/
theorem lintegral_mul_eq_lintegral_sojourn_mul (w : ℝ → ℝ → ℝ → ℝ≥0∞)
    (hw : Measurable fun q : ℝ × ℝ × ℝ => w q.1 q.2.1 q.2.2)
    (hck : ∀ p x s t, 0 < s → 0 < t →
      w p x (s + t) = ∫⁻ y in Ioo (0 : ℝ) 1, w p y s * w y x t)
    (p x : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t * w p x t =
      ∫⁻ y in Ioo (0 : ℝ) 1, (∫⁻ s in Ioi (0 : ℝ), w p y s) * ∫⁻ t in Ioi (0 : ℝ), w y x t := by
  have hsec (a b : ℝ) : Measurable (w a b) :=
    hw.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hm (s : ℝ) : Measurable (fun q : ℝ × ℝ => w p q.2 s * w q.2 x q.1) :=
    (hw.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_const))).mul
      (hw.comp (measurable_snd.prodMk (measurable_const.prodMk measurable_fst)))
  have hn : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      w p q.1.2 q.1.1 * w q.1.2 x q.2) :=
    (hw.comp (measurable_const.prodMk
      (measurable_fst.snd.prodMk measurable_fst.fst))).mul
      (hw.comp (measurable_fst.snd.prodMk (measurable_const.prodMk measurable_snd)))
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), w p x (s + t) :=
      weighted_time_integral (w p x) (hsec p x)
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ),
        ∫⁻ y in Ioo (0 : ℝ) 1, w p y s * w y x t := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hck p x s t hs ht
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ y in Ioo (0 : ℝ) 1,
        ∫⁻ t in Ioi (0 : ℝ), w p y s * w y x t := by
      apply lintegral_congr
      intro s
      exact lintegral_lintegral_swap (hm s).aemeasurable
    _ = ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ s in Ioi (0 : ℝ),
        ∫⁻ t in Ioi (0 : ℝ), w p y s * w y x t :=
      lintegral_lintegral_swap hn.lintegral_prod_right'.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      exact lintegral_lintegral_mul (hsec p y).aemeasurable (hsec y x).aemeasurable

end Tonelli

end MathlibExt.Biology.PopulationGenetics.Diffusion
