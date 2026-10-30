/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Probability.Distributions.Binomial
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The Wright–Fisher diffusion: ODE facts behind diffusion methods

The Wright–Fisher diffusion approximates the frequency `x ∈ [0, 1]` of an allele in a diploid
population of size `N` (so `2N` gene copies). Time is measured in units of `2N` generations.
With genic selection of strength `s` per generation, the scaled selection coefficient is
`σ = 2 N s` (so `2σ = 4 N s`, Kimura's `4Ns`), and the diffusion has infinitesimal variance
`x (1 - x)` and drift `σ x (1 - x)`. Its backward generator is

  `(L_σ u)(x) = x (1 - x) / 2 · u''(x) + σ x (1 - x) · u'(x)`.

The stochastic differential equation itself is **not** formalized here (Mathlib has no Itô
calculus). This file proves the ordinary-differential-equation facts that diffusion methods
use, stated for the backward generator `generator σ` (and, for Wright's stationary density, for
the stationary forward / Fokker–Planck equation):

* Kimura's fixation probability `u(x) = (1 - e^{-2σx}) / (1 - e^{-2σ})` (neutral case `u = x`)
  solves `L_σ u = 0` with `u(0) = 0`, `u(1) = 1`, and it is the *unique* such solution among
  functions continuous on `[0, 1]` and twice differentiable on `(0, 1)`.
* Kimura–Ohta neutral mean absorption time `T(x) = -2 (x log x + (1 - x) log (1 - x))`
  (in units of `2N` generations; in generations it is `-4N (x ln x + (1 - x) ln (1 - x))`)
  solves `L_0 T = -1`, `T(0) = T(1) = 0`.
* Heterozygosity `H(x) = 2x(1 - x)` is an eigenfunction: `L_0 H = -H`, so `E[H_t] = H_0 e^{-t}`
  (matching the per-generation factor `1 - 1/(2N)`).
* Moment duality with Kingman's coalescent at generator level:
  `L_0 (y ↦ y ^ n)(x) = C(n, 2) (x ^ (n - 1) - x ^ n)`.
* Wright's stationary density with two-way mutation (scaled rates `α`, `β`, drift
  `α (1 - x) - β x`), `π(x) = x ^ (2α - 1) (1 - x) ^ (2β - 1)`, satisfies the zero-flux
  equation `½ (x (1 - x) π)' = (α (1 - x) - β x) π` on `(0, 1)`.

## Main results

* `generator`, `kimuraFixation`, `meanAbsorptionTime`, `wrightDensity`: the objects above.
* `kimuraFixation_zero_right`, `kimuraFixation_one_right`, `kimuraFixation_neutral`.
* `generator_kimuraFixation`: `L_σ u = 0` for Kimura's formula.
* `eq_kimuraFixation_of_generator_eq_zero`, `eq_kimuraFixation_of_contDiffOn`: uniqueness of
  the solution of the fixation boundary-value problem.
* `kimuraFixation_mem_Icc`, `lt_kimuraFixation`: `0 ≤ u ≤ 1`, and `x < u(x)` when `σ > 0`.
* `generator_meanAbsorptionTime`, `meanAbsorptionTime_zero`, `meanAbsorptionTime_one`.
* `generator_heterozygosity`, `generator_pow`.
* `deriv_flux_wrightDensity`, `integral_wrightDensity`: zero-flux stationarity of Wright's
  density and its normalization by the Beta function `B(2α, 2β)`.
* `integral_binomial_heterozygosity`: the discrete counterpart of heterozygosity decay,
  `E[2p'(1 - p')] = (1 - 1/M) · 2x(1 - x)` for one Wright–Fisher generation.

## References

* M. Kimura, *On the probability of fixation of mutant genes in a population*,
  Genetics 47 (1962) 713–719.
* M. Kimura and T. Ohta, *The average number of generations until fixation of a mutant gene in
  a finite population*, Genetics 61 (1969) 763–771.
* S. Wright, *Evolution in Mendelian populations*, Genetics 16 (1931) 97–159.
* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), ch. 4–5.
* R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), ch. 7.
* S. N. Ethier and T. G. Kurtz, *Markov Processes*, Wiley (1986), ch. 10.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- The backward generator of the Wright–Fisher diffusion with genic selection, time in units
of `2N` generations and scaled selection coefficient `σ = 2Ns`:
`(L_σ u)(x) = x (1 - x) / 2 · u''(x) + σ x (1 - x) · u'(x)`. -/
noncomputable def generator (σ : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * (1 - x) / 2 * deriv (deriv u) x + σ * x * (1 - x) * deriv u x

/-- Kimura's fixation probability of an allele at initial frequency `x` with scaled selection
coefficient `σ = 2Ns`: `(1 - e^{-2σx}) / (1 - e^{-2σ})`, and `x` in the neutral case. -/
noncomputable def kimuraFixation (σ x : ℝ) : ℝ :=
  if σ = 0 then x else (1 - exp (-2 * σ * x)) / (1 - exp (-2 * σ))

/-- Kimura–Ohta mean time to absorption (loss or fixation) of a neutral allele at frequency `x`,
in units of `2N` generations: `-2 (x log x + (1 - x) log (1 - x))`. In generations this is
`-4N (x ln x + (1 - x) ln (1 - x))`. -/
noncomputable def meanAbsorptionTime (x : ℝ) : ℝ :=
  -2 * (x * log x + (1 - x) * log (1 - x))

/-- Wright's (unnormalized) stationary density of the Wright–Fisher diffusion with scaled
mutation rates `α` (towards the allele) and `β` (away from it):
`x ^ (2α - 1) (1 - x) ^ (2β - 1)` (real powers). -/
noncomputable def wrightDensity (α β x : ℝ) : ℝ :=
  x ^ (2 * α - 1) * (1 - x) ^ (2 * β - 1)

/-- The constant `K σ` such that `(kimuraFixation σ)' x = K σ · e^{-2σx}`:
`1` if `σ = 0`, and `2σ / (1 - e^{-2σ})` otherwise. -/
noncomputable def kimuraSlope (σ : ℝ) : ℝ :=
  if σ = 0 then 1 else 2 * σ / (1 - exp (-2 * σ))

/-- For `σ ≠ 0` the denominator `1 - e^{-2σ}` of Kimura's formula does not vanish. -/
theorem one_sub_exp_ne_zero {σ : ℝ} (hσ : σ ≠ 0) : 1 - exp (-2 * σ) ≠ 0 := by
  intro h
  have h' : exp (-2 * σ) = 1 := by linarith
  rw [exp_eq_one_iff] at h'
  exact hσ (by linarith)

/-- An allele that is absent is never fixed. -/
@[simp]
theorem kimuraFixation_zero_right (σ : ℝ) : kimuraFixation σ 0 = 0 := by
  simp [kimuraFixation]

/-- An allele that is already fixed stays fixed. -/
@[simp]
theorem kimuraFixation_one_right (σ : ℝ) : kimuraFixation σ 1 = 1 := by
  unfold kimuraFixation
  split_ifs with h
  · rfl
  · rw [mul_one, div_self (one_sub_exp_ne_zero h)]

/-- Neutral case: the fixation probability equals the initial frequency. -/
@[simp]
theorem kimuraFixation_neutral (x : ℝ) : kimuraFixation 0 x = x := by
  simp [kimuraFixation]

/-- The slope constant of Kimura's formula never vanishes. -/
theorem kimuraSlope_ne_zero (σ : ℝ) : kimuraSlope σ ≠ 0 := by
  unfold kimuraSlope
  split_ifs with h
  · exact one_ne_zero
  · exact div_ne_zero (mul_ne_zero two_ne_zero h) (one_sub_exp_ne_zero h)

private theorem hasDerivAt_exp_mul (c x : ℝ) :
    HasDerivAt (fun y => exp (c * y)) (exp (c * x) * c) x := by
  simpa only [mul_one] using ((hasDerivAt_id' x).const_mul c).exp

/-- The derivative of Kimura's fixation probability: `u'(x) = K σ · e^{-2σx}`. -/
theorem hasDerivAt_kimuraFixation (σ x : ℝ) :
    HasDerivAt (kimuraFixation σ) (kimuraSlope σ * exp (-2 * σ * x)) x := by
  by_cases h : σ = 0
  · subst h
    have hk : kimuraFixation 0 = id := funext kimuraFixation_neutral
    rw [hk]
    simpa [kimuraSlope] using hasDerivAt_id x
  · have hk : kimuraFixation σ = fun y => (1 - exp (-2 * σ * y)) / (1 - exp (-2 * σ)) :=
      funext fun y => by simp [kimuraFixation, h]
    rw [hk]
    convert ((hasDerivAt_exp_mul (-2 * σ) x).const_sub 1).div_const (1 - exp (-2 * σ)) using 1
    simp only [kimuraSlope, h, ↓reduceIte]
    ring

/-- Kimura's fixation probability is continuous in the initial frequency. -/
theorem continuous_kimuraFixation (σ : ℝ) : Continuous (kimuraFixation σ) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_kimuraFixation σ x).continuousAt

/-- The derivative of Kimura's fixation probability, as a function. -/
theorem deriv_kimuraFixation (σ : ℝ) :
    deriv (kimuraFixation σ) = fun y => kimuraSlope σ * exp (-2 * σ * y) :=
  funext fun y => (hasDerivAt_kimuraFixation σ y).deriv

/-- **Kimura (1962).** The fixation probability solves the backward equation
`x (1 - x) / 2 · u'' + σ x (1 - x) · u' = 0` (everywhere). -/
theorem generator_kimuraFixation (σ x : ℝ) : generator σ (kimuraFixation σ) x = 0 := by
  rw [generator, deriv_kimuraFixation, ((hasDerivAt_exp_mul (-2 * σ) x).const_mul _).deriv]
  ring

/-- A function continuous on `[a, b]` with zero derivative on `(a, b)` is constant on `[a, b]`. -/
private theorem eq_left_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : ∀ x ∈ Icc a b, f x = f a := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · rfl
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hax (hf.mono (Icc_subset_Icc_right hx.2))
    fun y hy => (hd y ⟨hy.1, hy.2.trans_le hx.2⟩).differentiableAt.differentiableWithinAt
  rw [(hd c ⟨hc.1, hc.2.trans_le hx.2⟩).deriv, eq_comm, div_eq_zero_iff] at hcd
  rcases hcd with h | h <;> linarith

/-- **Uniqueness of the fixation probability (Kimura 1962).** If `u` is continuous on `[0, 1]`,
differentiable on `(0, 1)` with derivative `u'` differentiable on `(0, 1)`, solves the backward
equation `L_σ u = 0` on `(0, 1)`, and satisfies `u 0 = 0`, `u 1 = 1`, then `u` is Kimura's
fixation probability on `[0, 1]`. -/
theorem eq_kimuraFixation_of_generator_eq_zero {σ : ℝ} {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Icc 0 1)) (hdiff : DifferentiableOn ℝ u (Ioo 0 1))
    (hdiff' : DifferentiableOn ℝ (deriv u) (Ioo 0 1))
    (hgen : ∀ x ∈ Ioo (0 : ℝ) 1, generator σ u x = 0) (h0 : u 0 = 0) (h1 : u 1 = 1) :
    ∀ x ∈ Icc (0 : ℝ) 1, u x = kimuraFixation σ x := by
  -- On `(0, 1)` the backward equation reads `u'' + 2σ u' = 0`.
  have hode : ∀ x ∈ Ioo (0 : ℝ) 1, deriv (deriv u) x + 2 * σ * deriv u x = 0 := by
    intro x hx
    have hpos : 0 < x * (1 - x) / 2 := by
      have := hx.1; have := sub_pos.2 hx.2; positivity
    have h' : x * (1 - x) / 2 * (deriv (deriv u) x + 2 * σ * deriv u x) = 0 := by
      rw [← hgen x hx, generator]; ring
    exact (mul_eq_zero.1 h').resolve_left hpos.ne'
  -- Hence `g y = e^{2σy} u'(y)` has zero derivative on `(0, 1)`.
  set g : ℝ → ℝ := fun y => exp (2 * σ * y) * deriv u y
  have hgd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g 0 x := by
    intro x hx
    have hu' : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
      (hdiff'.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
    convert (hasDerivAt_exp_mul (2 * σ) x).mul hu' using 1
    linear_combination -(exp (2 * σ * x)) * hode x hx
  -- So `g` is constant on `(0, 1)`.
  have hgc : ∀ x ∈ Ioo (0 : ℝ) 1, g x = g (1 / 2) := by
    intro x hx
    have hsub : Icc (min x (1 / 2)) (max x (1 / 2)) ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      constructor
      · exact lt_of_lt_of_le (lt_min hx.1 (by norm_num)) hy.1
      · exact lt_of_le_of_lt hy.2 (max_lt hx.2 (by norm_num))
    have hc : ContinuousOn g (Icc (min x (1 / 2)) (max x (1 / 2))) := fun y hy =>
      (hgd y (hsub hy)).continuousAt.continuousWithinAt
    have hd : ∀ y ∈ Ioo (min x (1 / 2)) (max x (1 / 2)), HasDerivAt g 0 y := fun y hy =>
      hgd y (hsub (Ioo_subset_Icc_self hy))
    rw [eq_left_of_hasDerivAt_zero hc hd x ⟨min_le_left _ _, le_max_left _ _⟩,
      eq_left_of_hasDerivAt_zero hc hd (1 / 2) ⟨min_le_right _ _, le_max_right _ _⟩]
  -- Therefore `u' = m · (kimuraFixation σ)'` on `(0, 1)` with `m = g(1/2) / K σ`.
  set m : ℝ := g (1 / 2) / kimuraSlope σ with hm
  have hu' : ∀ x ∈ Ioo (0 : ℝ) 1, deriv u x = m * (kimuraSlope σ * exp (-2 * σ * x)) := by
    intro x hx
    have hx' : exp (2 * σ * x) * deriv u x = g (1 / 2) := hgc x hx
    have he : exp (-2 * σ * x) * exp (2 * σ * x) = 1 := by
      rw [← exp_add, show -2 * σ * x + 2 * σ * x = 0 by ring, exp_zero]
    calc deriv u x = exp (-2 * σ * x) * (exp (2 * σ * x) * deriv u x) := by
          rw [← mul_assoc, he, one_mul]
      _ = m * (kimuraSlope σ * exp (-2 * σ * x)) := by
          have hK := kimuraSlope_ne_zero σ
          rw [hx', hm]
          field_simp
  -- `h = u - m · kimuraFixation σ` is constant on `[0, 1]`, equal to `h 0 = 0`.
  have hh : ∀ x ∈ Icc (0 : ℝ) 1, u x - m * kimuraFixation σ x = 0 := by
    have hc : ContinuousOn (fun y => u y - m * kimuraFixation σ y) (Icc 0 1) :=
      hcont.sub ((continuous_kimuraFixation σ).continuousOn.const_smul m)
    have hd : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y => u y - m * kimuraFixation σ y) 0 y := by
      intro y hy
      have hu : HasDerivAt u (deriv u y) y :=
        (hdiff.differentiableAt (isOpen_Ioo.mem_nhds hy)).hasDerivAt
      convert hu.sub ((hasDerivAt_kimuraFixation σ y).const_mul m) using 1
      rw [hu' y hy, sub_self]
    intro x hx
    rw [eq_left_of_hasDerivAt_zero hc hd x hx, h0, kimuraFixation_zero_right, mul_zero, sub_self]
  -- The boundary value at `1` forces `m = 1`.
  have hm1 : m = 1 := by
    have := hh 1 ⟨zero_le_one, le_rfl⟩
    rw [h1, kimuraFixation_one_right, mul_one] at this
    linarith
  intro x hx
  have := hh x hx
  rw [hm1, one_mul] at this
  linarith

/-- **Uniqueness of the fixation probability**, `C²` form: a function continuous on `[0, 1]`,
`C²` on `(0, 1)`, solving `L_σ u = 0` on `(0, 1)` with `u 0 = 0`, `u 1 = 1` equals Kimura's
fixation probability on `[0, 1]`. -/
theorem eq_kimuraFixation_of_contDiffOn {σ : ℝ} {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Icc 0 1)) (hu : ContDiffOn ℝ 2 u (Ioo 0 1))
    (hgen : ∀ x ∈ Ioo (0 : ℝ) 1, generator σ u x = 0) (h0 : u 0 = 0) (h1 : u 1 = 1) :
    ∀ x ∈ Icc (0 : ℝ) 1, u x = kimuraFixation σ x := by
  have h := (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).1 hu
  exact eq_kimuraFixation_of_generator_eq_zero hcont h.1 (h.2.2.differentiableOn one_ne_zero)
    hgen h0 h1

/-- Kimura's fixation probability is a probability on `[0, 1]`. -/
theorem kimuraFixation_mem_Icc (σ : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    kimuraFixation σ x ∈ Icc (0 : ℝ) 1 := by
  unfold kimuraFixation
  split_ifs with h
  · exact hx
  rcases lt_or_gt_of_ne h with hσ | hσ
  · -- `σ < 0`: numerator and denominator are both nonpositive.
    have hden : 1 - exp (-2 * σ) < 0 := by
      have : 1 < exp (-2 * σ) := one_lt_exp_iff.2 (by linarith)
      linarith
    have hnum : 1 - exp (-2 * σ * x) ≤ 0 := by
      have : 1 ≤ exp (-2 * σ * x) := one_le_exp (by nlinarith [hx.1])
      linarith
    have hle : exp (-2 * σ * x) ≤ exp (-2 * σ) := exp_le_exp.2 (by nlinarith [hx.2])
    rw [← neg_div_neg_eq]
    exact ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩
  · -- `σ > 0`: numerator and denominator are both nonnegative.
    have hden : 0 < 1 - exp (-2 * σ) := by
      have : exp (-2 * σ) < 1 := exp_lt_one_iff.2 (by linarith)
      linarith
    have hnum : 0 ≤ 1 - exp (-2 * σ * x) := by
      have : exp (-2 * σ * x) ≤ 1 := exp_le_one_iff.2 (by nlinarith [hx.1])
      linarith
    have hle : exp (-2 * σ) ≤ exp (-2 * σ * x) := exp_le_exp.2 (by nlinarith [hx.2])
    exact ⟨div_nonneg hnum hden.le, (div_le_one hden).2 (by linarith)⟩

/-- Advantageous alleles (`σ > 0`) are fixed with probability strictly larger than their
initial frequency `x ∈ (0, 1)`. -/
theorem lt_kimuraFixation {σ x : ℝ} (hσ : 0 < σ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    x < kimuraFixation σ x := by
  have hden : 0 < 1 - exp (-2 * σ) := by
    have : exp (-2 * σ) < 1 := exp_lt_one_iff.2 (by linarith)
    linarith
  simp only [kimuraFixation, hσ.ne', ↓reduceIte]
  rw [lt_div_iff₀ hden]
  have hconv := strictConvexOn_exp.2 (mem_univ 0) (mem_univ (-2 * σ))
    (by linarith : (0 : ℝ) ≠ -2 * σ) (sub_pos.2 hx.2) hx.1 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at hconv
  rw [show x * (-2 * σ) = -2 * σ * x by ring] at hconv
  linarith

/-- The neutral mean absorption time vanishes at `x = 0`. -/
@[simp]
theorem meanAbsorptionTime_zero : meanAbsorptionTime 0 = 0 := by
  simp [meanAbsorptionTime]

/-- The neutral mean absorption time vanishes at `x = 1`. -/
@[simp]
theorem meanAbsorptionTime_one : meanAbsorptionTime 1 = 0 := by
  simp [meanAbsorptionTime]

private theorem hasDerivAt_one_sub (x : ℝ) : HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
  simpa using (hasDerivAt_id' x).const_sub 1

/-- On `(0, 1)`, `T'(x) = -2 (log x - log (1 - x))`. -/
theorem hasDerivAt_meanAbsorptionTime {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt meanAbsorptionTime (-2 * (log x - log (1 - x))) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  have h1 : HasDerivAt (fun y => y * log y) (1 * log x + x * x⁻¹) x :=
    (hasDerivAt_id' x).mul (hasDerivAt_log hx0)
  have h3 : HasDerivAt (fun y => (1 - y) * log (1 - y))
      (-1 * log (1 - x) + (1 - x) * (-1 / (1 - x))) x :=
    (hasDerivAt_one_sub x).mul ((hasDerivAt_one_sub x).log hx1)
  have h : HasDerivAt meanAbsorptionTime
      (-2 * (1 * log x + x * x⁻¹ + (-1 * log (1 - x) + (1 - x) * (-1 / (1 - x))))) x :=
    (h1.add h3).const_mul (-2)
  convert h using 1
  field_simp
  ring

/-- **Kimura–Ohta (1969).** The neutral mean absorption time solves `L_0 T = -1` on `(0, 1)`. -/
theorem generator_meanAbsorptionTime {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    generator 0 meanAbsorptionTime x = -1 := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  have hD : deriv meanAbsorptionTime =ᶠ[𝓝 x] fun y => -2 * (log y - log (1 - y)) :=
    eventually_of_mem (isOpen_Ioo.mem_nhds hx) fun y hy => (hasDerivAt_meanAbsorptionTime hy).deriv
  have h4 : HasDerivAt (fun y => -2 * (log y - log (1 - y))) (-2 * (x⁻¹ - -1 / (1 - x))) x :=
    ((hasDerivAt_log hx0).sub ((hasDerivAt_one_sub x).log hx1)).const_mul (-2)
  rw [generator, hD.deriv_eq, h4.deriv]
  field_simp
  ring

/-- **Decay of heterozygosity.** `H(x) = 2x(1 - x)` is an eigenfunction of the neutral
generator with eigenvalue `-1`, so `E[H_t] = H_0 e^{-t}` (time in units of `2N` generations). -/
theorem generator_heterozygosity (x : ℝ) :
    generator 0 (fun y => 2 * y * (1 - y)) x = -(2 * x * (1 - x)) := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y => 2 * y * (1 - y)) (2 - 4 * y) y := fun y => by
    convert ((hasDerivAt_id' y).const_mul 2).mul (hasDerivAt_one_sub y) using 1
    ring
  have hD : deriv (fun y : ℝ => 2 * y * (1 - y)) = fun y => 2 - 4 * y :=
    funext fun y => (hd y).deriv
  have h2 : HasDerivAt (fun y : ℝ => 2 - 4 * y) (-4) x := by
    simpa using ((hasDerivAt_id' x).const_mul 4).const_sub 2
  rw [generator, hD, h2.deriv]
  ring

/-- **Moment duality with Kingman's coalescent** at generator level: the neutral generator maps
`y ↦ y ^ n` to `C(n, 2) (x ^ (n - 1) - x ^ n)`, which is the generator of the block-counting
process (jumps `n → n - 1` at rate `C(n, 2)`) applied to `n ↦ x ^ n`. -/
theorem generator_pow (n : ℕ) (x : ℝ) :
    generator 0 (fun y => y ^ n) x = (n.choose 2 : ℝ) * (x ^ (n - 1) - x ^ n) := by
  have hD : deriv (fun y : ℝ => y ^ n) = fun y => (n : ℝ) * y ^ (n - 1) :=
    funext fun y => (hasDerivAt_pow n y).deriv
  rw [generator, hD, ((hasDerivAt_pow (n - 1) x).const_mul (n : ℝ)).deriv, Nat.cast_choose_two]
  rcases n with _ | _ | k
  · simp
  · simp
  · simp only [Nat.add_sub_cancel, show k + 1 + 1 - 1 = k + 1 by omega]
    push_cast
    ring

/-- **Wright's stationary density (zero-flux form).** On `(0, 1)`, with infinitesimal variance
`a(x) = x (1 - x)` and mutation drift `b(x) = α (1 - x) - β x`, Wright's density
`π(x) = x ^ (2α - 1) (1 - x) ^ (2β - 1)` satisfies `(a π)' = 2 b π`, i.e. the stationary
forward (Fokker–Planck) equation `½ (a π)' - b π = 0` with zero probability flux. -/
theorem deriv_flux_wrightDensity (α β : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (fun y => y * (1 - y) * wrightDensity α β y) x =
      2 * (α * (1 - x) - β * x) * wrightDensity α β x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  have hA : HasDerivAt (fun z : ℝ => z ^ (2 * α - 1)) ((2 * α - 1) * x ^ (2 * α - 1 - 1)) x :=
    hasDerivAt_rpow_const (Or.inl hx0)
  have hB := (hasDerivAt_one_sub x).rpow_const (p := 2 * β - 1) (Or.inl hx1)
  have h : HasDerivAt (fun y => y * (1 - y) * wrightDensity α β y)
      ((1 * (1 - x) + x * -1) * (x ^ (2 * α - 1) * (1 - x) ^ (2 * β - 1)) +
        x * (1 - x) * ((2 * α - 1) * x ^ (2 * α - 1 - 1) * (1 - x) ^ (2 * β - 1) +
          x ^ (2 * α - 1) * (-1 * (2 * β - 1) * (1 - x) ^ (2 * β - 1 - 1)))) x :=
    ((hasDerivAt_id' x).mul (hasDerivAt_one_sub x)).mul (hA.mul hB)
  rw [h.deriv, rpow_sub_one hx0 (2 * α - 1), rpow_sub_one hx1 (2 * β - 1), wrightDensity]
  field_simp
  ring

/-- **Normalization of Wright's density.** For `α, β > 0` the stationary density integrates to
the Beta function `B(2α, 2β) = Γ(2α) Γ(2β) / Γ(2α + 2β)`, so
`wrightDensity α β x / B(2α, 2β)` is the Beta`(2α, 2β)` probability density on `(0, 1)`. -/
theorem integral_wrightDensity {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x in (0 : ℝ)..1, wrightDensity α β x =
      Gamma (2 * α) * Gamma (2 * β) / Gamma (2 * α + 2 * β) := by
  apply Complex.ofReal_injective
  have h1 : ((∫ x in (0 : ℝ)..1, wrightDensity α β x : ℝ) : ℂ) =
      Complex.betaIntegral (2 * α) (2 * β) := by
    rw [← intervalIntegral.integral_ofReal, Complex.betaIntegral]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    simp only [wrightDensity]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1, Complex.ofReal_cpow (sub_nonneg.2 hx.2)]
    push_cast
    rfl
  have hs : 0 < ((2 * α : ℝ) : ℂ).re := by simp; linarith
  have ht : 0 < ((2 * β : ℝ) : ℂ).re := by simp; linarith
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral hs ht
  have hne := Complex.Gamma_ne_zero_of_re_pos (s := ((2 * α : ℝ) : ℂ) + ((2 * β : ℝ) : ℂ))
    (by rw [Complex.add_re]; linarith)
  rw [h1]
  push_cast [← Complex.Gamma_ofReal]
  push_cast at hG hne
  rw [hG, mul_div_cancel_left₀ _ hne]

/-- For `α, β > 0` Wright's density has a finite, positive total mass on `(0, 1)`. -/
theorem integral_wrightDensity_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 < ∫ x in (0 : ℝ)..1, wrightDensity α β x := by
  rw [integral_wrightDensity hα hβ]
  exact div_pos (mul_pos (Gamma_pos_of_pos (by linarith)) (Gamma_pos_of_pos (by linarith)))
    (Gamma_pos_of_pos (by linarith))

/-- For `α, β > 0` Wright's density is integrable on `[0, 1]`. -/
theorem intervalIntegrable_wrightDensity {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IntervalIntegrable (wrightDensity α β) MeasureTheory.volume 0 1 := by
  by_contra h
  exact (integral_wrightDensity_pos hα hβ).ne' (intervalIntegral.integral_undef h)

private theorem eval_bernsteinPolynomial (M k : ℕ) (x : ℝ) :
    (bernsteinPolynomial ℝ M k).eval x = (M.choose k : ℝ) * x ^ k * (1 - x) ^ (M - k) := by
  simp [bernsteinPolynomial]

/-- **Heterozygosity decay in one Wright–Fisher generation.** If the number `X` of copies of an
allele among `M` gene copies (`M = 2N` for diploids) is `Binomial(M, x)`, then the new frequency
`p' = X / M` satisfies `E[2 p' (1 - p')] = (1 - 1/M) · 2x(1 - x)`. -/
theorem integral_binomial_heterozygosity (M : ℕ) (hM : M ≠ 0) (x : unitInterval) :
    ∫ k, 2 * ((k : ℝ) / M) * (1 - (k : ℝ) / M) ∂(ProbabilityTheory.binomial M x) =
      (1 - 1 / (M : ℝ)) * (2 * x * (1 - x)) := by
  set y : ℝ := (x : ℝ)
  set w : ℕ → ℝ := fun k => (M.choose k : ℝ) * y ^ k * (1 - y) ^ (M - k) with hw
  have S0 : ∑ k ∈ Finset.range (M + 1), w k = 1 := by
    have := congrArg (Polynomial.eval y) (bernsteinPolynomial.sum ℝ M)
    simpa [Polynomial.eval_finsetSum, eval_bernsteinPolynomial] using this
  have S1 : ∑ k ∈ Finset.range (M + 1), (k : ℝ) * w k = M * y := by
    have := congrArg (Polynomial.eval y) (bernsteinPolynomial.sum_smul ℝ M)
    simpa [Polynomial.eval_finsetSum, eval_bernsteinPolynomial, nsmul_eq_mul, mul_assoc, hw]
      using this
  have S2 : ∑ k ∈ Finset.range (M + 1), (M * y - k) ^ 2 * w k = M * y * (1 - y) := by
    have := congrArg (Polynomial.eval y) (bernsteinPolynomial.variance ℝ M)
    simpa [Polynomial.eval_finsetSum, eval_bernsteinPolynomial, nsmul_eq_mul, mul_assoc, hw]
      using this
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM
  rw [ProbabilityTheory.integral_binomial, ← Nat.range_succ_eq_Iic]
  simp only [smul_eq_mul]
  change ∑ k ∈ Finset.range (M + 1), w k * (2 * ((k : ℝ) / M) * (1 - (k : ℝ) / M)) = _
  calc ∑ k ∈ Finset.range (M + 1), w k * (2 * ((k : ℝ) / M) * (1 - (k : ℝ) / M))
      = ∑ k ∈ Finset.range (M + 1), (2 / M ^ 2 * M * ((k : ℝ) * w k)
          - 2 / M ^ 2 * ((M * y - k) ^ 2 * w k) + 2 / M ^ 2 * (M ^ 2 * y ^ 2) * w k
          - 2 / M ^ 2 * (2 * M * y) * ((k : ℝ) * w k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        field_simp
        ring
    _ = 2 / M ^ 2 * M * (M * y) - 2 / M ^ 2 * (M * y * (1 - y)) + 2 / M ^ 2 * (M ^ 2 * y ^ 2)
          - 2 / M ^ 2 * (2 * M * y) * (M * y) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, S0, S1, S2,
          mul_one]
    _ = (1 - 1 / (M : ℝ)) * (2 * y * (1 - y)) := by
        field_simp
        ring

end MathlibExt.Biology.PopulationGenetics.Diffusion
