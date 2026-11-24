/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.GeneralDiffusion
public import Domains.Biology.PopulationGenetics.Diffusion.Generator
public import Mathlib.Probability.Distributions.Beta

/-!
# Speed density and the canonical form of one-dimensional generators

For a one-dimensional diffusion generator `L f = (a/2) f'' + b f'` with scale
density `ψ = S'`, the speed density is `m = 2 / (a ψ)`, and the generator has
the canonical form `L f = (1/m) (f'/ψ)'`, i.e. `L = (d/dm) ∘ (d/dS)`. This
file defines the speed density and speed measure for the general regular
diffusion of `GeneralDiffusion`, proves the canonical form from the pointwise
identity driven by `ψ'/ψ = -2b/a`, and gives the explicit neutral and
selection–mutation densities `m(x) = e^{2αx} 2 x^{θ₁-1} (1-x)^{θ₂-1}` with
total mass `∫₀¹ m = 2 B(θ₁, θ₂)` in the mutation case. Boundary
classification from primitives of `m` and `ψ` is a separate development.

## Main results

* `speedDensity`, `speedMeasure`: speed density `2 / (a ψ)` and its measure.
* `diffusionGenerator_eq_of_hasDerivAt`: the generic canonical-form step from
  `ψ' = -(2b/a) ψ`.
* `diffusionGenerator_eq_one_div_speedDensity`: canonical form for regular
  diffusions.
* `speedDensity_neutral`, `selectionMutationSpeedDensity_eq`,
  `selectionMutationGenerator_eq_one_div_speedDensity`: explicit densities.
* `integral_mutationSpeedDensity`: total mass `2 B(θ₁, θ₂)`.

## References

* S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*,
  Academic Press, 1981, Chapter 15 (scale function and speed measure).
* W. J. Ewens, *Mathematical Population Genetics*, 2nd ed., Springer, 2004,
  Chapter 4.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

variable {b a : ℝ → ℝ}

/-- Speed density `m(x) = 2 / (a(x) ψ(x))` for scale density `ψ = scaleDensity b a`. With
`x / 0 = 0`, `m(x) = 0` where `a(x) = 0` (`ψ` is positive everywhere). The intended domain is
`x ∈ (0, 1)` for a regular diffusion, where `a > 0`. -/
noncomputable def speedDensity (b a : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 / (a x * scaleDensity b a x)

/-- Speed measure on the state space `(0, 1)`: Lebesgue measure restricted to `(0, 1)` with density
`speedDensity b a`, negative values of the density counting as `0` (the density is `max (m x) 0`): a
measurable set `A` gets the mass `∫⁻_{A ∩ (0, 1)} max (m x) 0 dx`, a lower integral. It is an
ordinary density measure when `m` is measurable, as for a regular diffusion; `b` and `a` are
otherwise unrestricted. Coefficient values outside `(0, 1)` do not affect it. It need not be
finite. -/
noncomputable def speedMeasure (b a : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioo 0 1)).withDensity (fun x => ENNReal.ofReal (speedDensity b a x))

/-- For a regular diffusion the speed density is positive on `(0, 1)`: there `a x > 0` and
`scaleDensity b a x > 0`. -/
theorem speedDensity_pos_of_isRegular (h : IsRegularDiffusion b a) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < speedDensity b a x :=
  div_pos two_pos (mul_pos (h.pos x hx) (scaleDensity_pos b a x))

/-- Canonical form step: for any `ψ` with `ψ x ≠ 0` and `ψ' = -(2b/a) ψ` at `x`, where `a x ≠ 0`,
and any `f` whose total derivative `f' = deriv f` (the derivative where it exists, `0` elsewhere) is
differentiable at `x`, `L f (x) = (a(x) ψ(x) / 2) (f' / ψ)' (x)`. -/
theorem diffusionGenerator_eq_of_hasDerivAt {ψ f : ℝ → ℝ} {x : ℝ}
    (ha : a x ≠ 0) (hψ0 : ψ x ≠ 0)
    (hψ : HasDerivAt ψ (-(2 * b x / a x) * ψ x) x)
    (hf : HasDerivAt (deriv f) (deriv (deriv f) x) x) :
    diffusionGenerator b a f x =
      (a x * ψ x / 2) * deriv (fun y => deriv f y / ψ y) x := by
  have hdiv : HasDerivAt (fun y => deriv f y / ψ y)
      ((deriv (deriv f) x * ψ x - deriv f x * (-(2 * b x / a x) * ψ x)) / ψ x ^ 2) x :=
    hf.div hψ hψ0
  rw [diffusionGenerator, hdiv.deriv]
  field_simp
  ring

/-- Canonical form of a regular one-dimensional diffusion generator: for a regular diffusion and `f`
whose total derivative `deriv f` is differentiable on `(0, 1)`, `L f = (1/m) (f'/ψ)'`, the
`d/dm ∘ d/dS` form, on `(0, 1)`. -/
theorem diffusionGenerator_eq_one_div_speedDensity (h : IsRegularDiffusion b a)
    {f : ℝ → ℝ} (hf' : DifferentiableOn ℝ (deriv f) (Ioo 0 1)) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    diffusionGenerator b a f x =
      (1 / speedDensity b a x) * deriv (fun y => deriv f y / scaleDensity b a y) x := by
  have hfAt : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    (hf'.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have key := diffusionGenerator_eq_of_hasDerivAt (h.pos x hx).ne'
    (scaleDensity_pos b a x).ne' (h.hasDerivAt_scaleDensity hx) hfAt
  rw [key, speedDensity]
  congr 1
  field_simp [(h.pos x hx).ne', (scaleDensity_pos b a x).ne']

/-- Neutral Wright–Fisher speed density: the scale density is `1`, so
`m(x) = 2 / (x (1 - x))` (as a real identity for every `x`; at `x = 0` and `x = 1` both sides
are `0` by division by `0`). -/
theorem speedDensity_neutral (x : ℝ) :
    speedDensity (fun _ => 0) (fun x => x * (1 - x)) x = 2 / (x * (1 - x)) := by
  have hψ : scaleDensity (fun _ => 0) (fun x => x * (1 - x)) x = 1 := by
    simp [scaleDensity]
  rw [speedDensity, hψ, mul_one]

/-- Mutation scale density with the normalization `ψ(x) = x^{-θ₁} (1-x)^{-θ₂}`
(real powers), finite and positive on `(0, 1)` for every real `θ₁, θ₂`.
With real powers, `0 ^ 0 = 1`, `0 ^ t = 0` for `t ≠ 0` and `s ^ t = |s| ^ t cos (π t)`
for `s < 0`; the intended domain is `0 < x < 1`. -/
noncomputable def mutationScaleDensity (θ₁ θ₂ x : ℝ) : ℝ :=
  x ^ (-θ₁) * (1 - x) ^ (-θ₂)

/-- Mutation speed density `2 x^{θ₁-1} (1-x)^{θ₂-1}` (real powers).
With real powers, `0 ^ 0 = 1`, `0 ^ t = 0` for `t ≠ 0` and `s ^ t = |s| ^ t cos (π t)`
for `s < 0`; the intended domain is `0 < x < 1`. -/
noncomputable def mutationSpeedDensity (θ₁ θ₂ x : ℝ) : ℝ :=
  2 * x ^ (θ₁ - 1) * (1 - x) ^ (θ₂ - 1)

/-- Selection–mutation scale density `e^{-2αx} x^{-θ₁} (1-x)^{-θ₂}`.
With real powers, `0 ^ 0 = 1`, `0 ^ t = 0` for `t ≠ 0` and `s ^ t = |s| ^ t cos (π t)`
for `s < 0`; the intended domain is `0 < x < 1`. -/
noncomputable def selectionMutationScaleDensity (α θ₁ θ₂ x : ℝ) : ℝ :=
  Real.exp (-2 * α * x) * mutationScaleDensity θ₁ θ₂ x

/-- Selection–mutation speed density `e^{2αx} · 2 x^{θ₁-1} (1-x)^{θ₂-1}`.
With real powers, `0 ^ 0 = 1`, `0 ^ t = 0` for `t ≠ 0` and `s ^ t = |s| ^ t cos (π t)`
for `s < 0`; the intended domain is `0 < x < 1`. -/
noncomputable def selectionMutationSpeedDensity (α θ₁ θ₂ x : ℝ) : ℝ :=
  Real.exp (2 * α * x) * mutationSpeedDensity θ₁ θ₂ x

/-- The selection–mutation scale density is positive on `(0, 1)` for every real `θ₁, θ₂`. -/
theorem selectionMutationScaleDensity_pos {α θ₁ θ₂ x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < selectionMutationScaleDensity α θ₁ θ₂ x := by
  unfold selectionMutationScaleDensity mutationScaleDensity
  exact mul_pos (Real.exp_pos _) (mul_pos (Real.rpow_pos_of_pos hx.1 _)
    (Real.rpow_pos_of_pos (sub_pos.mpr hx.2) _))

/-- On `(0, 1)` the selection–mutation speed density is `2 / (a ψ)` for `a(x) = x (1 - x)` and its scale density: the selection factor `e^{2αx}` appears in `m`. -/
theorem selectionMutationSpeedDensity_eq {α θ₁ θ₂ x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    selectionMutationSpeedDensity α θ₁ θ₂ x =
      2 / ((x * (1 - x)) * selectionMutationScaleDensity α θ₁ θ₂ x) := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : (1 - x) ≠ 0 := (sub_pos.mpr hx.2).ne'
  have hexp : Real.exp (-2 * α * x) = (Real.exp (2 * α * x))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [selectionMutationSpeedDensity, mutationSpeedDensity, selectionMutationScaleDensity,
    mutationScaleDensity, Real.rpow_sub_one hx0 θ₁, Real.rpow_sub_one hx1 θ₂,
    Real.rpow_neg hx.1.le, Real.rpow_neg (sub_pos.mpr hx.2).le, hexp]
  field_simp [(Real.rpow_pos_of_pos hx.1 θ₁).ne', (Real.rpow_pos_of_pos (sub_pos.mpr hx.2) θ₂).ne',
    (Real.exp_pos (2 * α * x)).ne']

/-- The selection–mutation scale density satisfies `ψ'/ψ = -2b/a` for the selection–mutation drift and `a(x) = x (1 - x)`, on `(0, 1)`. -/
theorem hasDerivAt_selectionMutationScaleDensity {α θ₁ θ₂ x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (selectionMutationScaleDensity α θ₁ θ₂)
      ((-(2 * (α * x * (1 - x) + (θ₁ * (1 - x) - θ₂ * x) / 2) / (x * (1 - x)))) *
        selectionMutationScaleDensity α θ₁ θ₂ x) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : (1 - x) ≠ 0 := (sub_pos.mpr hx.2).ne'
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-2 * α * y))
      (Real.exp (-2 * α * x) * (-2 * α)) x := by
    simpa only [mul_one] using ((hasDerivAt_id' x).const_mul (-2 * α)).exp
  have hr1 : HasDerivAt (fun y : ℝ => y ^ (-θ₁)) ((-θ₁ / x) * x ^ (-θ₁)) x := by
    have h := Real.hasDerivAt_rpow_const (p := -θ₁) (Or.inl hx0)
    convert h using 1
    rw [Real.rpow_sub_one hx0 (-θ₁)]
    ring
  have hr2 : HasDerivAt (fun y : ℝ => (1 - y) ^ (-θ₂))
      ((θ₂ / (1 - x)) * (1 - x) ^ (-θ₂)) x := by
    have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have h := hsub.rpow_const (p := -θ₂) (Or.inl hx1)
    convert h using 1
    rw [Real.rpow_sub_one hx1 (-θ₂)]
    field_simp
  have hψ := hexp.mul (hr1.mul hr2)
  have hval : (-(2 * (α * x * (1 - x) + (θ₁ * (1 - x) - θ₂ * x) / 2) / (x * (1 - x)))) *
        selectionMutationScaleDensity α θ₁ θ₂ x =
      Real.exp (-2 * α * x) * (-2 * α) * (x ^ (-θ₁) * (1 - x) ^ (-θ₂)) +
        Real.exp (-2 * α * x) *
          ((-θ₁ / x) * x ^ (-θ₁) * (1 - x) ^ (-θ₂) +
            x ^ (-θ₁) * ((θ₂ / (1 - x)) * (1 - x) ^ (-θ₂))) := by
    simp only [selectionMutationScaleDensity, mutationScaleDensity]
    field_simp
    ring
  rw [hval]
  refine hψ.congr_of_eventuallyEq ?_
  exact Filter.EventuallyEq.of_eq (funext fun y => by
    simp [selectionMutationScaleDensity, mutationScaleDensity, Pi.mul_apply])

/-- Canonical form of the selection–mutation generator in terms of its speed and scale densities, on
`(0, 1)`, for `f` whose total derivative `deriv f` is differentiable on `(0, 1)`, including
non-integrable endpoint regimes. -/
theorem selectionMutationGenerator_eq_one_div_speedDensity {α θ₁ θ₂ : ℝ} {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ (deriv f) (Ioo 0 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    selectionMutationGenerator α θ₁ θ₂ f x =
      (1 / selectionMutationSpeedDensity α θ₁ θ₂ x) *
        deriv (fun y => deriv f y / selectionMutationScaleDensity α θ₁ θ₂ y) x := by
  have hfAt : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    (hf'.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hψ0 : selectionMutationScaleDensity α θ₁ θ₂ x ≠ 0 :=
    (selectionMutationScaleDensity_pos hx).ne'
  have ha : x * (1 - x) ≠ 0 := mul_ne_zero hx.1.ne' (sub_pos.mpr hx.2).ne'
  have key := diffusionGenerator_eq_of_hasDerivAt (b :=
      fun y => α * y * (1 - y) + (θ₁ * (1 - y) - θ₂ * y) / 2)
    (a := fun y => y * (1 - y)) ha hψ0
    (hasDerivAt_selectionMutationScaleDensity hx) hfAt
  have hgen : selectionMutationGenerator α θ₁ θ₂ f x =
      diffusionGenerator (fun y => α * y * (1 - y) + (θ₁ * (1 - y) - θ₂ * y) / 2)
        (fun y => y * (1 - y)) f x := by
    simp only [selectionMutationGenerator, diffusionGenerator]
  rw [hgen, key, selectionMutationSpeedDensity_eq hx]
  congr 1
  field_simp [ha, hψ0]

/-- Total speed mass in the mutation case: `∫₀¹ m = 2 B(θ₁, θ₂)` for `θ₁, θ₂ > 0`. -/
theorem integral_mutationSpeedDensity {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    ∫ x in (0 : ℝ)..1, mutationSpeedDensity θ₁ θ₂ x =
      2 * ProbabilityTheory.beta θ₁ θ₂ := by
  have hEq : mutationSpeedDensity θ₁ θ₂ = fun x => 2 * wrightDensity (θ₁ / 2) (θ₂ / 2) x := by
    funext x
    change 2 * x ^ (θ₁ - 1) * (1 - x) ^ (θ₂ - 1) =
      2 * (x ^ (2 * (θ₁ / 2) - 1) * (1 - x) ^ (2 * (θ₂ / 2) - 1))
    rw [show 2 * (θ₁ / 2) - 1 = θ₁ - 1 from by ring, show 2 * (θ₂ / 2) - 1 = θ₂ - 1 from by ring]
    ring
  rw [hEq, intervalIntegral.integral_const_mul,
    integral_wrightDensity (by linarith) (by linarith),
    show 2 * (θ₁ / 2) = θ₁ from by ring, show 2 * (θ₂ / 2) = θ₂ from by ring,
    ProbabilityTheory.beta]

end MathlibExt.Biology.PopulationGenetics.Diffusion
