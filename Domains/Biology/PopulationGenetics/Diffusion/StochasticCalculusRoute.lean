/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Hölder bound for the Wright–Fisher diffusion coefficient

Consider the frequency `x ∈ [0, 1]` of an allele in a diploid population of
size `N`, with time measured in units of `2N` generations. Following the
repository conventions in `Diffusion.WrightFisher`, the scaled genic
selection coefficient is `σ = 2 * N * s`, where `s` is the per-allele
advantage per generation; for two-way mutation, the scaled rates are
`θ₁ = 4 * N * u₁` and `θ₂ = 4 * N * u₂`, where `u₁` is the per-generation,
per-copy mutation rate towards the allele and `u₂` the rate away from it.
In this scaling the Wright–Fisher diffusion has infinitesimal variance
`x * (1 - x)` and diffusion coefficient `√(x * (1 - x))`. The combined drift
estimated below is
`σ * x * (1 - x) + (θ₁ * (1 - x) - θ₂ * x) / 2`. Existing declarations keep
its two summands separate: `generator σ` in `Diffusion.WrightFisher` is the
selection-only backward generator, while `mutationGenerator θ₁ θ₂` in
`Diffusion.Mutation` is the mutation-only backward generator. No combined
generator declaration is introduced or claimed here; the drift theorem is a
pointwise estimate for the displayed combined coefficient function.

This file proves the coefficient estimates used by Yamada–Watanabe style
pathwise-uniqueness arguments: the Hölder-`1/2` estimate with constant `1`
for the diffusion coefficient, the Lipschitz bound for the variance function
`x * (1 - x)`, and the corresponding Lipschitz estimate for the drift above.

## Main results

* `abs_mul_one_sub_sub_le`: `x (1 - x)` is `1`-Lipschitz on `[0, 1]`.
* `abs_sqrt_mul_one_sub_sub_le`: `√(x (1 - x))` is `1/2`-Hölder with
  constant `1` on `[0, 1]`.
* `abs_genicDrift_sub_le`: the drift Lipschitz estimate.

## References

* S. Wright, *Evolution in Mendelian populations*, Genetics 16 (1931) 97–159.
* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), ch. 4–5.
* S. N. Ethier and T. G. Kurtz, *Markov Processes*, Wiley (1986), ch. 10.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- The Wright–Fisher variance function `x * (1 - x)` is `1`-Lipschitz on
`[0, 1]`: `|x * (1 - x) - y * (1 - y)| ≤ |x - y|`, since the difference
factors as `(x - y) * (1 - x - y)` and `|1 - x - y| ≤ 1` on the unit
square. -/
theorem abs_mul_one_sub_sub_le {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |x * (1 - x) - y * (1 - y)| ≤ |x - y| := by
  have hfactor : x * (1 - x) - y * (1 - y) = (x - y) * (1 - x - y) := by ring
  rw [hfactor, abs_mul]
  have h1 : |1 - x - y| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  calc |x - y| * |1 - x - y| ≤ |x - y| * 1 :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |x - y| := mul_one _

/-- Hölder-`1/2` bound for the Wright–Fisher diffusion coefficient
`√(x * (1 - x))` on `[0, 1]`, with constant `1`:
`|√(x * (1 - x)) - √(y * (1 - y))| ≤ √|x - y|`. -/
theorem abs_sqrt_mul_one_sub_sub_le {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |Real.sqrt (x * (1 - x)) - Real.sqrt (y * (1 - y))| ≤ Real.sqrt |x - y| := by
  have hu : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
  have hv : 0 ≤ y * (1 - y) := mul_nonneg hy0 (by linarith)
  have hsq : (Real.sqrt (x * (1 - x)) - Real.sqrt (y * (1 - y))) ^ 2 ≤
      |x * (1 - x) - y * (1 - y)| := by
    rcases le_total (x * (1 - x)) (y * (1 - y)) with huv | hvu
    · rw [abs_of_nonpos (sub_nonpos.mpr huv)]
      have hle : Real.sqrt (x * (1 - x)) ≤ Real.sqrt (y * (1 - y)) :=
        Real.sqrt_le_sqrt huv
      have h2 : Real.sqrt (x * (1 - x)) * Real.sqrt (x * (1 - x)) ≤
          Real.sqrt (x * (1 - x)) * Real.sqrt (y * (1 - y)) :=
        mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
      have hsu : Real.sqrt (x * (1 - x)) ^ 2 = x * (1 - x) := Real.sq_sqrt hu
      have hsv : Real.sqrt (y * (1 - y)) ^ 2 = y * (1 - y) := Real.sq_sqrt hv
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
      have hle : Real.sqrt (y * (1 - y)) ≤ Real.sqrt (x * (1 - x)) :=
        Real.sqrt_le_sqrt hvu
      have h2 : Real.sqrt (y * (1 - y)) * Real.sqrt (y * (1 - y)) ≤
          Real.sqrt (y * (1 - y)) * Real.sqrt (x * (1 - x)) :=
        mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
      have hsu : Real.sqrt (x * (1 - x)) ^ 2 = x * (1 - x) := Real.sq_sqrt hu
      have hsv : Real.sqrt (y * (1 - y)) ^ 2 = y * (1 - y) := Real.sq_sqrt hv
      linarith
  have hmain : |Real.sqrt (x * (1 - x)) - Real.sqrt (y * (1 - y))| ≤
      Real.sqrt |x * (1 - x) - y * (1 - y)| :=
    Real.abs_le_sqrt hsq
  have hle : |x * (1 - x) - y * (1 - y)| ≤ |x - y| :=
    abs_mul_one_sub_sub_le hx0 hx1 hy0 hy1
  exact le_trans hmain (Real.sqrt_le_sqrt hle)

/-- Lipschitz estimate for the genic-selection/two-way-mutation drift
`σ x (1 - x) + (θ₁ (1 - x) - θ₂ x) / 2` on `[0, 1]`, with constant
`|σ| + (|θ₁| + |θ₂|) / 2`, for arbitrary real `σ`, `θ₁`, `θ₂`; the diffusion-drift reading needs
`θ₁, θ₂ ≥ 0`. -/
theorem abs_genicDrift_sub_le (σ θ₁ θ₂ : ℝ) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |(σ * (x * (1 - x)) + (θ₁ * (1 - x) - θ₂ * x) / 2) -
        (σ * (y * (1 - y)) + (θ₁ * (1 - y) - θ₂ * y) / 2)| ≤
      (|σ| + (|θ₁| + |θ₂|) / 2) * |x - y| := by
  have hsplit : (σ * (x * (1 - x)) + (θ₁ * (1 - x) - θ₂ * x) / 2) -
        (σ * (y * (1 - y)) + (θ₁ * (1 - y) - θ₂ * y) / 2) =
      σ * (x * (1 - x) - y * (1 - y)) - ((θ₁ + θ₂) / 2) * (x - y) := by ring
  rw [hsplit]
  have hcore : |x * (1 - x) - y * (1 - y)| ≤ |x - y| :=
    abs_mul_one_sub_sub_le hx0 hx1 hy0 hy1
  have hθ : |(θ₁ + θ₂) / 2| ≤ (|θ₁| + |θ₂|) / 2 := by
    rw [abs_div]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    have h := abs_add_le θ₁ θ₂
    linarith
  calc |σ * (x * (1 - x) - y * (1 - y)) - ((θ₁ + θ₂) / 2) * (x - y)|
      ≤ |σ * (x * (1 - x) - y * (1 - y))| +
          |((θ₁ + θ₂) / 2) * (x - y)| := abs_sub _ _
    _ = |σ| * |x * (1 - x) - y * (1 - y)| +
          |(θ₁ + θ₂) / 2| * |x - y| := by rw [abs_mul, abs_mul]
    _ ≤ |σ| * |x - y| + ((|θ₁| + |θ₂|) / 2) * |x - y| :=
        add_le_add (mul_le_mul_of_nonneg_left hcore (abs_nonneg σ))
          (mul_le_mul_of_nonneg_right hθ (abs_nonneg _))
    _ = (|σ| + (|θ₁| + |θ₂|) / 2) * |x - y| := by ring

end MathlibExt.Biology.PopulationGenetics.Diffusion
