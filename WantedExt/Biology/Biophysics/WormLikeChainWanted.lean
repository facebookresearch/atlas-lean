/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mean-square end-to-end distance of the worm-like chain (Kratky–Porod)

A worm-like chain of contour length `L_C > 0` has unit tangents `u(s)`, `0 ≤ s ≤ L_C`, whose
correlation decays exponentially with the persistence length `ℓ_p > 0`:
`⟨u(s) · u(s')⟩ = e^{-|s - s'|/ℓ_p}`. Its end-to-end vector is `R = ∫_0^{L_C} u(s) ds`, and the
Kratky–Porod result is

  `⟨R²⟩ = 2 ℓ_p L_C - 2 ℓ_p² (1 - e^{-L_C/ℓ_p})`,

so that `⟨R²⟩ ≈ L_C²` (a rigid rod) when `L_C ≪ ℓ_p` and `⟨R²⟩ ≈ 2 ℓ_p L_C` (a random coil) when
`L_C ≫ ℓ_p`. The formula is the double integral of the correlation, by linearity of
expectation. The secondary source prints the integrand as `e^{-(s - s')/ℓ_p}`, without the
absolute value; the formula holds only with `|s - s'|`, which is used here.

Sources: O. Kratky and G. Porod, "Röntgenuntersuchung gelöster Fadenmoleküle", Recl. Trav.
Chim. Pays-Bas 68 (1949) 1106–1122; the derivation as stated in A. Tokmakoff, *Concepts in
Biophysical Chemistry* (open textbook, University of Chicago), Section 9.2.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Notation

@[expose] public section

namespace WantedExt.Biology.Biophysics.WormLikeChainWanted

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

/-- The Kratky–Porod expression `2 ℓ_p L - 2 ℓ_p² (1 - e^{-L/ℓ_p})`, for arbitrary real `ℓ_p`
and `L`. For `ℓ_p > 0` and `L ≥ 0` it is the mean-square end-to-end distance of a worm-like chain
of contour length `L` and persistence length `ℓ_p` (`integral_norm_endToEnd_sq`). -/
noncomputable def meanSquareEndToEnd (ℓp L : ℝ) : ℝ :=
  2 * ℓp * L - 2 * ℓp ^ 2 * (1 - Real.exp (-L / ℓp))

/-- **The double-integral identity** (Kratky and Porod 1949). For `ℓ_p > 0` and `L ≥ 0`,
`∫_0^L ∫_0^L e^{-|s - s'|/ℓ_p} ds' ds = 2 ℓ_p L - 2 ℓ_p² (1 - e^{-L/ℓ_p})`. Tokmakoff,
Section 9.2, defines the tangent correlation as `g(s) = ⟨t(0) · t(s)⟩ = exp[-|s|/ℓ_p]`
(Eq. (9.2.1)) and gives this value for `⟨R²⟩`; only the middle line of its derivation prints the
integrand as `e^{-(s - s')/ℓ_p}`, without the absolute value.

Source: Kratky and Porod (1949); Tokmakoff, Section 9.2. -/
theorem_wanted integral_integral_exp_abs (ℓp L : ℝ) (hℓp : 0 < ℓp) (hL : 0 ≤ L) :
    ∫ s in (0 : ℝ)..L, ∫ s' in (0 : ℝ)..L, Real.exp (-|s - s'| / ℓp) =
      meanSquareEndToEnd ℓp L

/-- **Mean-square end-to-end distance** (Kratky and Porod 1949). Let `(Ω, P)` be a probability
space and `u : Ω → ℝ → ℝ³` a random tangent field that is jointly measurable, has unit length
`‖u ω s‖ = 1` everywhere, and has correlation `E ⟪u(s), u(s')⟫ = e^{-|s - s'|/ℓ_p}` for all
`s, s' ∈ [0, L]`, with `ℓ_p > 0` and `L ≥ 0`. Then the end-to-end vector
`R = ∫_0^L u(s) ds` satisfies `E ‖R‖² = 2 ℓ_p L - 2 ℓ_p² (1 - e^{-L/ℓ_p})`.

Source: Kratky and Porod (1949); Tokmakoff, Section 9.2. -/
theorem_wanted integral_norm_endToEnd_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℓp L : ℝ) (hℓp : 0 < ℓp) (hL : 0 ≤ L)
    (u : Ω → ℝ → EuclideanSpace ℝ (Fin 3)) (hmeas : Measurable (Function.uncurry u))
    (hunit : ∀ ω s, ‖u ω s‖ = 1)
    (hcorr : ∀ s ∈ Set.Icc 0 L, ∀ s' ∈ Set.Icc 0 L,
      ∫ ω, ⟪u ω s, u ω s'⟫ ∂P = Real.exp (-|s - s'| / ℓp)) :
    ∫ ω, ‖∫ s in (0 : ℝ)..L, u ω s‖ ^ 2 ∂P = meanSquareEndToEnd ℓp L

/-- **Rod and coil limits** (Kratky and Porod 1949). For `ℓ_p > 0`:
`⟨R²⟩ / L² → 1` as `L → 0⁺` (rigid rod), and `⟨R²⟩ / (2 ℓ_p L) → 1` as `L → ∞`
(random coil), where `⟨R²⟩ = meanSquareEndToEnd ℓ_p L`.

Source: Kratky and Porod (1949); Tokmakoff, Section 9.2. -/
theorem_wanted tendsto_meanSquareEndToEnd (ℓp : ℝ) (hℓp : 0 < ℓp) :
    Tendsto (fun L => meanSquareEndToEnd ℓp L / L ^ 2) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun L => meanSquareEndToEnd ℓp L / (2 * ℓp * L)) atTop (𝓝 1)

end WantedExt.Biology.Biophysics.WormLikeChainWanted
