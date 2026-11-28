/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.GeneralDiffusion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

/-!
# Scale normalization independence

This module shows that the analytic Dirichlet ratio (`fixationProb`) and the
Green kernel (`greenFunction`) do not depend on where the scale function is
normalized. Shifting the scale function by a constant, equivalently integrating
the scale density from any interior point `c`, leaves both quantities unchanged
because only scale differences enter.

The interior-normalized scale function `scaleFunctionFrom b a c p` integrates
the scale density from `c` to `p`, while the existing `scaleFunction` is
normalized by `S 0 = 0`. The results below rewrite each quantity in terms of
`scaleFunctionFrom`: the difference identity, the Dirichlet ratio identity, and
the Green kernel identity.

These are analytic identities about the existing definitions. They do not claim
any hitting-probability or occupation interpretation, which would need Feller
boundary hypotheses that `IsRegularDiffusion` does not supply.

References: Karlin and Taylor (1981), Chapter 15; Ewens (2004), Chapter 4.

Intended path:
`Domains/Biology/PopulationGenetics/Diffusion/ScaleNormalization.lean`.
-/

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

open Set MeasureTheory

/-- Interior-normalized scale function: the integral of the scale density from
`c` to `p`. Unlike `scaleFunction` (normalized by `S 0 = 0`), the base point
`c` is arbitrary. The integral is oriented (`∫ y in c..p = -∫ y in p..c`) and is `0` when the
scale density is not integrable between `c` and `p`. The definition imposes no hypotheses; under
`IsRegularDiffusion` and for `c, p ∈ [0, 1]` (or suitable integrability of `scaleDensity b a` on
the relevant intervals), the two differ by the constant `scaleFunction b a c`; see
`scaleFunctionFrom_eq_sub`. -/
public noncomputable def scaleFunctionFrom (b a : ℝ → ℝ) (c p : ℝ) : ℝ :=
  ∫ y in c..p, scaleDensity b a y

/-- The interior-normalized scale function equals the difference of the
`0`-normalized scale function at the endpoints. Stated for `c, p ∈ Icc 0 1`
under `IsRegularDiffusion`; no probabilistic meaning is claimed. -/
public theorem scaleFunctionFrom_eq_sub (b a : ℝ → ℝ) (h : IsRegularDiffusion b a)
    (c p : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) (hp : p ∈ Icc (0 : ℝ) 1) :
    scaleFunctionFrom b a c p = scaleFunction b a p - scaleFunction b a c := by
  have h0p : IntervalIntegrable (scaleDensity b a) volume 0 p :=
    (h.continuousOn_scaleDensity.mono (Icc_subset_Icc_right hp.2)).intervalIntegrable_of_Icc
      hp.1
  have h0c : IntervalIntegrable (scaleDensity b a) volume 0 c :=
    (h.continuousOn_scaleDensity.mono (Icc_subset_Icc_right hc.2)).intervalIntegrable_of_Icc
      hc.1
  have hsub := intervalIntegral.integral_interval_sub_left h0p h0c
  simp only [scaleFunctionFrom, scaleFunction] at hsub ⊢
  exact hsub.symm

/-- The Dirichlet ratio `fixationProb` rewritten with differences of the
interior-normalized scale function, for a regular diffusion and `c, p ∈ [0, 1]`: the additive
normalization constant cancels, and `S(1) > 0`. An analytic identity only; not a
hitting-probability claim. -/
public theorem fixationProb_eq_ratio_scaleFunctionFrom (b a : ℝ → ℝ)
    (h : IsRegularDiffusion b a) (c p : ℝ) (hc : c ∈ Icc (0 : ℝ) 1)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    fixationProb b a p = (scaleFunctionFrom b a c p - scaleFunctionFrom b a c 0) /
      (scaleFunctionFrom b a c 1 - scaleFunctionFrom b a c 0) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have e1 := scaleFunctionFrom_eq_sub b a h c p hc hp
  have e2 := scaleFunctionFrom_eq_sub b a h c 0 hc h0
  have e3 := scaleFunctionFrom_eq_sub b a h c 1 hc h1
  simp only [fixationProb]
  rw [e1, e2, e3, scaleFunction_zero]
  congr 1 <;> ring

/-- The Green kernel rewritten with differences of the interior-normalized
scale function, for a regular diffusion and `c, p, x ∈ [0, 1]`: shifting the scale normalization
leaves the kernel unchanged.
As in `greenFunction`, division by `0` gives `0` (the denominator vanishes where `a x = 0`).
An analytic identity only; not an occupation-density claim. -/
public theorem greenFunction_eq_scaleFunctionFrom (b a : ℝ → ℝ)
    (h : IsRegularDiffusion b a) (c p x : ℝ) (hc : c ∈ Icc (0 : ℝ) 1)
    (hp : p ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    greenFunction b a p x = 2 * (scaleFunctionFrom b a c (min p x) -
      scaleFunctionFrom b a c 0) * (scaleFunctionFrom b a c 1 -
      scaleFunctionFrom b a c (max p x)) / ((scaleFunctionFrom b a c 1 -
      scaleFunctionFrom b a c 0) * a x * scaleDensity b a x) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hmin : min p x ∈ Icc (0 : ℝ) 1 := ⟨le_min hp.1 hx.1, (min_le_left p x).trans hp.2⟩
  have hmax : max p x ∈ Icc (0 : ℝ) 1 := ⟨hp.1.trans (le_max_left p x), max_le hp.2 hx.2⟩
  have e1 := scaleFunctionFrom_eq_sub b a h c (min p x) hc hmin
  have e2 := scaleFunctionFrom_eq_sub b a h c 0 hc h0
  have e3 := scaleFunctionFrom_eq_sub b a h c 1 hc h1
  have e4 := scaleFunctionFrom_eq_sub b a h c (max p x) hc hmax
  simp only [greenFunction]
  rw [e1, e2, e3, e4, scaleFunction_zero]
  congr 1 <;> ring

end MathlibExt.Biology.PopulationGenetics.Diffusion
