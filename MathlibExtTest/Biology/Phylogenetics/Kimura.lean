/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.Kimura

/-!
# Tests for the Kimura two-parameter (K80) model

The identity at `t = 0` and row sums; explicit entries of the K80 transition matrix at
`κ = 3`, `t = 2` (composite parameters `a = 3/2`, `b = 1/2`) and an exact round trip of the
recovery maps and the Kimura distance on those proportions through `exp`/`log` identities;
nonnegativity in the biological domain and a negative entry outside it; the Jukes–Cantor
reduction numerically (`κ = 1`, and `a = b = 1`) and symbolically; the non-identifiability of
rate scale and time; the eigenbasis; and the junk values at the saturation boundary.
-/

@[expose] public section

open Real Finset Matrix ProbabilityTheory MathlibExt.Biology.Phylogenetics.JukesCantor

namespace MathlibExtTest.Biology.Phylogenetics.Kimura

open MathlibExt.Biology.Phylogenetics.SubstitutionModels

-- The generator's entries: diagonal, a transition `A → G`, a transversion `A → T`.
example : k80Rate 3 0 0 = -(5 / 4) := by rw [k80Rate_apply]; norm_num
example : k80Rate 3 0 2 = 3 / 4 := by rw [k80Rate_apply]; norm_num
example : k80Rate 3 0 3 = 1 / 4 := by rw [k80Rate_apply]; norm_num

-- The eigenbasis is invertible, with the stated inverse.
example : (k80EigenbasisUnit : Matrix (Fin 4) (Fin 4) ℝ) = k80Eigenbasis := rfl
example : (k80EigenbasisUnit : Matrix (Fin 4) (Fin 4) ℝ) *
    (↑(k80EigenbasisUnit⁻¹) : Matrix (Fin 4) (Fin 4) ℝ) = 1 :=
  Units.mul_inv _

-- At `t = 0` the transition matrix is the identity (closed form and matrix exponential agree).
example : kimuraProb 0 0 = 1 := kimuraProb_zero
example (κ : ℝ) : ctmcTransition (k80Rate κ) 0 = kimuraProb 0 0 := by
  rw [ctmcTransition_k80Rate]; norm_num

-- Row sums, at concrete and at arbitrary parameters.
example : ∑ j, kimuraProb (3 / 2) (1 / 2) 2 j = 1 := sum_kimuraProb _ _ 2
example (κ t : ℝ) (i : Fin 4) : ∑ j, ctmcTransition (k80Rate κ) t i j = 1 := by
  rw [ctmcTransition_k80Rate]; exact sum_kimuraProb _ _ i

-- Explicit entries at `κ = 3`, `t = 2`: identity, transition `C → T`, transversion `C → G`.
example : ctmcTransition (k80Rate 3) 2 1 1 = 1 / 4 + 1 / 4 * exp (-2) + 1 / 2 * exp (-4) := by
  rw [ctmcTransition_k80Rate]; norm_num [kimuraProb]
example : ctmcTransition (k80Rate 3) 2 1 3 = 1 / 4 + 1 / 4 * exp (-2) - 1 / 2 * exp (-4) := by
  rw [ctmcTransition_k80Rate]; norm_num [kimuraProb]
example : ctmcTransition (k80Rate 3) 2 1 2 = 1 / 4 - 1 / 4 * exp (-2) := by
  rw [ctmcTransition_k80Rate]; norm_num [kimuraProb]

-- The proportions at `κ = 3`, `t = 2`.
example : transitionProp (ctmcTransition (k80Rate 3) 2) 0 =
    1 / 4 + 1 / 4 * exp (-2) - 1 / 2 * exp (-4) := by
  rw [ctmcTransition_k80Rate, transitionProp_kimuraProb]; norm_num
example : transversionProp (ctmcTransition (k80Rate 3) 2) 0 = 1 / 2 - 1 / 2 * exp (-2) := by
  rw [ctmcTransition_k80Rate, transversionProp_kimuraProb]; norm_num

-- Exact round trip on these proportions, by `exp`/`log` algebra: `b = 1/2`, `a = 3/2` and
-- `d = a + 2b = 5/2 = (κ + 2) t / 4`.
example : kimuraTransversionParam (1 / 2 - 1 / 2 * exp (-2)) = 1 / 2 := by
  rw [kimuraTransversionParam, show 1 - 2 * (1 / 2 - 1 / 2 * exp (-2)) = exp (-2) by ring,
    log_exp]
  norm_num
example :
    kimuraTransitionParam (1 / 4 + 1 / 4 * exp (-2) - 1 / 2 * exp (-4))
      (1 / 2 - 1 / 2 * exp (-2)) = 3 / 2 := by
  rw [kimuraTransitionParam,
    show 1 - 2 * (1 / 4 + 1 / 4 * exp (-2) - 1 / 2 * exp (-4)) - (1 / 2 - 1 / 2 * exp (-2)) =
      exp (-4) by ring,
    show 1 - 2 * (1 / 2 - 1 / 2 * exp (-2)) = exp (-2) by ring, log_exp, log_exp]
  norm_num
example :
    kimuraDistance (1 / 4 + 1 / 4 * exp (-2) - 1 / 2 * exp (-4))
      (1 / 2 - 1 / 2 * exp (-2)) = 5 / 2 := by
  rw [kimuraDistance,
    show 1 - 2 * (1 / 4 + 1 / 4 * exp (-2) - 1 / 2 * exp (-4)) - (1 / 2 - 1 / 2 * exp (-2)) =
      exp (-4) by ring,
    show 1 - 2 * (1 / 2 - 1 / 2 * exp (-2)) = exp (-2) by ring, log_exp, log_exp]
  norm_num
example (i : Fin 4) :
    kimuraDistance (transitionProp (ctmcTransition (k80Rate 3) 2) i)
      (transversionProp (ctmcTransition (k80Rate 3) 2) i) = 5 / 2 := by
  rw [kimuraDistance_k80Rate]; norm_num

-- The recovery maps invert the parametrization on a domain point: `P = 1/10`, `Q = 1/5`.
example (i : Fin 4) :
    transitionProp (kimuraProb (kimuraTransitionParam (1 / 10) (1 / 5))
      (kimuraTransversionParam (1 / 5))) i = 1 / 10 :=
  transitionProp_kimuraProb_recover (by norm_num) (by norm_num) i
example (i : Fin 4) :
    transversionProp (kimuraProb (kimuraTransitionParam (1 / 10) (1 / 5))
      (kimuraTransversionParam (1 / 5))) i = 1 / 5 :=
  transversionProp_kimuraProb_recover (by norm_num) i

-- Nonnegativity in the domain `a, b ≥ 0`.
example (i j : Fin 4) : 0 ≤ kimuraProb (3 / 2) (1 / 2) i j :=
  kimuraProb_nonneg (by norm_num) (by norm_num) i j
-- Outside the domain an entry is negative: `a = -1`, `b = 0` makes the transition entry
-- `1/2 - e^2 / 2 < 0`.
example : kimuraProb (-1) 0 0 2 < 0 := by
  have : (1 : ℝ) < exp 2 := one_lt_exp_iff.mpr (by norm_num)
  norm_num [kimuraProb]

-- Jukes–Cantor reduction, numerically: `a = b = 1` is `jcProb 3 1`, and K80 with `κ = 1`
-- agrees with the closed form at `a = b = t / 4`.
example : kimuraProb 1 1 = Matrix.of (jcProb 3 1) := by
  rw [← kimuraProb_jukesCantor]; norm_num
example (t : ℝ) : kimuraProb (t / 4) (t / 4) = Matrix.of (jcProb (3 / 4) t) := by
  rw [← ctmcTransition_k80Rate_one, ctmcTransition_k80Rate, one_mul]
example : kimuraProb 1 1 0 2 = 1 / 4 - 1 / 4 * exp (-4) := by norm_num [kimuraProb]; ring

-- Jukes–Cantor reduction, symbolically: the Kimura distance is the Jukes–Cantor distance of
-- `P + Q` and returns `μ t`.
example (μ t : ℝ) (i : Fin 4) :
    kimuraDistance (transitionProp (Matrix.of (jcProb μ t)) i)
      (transversionProp (Matrix.of (jcProb μ t)) i) = μ * t := by
  rw [kimuraDistance_jukesCantor, transitionProp_add_transversionProp_jcProb, jcDistance_pDiff]

-- Non-identifiability: doubling the rates and halving the time gives the same matrix.
example : ctmcTransition ((2 : ℝ) • k80Rate 3) 1 = ctmcTransition ((1 : ℝ) • k80Rate 3) 2 := by
  rw [ctmcTransition_smul_k80Rate_eq_iff]; norm_num
example : ctmcTransition ((2 : ℝ) • k80Rate 3) 1 = ctmcTransition (k80Rate 3) 2 := by
  rw [ctmcTransition_smul_k80Rate, ctmcTransition_k80Rate]; norm_num
-- Under the K80 normalization, different times give different matrices, and so do different
-- `κ` at the same positive time.
example : ctmcTransition (k80Rate 3) 1 ≠ ctmcTransition (k80Rate 3) 2 := fun h => by
  have := (ctmcTransition_k80Rate_eq_iff.mp h).1; norm_num at this
example : ctmcTransition (k80Rate 3) 1 ≠ ctmcTransition (k80Rate 2) 1 := fun h => by
  have := (ctmcTransition_k80Rate_eq_iff.mp h).2; norm_num at this
-- At `t = 0` `κ` is not identified.
example : ctmcTransition (k80Rate 3) 0 = ctmcTransition (k80Rate 2) 0 :=
  ctmcTransition_k80Rate_eq_iff.mpr ⟨rfl, by norm_num⟩

-- Boundary: no differences give distance `0`; at saturation `1 - 2Q = 0` the totalized
-- logarithm returns a finite junk value instead of the true divergence.
example : kimuraDistance 0 0 = 0 := by norm_num [kimuraDistance]
example : kimuraDistance (1 / 4) (1 / 2) = 0 := by norm_num [kimuraDistance]
example : kimuraDistance 0 (1 / 2) = 1 / 2 * log 2 := by
  norm_num [kimuraDistance]; rw [one_div, log_inv]; ring

#print axioms ctmcTransition_k80Rate
#print axioms kimuraDistance_k80Rate
#print axioms kimuraProb_injective
#print axioms ctmcTransition_smul_k80Rate_eq_iff
#print axioms transitionProp_kimuraProb_recover
#print axioms kimuraDistance_jukesCantor

end MathlibExtTest.Biology.Phylogenetics.Kimura
