/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.ODE.ContinuumBalances
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Nonlinear 1D shallow water: conservative and primitive forms

At a wet point with positive depth, the conservative mass and momentum
equations agree with the primitive shallow-water equations. A centred
rarefaction and a dry-state counterexample delimit the statement.

## i. Overview

One horizontal dimension, flat frictionless bed, no rotation, and constant
gravitational acceleration `g`. Fields are functions of time first, then
space: `h t x` is the total fluid depth (not the surface elevation), and
`u t x` is the depth-averaged velocity, positive towards increasing `x`.
The convention record is `(h, q = h * u, g)`, with unit-width discharge
`q = h * u` derived from the fields, never an independent field.

Both conservative equations have zero source and are written through the
canonical `localConservation` predicate: mass `∂ₜh + ∂ₓ(h u) = 0` and
momentum `∂ₜ(h u) + ∂ₓ(h u² + g h² / 2) = 0`. The primitive form is
`∂ₜh + u ∂ₓh + h ∂ₓu = 0` and `∂ₜu + u ∂ₓu + g ∂ₓh = 0`.

Only classical pointwise solutions are considered. The four first
partials at `(t, x)` are supplied as `HasDerivAt` witnesses for the time
and space slices, and the primitive form is stated in those witness
values. The conservative side uses Mathlib's totalized `deriv` inside the
canonical predicate, which is meaningful because the slice witnesses make
every differentiated product differentiable at the point. Positive depth
`0 < h t x` is the only place a division by `h` is needed; no totalized
division or inverse appears in the main statement. The constant `g` is an
arbitrary real in the equivalence (the physical domain is `0 < g`); the
rarefaction divides by `τ` and by `g`, only at `0 < t` and `0 < g`.

The linear system in `PhyslibExt.EarthScience.ShallowWater` is the
linearization of the primitive form about the resting state `h = H`,
`u = 0` with `H > 0`. Pointwise local identities at one point only: no
weak, shock, entropy, or existence theorem, no bed slope, friction, or
rotation, and no surface-elevation variable.

## ii. Key results

- `EarthScience.shallow_water_conservative_iff_primitive`: conservative
  and primitive forms agree at a wet point.
- `EarthScience.shallow_water_conservative_rarefaction`: the centred
  rarefaction satisfies both conservative equations on the wet side, with
  positive depth and nonzero depth gradient.
- `EarthScience.exists_dry_conservative_not_primitive`: at zero depth the
  equivalence fails, so positive depth cannot be dropped.

## iii. Table of contents

- A. Conservative-primitive equivalence
- B. Rarefaction and dry-state controls

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics*, 2nd ed.,
  Cambridge University Press (2017), Ch. 3, §3.1 (3.1.1, 3.1.2) for the
  shallow-water equations and §3.7.1 for the non-rotating linear waves.
- `MathlibExt.Analysis.ODE.ContinuumBalances.localConservation`.

## A. Conservative-primitive equivalence
-/

@[expose] public section

open MathlibExt.Analysis.ODE.ContinuumBalances

namespace EarthScience

/-- Conservative and primitive forms of 1D flat-bed frictionless
shallow water agree at a wet point. Let `h` be the depth and `u` the
velocity, with time and space slices differentiable at `(t, x)` with
partials `hₜ`, `hₓ`, `uₜ`, `uₓ`, and let the depth be positive there.
Then mass and momentum conservation, `∂ₜh + ∂ₓ(h u) = 0` and
`∂ₜ(h u) + ∂ₓ(h u² + g h² / 2) = 0`, hold at `(t, x)` if and only if
`hₜ + u hₓ + h uₓ = 0` and `uₜ + u uₓ + g hₓ = 0` hold there. Classical
pointwise statement; no weak solutions. -/
theorem shallow_water_conservative_iff_primitive
    {h u : ℝ → ℝ → ℝ} {g t x hₜ hₓ uₜ uₓ : ℝ}
    (hpos : 0 < h t x)
    (dht : HasDerivAt (fun τ => h τ x) hₜ t)
    (dhx : HasDerivAt (h t) hₓ x)
    (dut : HasDerivAt (fun τ => u τ x) uₜ t)
    (dux : HasDerivAt (u t) uₓ x) :
    (localConservation h (fun τ y => h τ y * u τ y) 0 t x ∧
      localConservation (fun τ y => h τ y * u τ y)
        (fun τ y => h τ y * u τ y ^ 2 + g * h τ y ^ 2 / 2) 0 t x) ↔
    (hₜ + u t x * hₓ + h t x * uₓ = 0 ∧
      uₜ + u t x * uₓ + g * hₓ = 0) := by
  have e1 : deriv (fun τ => h τ x) t = hₜ := dht.deriv
  have e2 : HasDerivAt (fun y => h t y * u t y) (hₓ * u t x + h t x * uₓ) x :=
    dhx.mul dux
  have e3 : HasDerivAt (fun τ => h τ x * u τ x) (hₜ * u t x + h t x * uₜ) t :=
    dht.mul dut
  have eU2 : HasDerivAt (fun y => u t y ^ 2) (↑2 * u t x ^ (2 - 1) * uₓ) x :=
    dux.pow 2
  have eH2 : HasDerivAt (fun y => h t y ^ 2) (↑2 * h t x ^ (2 - 1) * hₓ) x :=
    dhx.pow 2
  have eF1 : HasDerivAt (fun y => h t y * u t y ^ 2)
      (hₓ * u t x ^ 2 + h t x * (↑2 * u t x ^ (2 - 1) * uₓ)) x :=
    dhx.mul eU2
  have eF2 : HasDerivAt (fun y => g * h t y ^ 2 / 2)
      (g * (↑2 * h t x ^ (2 - 1) * hₓ) / 2) x :=
    (eH2.const_mul g).div_const 2
  have eF : HasDerivAt (fun y => h t y * u t y ^ 2 + g * h t y ^ 2 / 2)
      ((hₓ * u t x ^ 2 + h t x * (↑2 * u t x ^ (2 - 1) * uₓ)) +
        (g * (↑2 * h t x ^ (2 - 1) * hₓ) / 2)) x :=
    eF1.add eF2
  simp only [localConservation, Pi.zero_apply, e1, e2.deriv, e3.deriv, eF.deriv]
  constructor
  · rintro ⟨c1, c2⟩
    have hne : h t x ≠ 0 := hpos.ne'
    have m : hₜ + u t x * hₓ + h t x * uₓ = 0 := by linear_combination c1
    have hP : h t x * (uₜ + u t x * uₓ + g * hₓ) = 0 := by
      linear_combination c2 - (u t x) * c1
    have p : uₜ + u t x * uₓ + g * hₓ = 0 := by
      rcases mul_eq_zero.mp hP with h0 | hp
      · exact absurd h0 hne
      · exact hp
    exact ⟨m, p⟩
  · rintro ⟨m, p⟩
    refine ⟨?_, ?_⟩
    · linear_combination m
    · linear_combination (h t x) * p + (u t x) * m

/-! ## B. Rarefaction and dry-state controls -/

/-- Nonzero depth gradient: the centred rarefaction
`h = (2 c₀ - x / t)² / (9 g)`, `u = 2 (x / t + c₀) / 3` satisfies both
conservative equations at every point with `0 < t` on the wet side
`x < 2 c₀ t`, where the depth is positive and its gradient is nonzero,
so the flux products genuinely vary. For `0 < c₀`, the self-similar fan
profile is read physically only between `-c₀ t ≤ x ≤ 2 c₀ t`; the
hypothesis `x < 2 c₀ t` restricts to the wet side of the dry edge
`x = 2 c₀ t`. Requires `0 < g`. -/
lemma shallow_water_conservative_rarefaction
    {g c₀ t x : ℝ} (hg : 0 < g) (ht : 0 < t) (hx : x < 2 * c₀ * t) :
    (localConservation (fun τ y => (2 * c₀ - y / τ) ^ 2 / (9 * g))
        (fun τ y => (2 * c₀ - y / τ) ^ 2 / (9 * g) *
          (2 * (y / τ + c₀) / 3)) 0 t x ∧
      localConservation
        (fun τ y => (2 * c₀ - y / τ) ^ 2 / (9 * g) *
          (2 * (y / τ + c₀) / 3))
        (fun τ y => (2 * c₀ - y / τ) ^ 2 / (9 * g) *
            (2 * (y / τ + c₀) / 3) ^ 2 +
          g * ((2 * c₀ - y / τ) ^ 2 / (9 * g)) ^ 2 / 2) 0 t x) ∧
    0 < (2 * c₀ - x / t) ^ 2 / (9 * g) ∧
    deriv (fun y => (2 * c₀ - y / t) ^ 2 / (9 * g)) x ≠ 0 := by
  have ht' : t ≠ 0 := ht.ne'
  have hg' : g ≠ 0 := hg.ne'
  have hxt : x / t < 2 * c₀ := (div_lt_iff₀ ht).mpr hx
  have hApos : 0 < 2 * c₀ - x / t := sub_pos.mpr hxt
  have hA : 2 * c₀ - x / t ≠ 0 := hApos.ne'
  have h9g : (0:ℝ) < 9 * g := by positivity
  have h1t : (1:ℝ) / t ≠ 0 := div_ne_zero one_ne_zero ht'
  have hB : (0:ℝ) - 1 / t ≠ 0 := sub_ne_zero.mpr (Ne.symm h1t)
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht'
  have h9g' : (9:ℝ) * g ≠ 0 := h9g.ne'
  have s1 : HasDerivAt (fun y : ℝ => y / t) (1 / t) x :=
    (hasDerivAt_id x).div_const t
  have sA : HasDerivAt (fun y : ℝ => 2 * c₀ - y / t) (0 - 1 / t) x :=
    (hasDerivAt_const x (2 * c₀)).sub s1
  have sAA : HasDerivAt (fun y : ℝ => (2 * c₀ - y / t) * (2 * c₀ - y / t)) _ x :=
    sA.mul sA
  have sH : HasDerivAt (fun y : ℝ => (2 * c₀ - y / t) * (2 * c₀ - y / t) / (9 * g))
      (((0 - 1 / t) * (2 * c₀ - x / t) + (2 * c₀ - x / t) * (0 - 1 / t)) / (9 * g)) x :=
    sAA.div_const (9 * g)
  have sU0 : HasDerivAt (fun y : ℝ => y / t + c₀) (1 / t + 0) x :=
    s1.add (hasDerivAt_const x c₀)
  have sU : HasDerivAt (fun y : ℝ => 2 * (y / t + c₀) / 3) (2 * (1 / t + 0) / 3) x :=
    (sU0.const_mul 2).div_const 3
  have sUU : HasDerivAt
      (fun y : ℝ => (2 * (y / t + c₀) / 3) * (2 * (y / t + c₀) / 3)) _ x :=
    sU.mul sU
  have sHH : HasDerivAt (fun y : ℝ =>
      ((2 * c₀ - y / t) * (2 * c₀ - y / t) / (9 * g)) *
        ((2 * c₀ - y / t) * (2 * c₀ - y / t) / (9 * g))) _ x :=
    sH.mul sH
  have mS : HasDerivAt (fun y : ℝ =>
      (2 * c₀ - y / t) * (2 * c₀ - y / t) / (9 * g) * (2 * (y / t + c₀) / 3)) _ x :=
    sH.mul sU
  have p1 : HasDerivAt (fun y : ℝ =>
      ((2 * c₀ - y / t) * (2 * c₀ - y / t) / (9 * g)) *
        ((2 * (y / t + c₀) / 3) * (2 * (y / t + c₀) / 3))) _ x :=
    sH.mul sUU
  have p2 : HasDerivAt (fun y : ℝ => g *
      (((2 * c₀ - y / t) * (2 * c₀ - y / t) / (9 * g)) *
        ((2 * c₀ - y / t) * (2 * c₀ - y / t) / (9 * g))) / 2) _ x :=
    (sHH.const_mul g).div_const 2
  have pS : HasDerivAt (fun y : ℝ =>
      ((2 * c₀ - y / t) * (2 * c₀ - y / t) / (9 * g)) *
          ((2 * (y / t + c₀) / 3) * (2 * (y / t + c₀) / 3)) +
        g * (((2 * c₀ - y / t) * (2 * c₀ - y / t) / (9 * g)) *
          ((2 * c₀ - y / t) * (2 * c₀ - y / t) / (9 * g))) / 2) _ x :=
    p1.add p2
  have t1 : HasDerivAt (fun τ : ℝ => x / τ) ((0 * t - x * 1) / t ^ 2) t :=
    (hasDerivAt_const t x).div (hasDerivAt_id t) ht'
  have tA : HasDerivAt (fun τ : ℝ => 2 * c₀ - x / τ) (0 - (0 * t - x * 1) / t ^ 2) t :=
    (hasDerivAt_const t (2 * c₀)).sub t1
  have tAA : HasDerivAt (fun τ : ℝ => (2 * c₀ - x / τ) * (2 * c₀ - x / τ)) _ t :=
    tA.mul tA
  have tH : HasDerivAt
      (fun τ : ℝ => (2 * c₀ - x / τ) * (2 * c₀ - x / τ) / (9 * g)) _ t :=
    tAA.div_const (9 * g)
  have tU0 : HasDerivAt (fun τ : ℝ => x / τ + c₀) ((0 * t - x * 1) / t ^ 2 + 0) t :=
    t1.add (hasDerivAt_const t c₀)
  have tU : HasDerivAt (fun τ : ℝ => 2 * (x / τ + c₀) / 3)
      (2 * ((0 * t - x * 1) / t ^ 2 + 0) / 3) t :=
    (tU0.const_mul 2).div_const 3
  have mT : HasDerivAt (fun τ : ℝ =>
      (2 * c₀ - x / τ) * (2 * c₀ - x / τ) / (9 * g) * (2 * (x / τ + c₀) / 3)) _ t :=
    tH.mul tU
  simp only [pow_two]
  simp only [localConservation, Pi.zero_apply, tH.deriv, mS.deriv, mT.deriv, pS.deriv,
    sH.deriv]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring
  · exact div_pos (mul_pos hApos hApos) h9g
  · have hfac : (0 - 1 / t) * (2 * c₀ - x / t) + (2 * c₀ - x / t) * (0 - 1 / t)
        = 2 * (0 - 1 / t) * (2 * c₀ - x / t) := by ring
    rw [hfac]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hB) hA) h9g'

/-- Dry state rejected: at zero depth the equivalence fails, for every
`g`. There are fields with `h t x = 0` whose slice partials
exist, which satisfy both conservative equations at `(t, x)`, but for which the
two primitive equations do not both hold there. So the positive-depth
admission of `shallow_water_conservative_iff_primitive` cannot be
dropped. -/
lemma exists_dry_conservative_not_primitive (g t x : ℝ) :
    ∃ (h u : ℝ → ℝ → ℝ) (hₜ hₓ uₜ uₓ : ℝ), h t x = 0 ∧
      HasDerivAt (fun τ => h τ x) hₜ t ∧ HasDerivAt (h t) hₓ x ∧
      HasDerivAt (fun τ => u τ x) uₜ t ∧ HasDerivAt (u t) uₓ x ∧
      (localConservation h (fun τ y => h τ y * u τ y) 0 t x ∧
        localConservation (fun τ y => h τ y * u τ y)
          (fun τ y => h τ y * u τ y ^ 2 + g * h τ y ^ 2 / 2) 0 t x) ∧
      ¬ (hₜ + u t x * hₓ + h t x * uₓ = 0 ∧
        uₜ + u t x * uₓ + g * hₓ = 0) := by
  refine ⟨fun _ _ => 0, fun τ _ => τ, 0, 0, 1, 0, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hasDerivAt_const t 0
  · exact hasDerivAt_const x 0
  · exact hasDerivAt_id t
  · exact hasDerivAt_const x t
  · have h0τ : HasDerivAt (fun τ : ℝ => 0 * τ) (0 * t + 0 * 1) t :=
      (hasDerivAt_const t 0).mul (hasDerivAt_id t)
    simp only [localConservation, Pi.zero_apply, deriv_const, h0τ.deriv]
    constructor <;> ring
  · simp

end EarthScience
