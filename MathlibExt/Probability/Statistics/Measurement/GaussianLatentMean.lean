/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Latent mean nonidentification in a two-group Gaussian measurement model -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathlibExt.Probability.Statistics.Measurement

private theorem hasLaw_gaussian_indicator {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F ε : Ω → ℝ} {κ : ℝ} {φ ψ : ℝ≥0} (hF : HasLaw F (gaussianReal κ φ) P)
    (hε : HasLaw ε (gaussianReal 0 ψ) P) (hind : IndepFun F ε P) (ν ℓ : ℝ) :
    HasLaw (fun ω => ν + ℓ * F ω + ε ω)
      (gaussianReal (ν + ℓ * κ) (NNReal.mk (ℓ ^ 2) (sq_nonneg ℓ) * φ + ψ)) P := by
  have hscaled := gaussianReal_const_mul hF ℓ
  have hshifted := gaussianReal_const_add hscaled ν
  have hind' : IndepFun (fun ω => ν + ℓ * F ω) ε P :=
    hind.comp (φ := fun f => ν + ℓ * f) (ψ := id) (by fun_prop) measurable_id
  refine ⟨hshifted.aemeasurable.add hε.aemeasurable, ?_⟩
  change P.map ((fun ω => ν + ℓ * F ω) + ε) = _
  simpa only [add_zero, add_comm (ℓ * κ) ν] using
    gaussianReal_add_gaussianReal_of_indepFun hind' hshifted hε

/-- **An affine change of latent coordinates preserves the observed law.** If `F` has
law `N(κ, φ)` and the error `ε` has law `N(0, ψ)` independently of `F`, then for any
shift `a` and nonzero slope `b` the recoded factor `F' = a + b * F` has law
`N(a + b * κ, b² * φ)` and is still independent of `ε`. Replacing the loading `ℓ`
by `ℓ / b` and the intercept `ν` by `ν - (ℓ / b) * a` leaves the observed indicator
unchanged pointwise. Both indicators have law `N(ν + ℓ * κ, ℓ² * φ + ψ)`. The
transformation can be chosen separately in each group. -/
theorem gaussian_latent_affine_invariance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F ε : Ω → ℝ} {κ : ℝ} {φ ψ : ℝ≥0} (hF : HasLaw F (gaussianReal κ φ) P)
    (hε : HasLaw ε (gaussianReal 0 ψ) P) (hind : IndepFun F ε P) (ν ℓ a : ℝ)
    {b : ℝ} (hb : b ≠ 0) :
    let F' := fun ω => a + b * F ω
    let X := fun ω => ν + ℓ * F ω + ε ω
    let X' := fun ω => (ν - (ℓ / b) * a) + (ℓ / b) * F' ω + ε ω
    HasLaw F' (gaussianReal (a + b * κ) (NNReal.mk (b ^ 2) (sq_nonneg b) * φ)) P ∧
      IndepFun F' ε P ∧ X' = X ∧
      HasLaw X' (gaussianReal (ν + ℓ * κ) (NNReal.mk (ℓ ^ 2) (sq_nonneg ℓ) * φ + ψ)) P := by
  intro F' X X'
  have heq : X' = X := by
    funext ω
    dsimp only [X', X, F']
    field_simp [hb]
    ring
  have hF' : HasLaw F' (gaussianReal (a + b * κ) (NNReal.mk (b ^ 2) (sq_nonneg b) * φ)) P := by
    simpa only [F', add_comm (b * κ) a] using
      gaussianReal_const_add (gaussianReal_const_mul hF b) a
  refine ⟨hF', ?_, heq, ?_⟩
  · exact hind.comp (φ := fun f => a + b * f) (ψ := id) (by fun_prop) measurable_id
  · rw [heq]
    exact hasLaw_gaussian_indicator hF hε hind ν ℓ

private theorem gaussian_unit_indicator_map (ν κ : ℝ) :
    ((gaussianReal κ 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => ν + p.1 + p.2) =
      gaussianReal (ν + κ) 2 := by
  let P := (gaussianReal κ 1).prod (gaussianReal 0 1)
  have hF : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (gaussianReal κ 1) P := measurePreserving_fst.hasLaw
  have hε : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (gaussianReal 0 1) P := measurePreserving_snd.hasLaw
  have hind : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd P :=
    indepFun_prod measurable_id measurable_id
  have h := (hasLaw_gaussian_indicator hF hε hind ν 1).map_eq
  have hv : NNReal.mk ((1 : ℝ) ^ 2) (sq_nonneg (1 : ℝ)) * 1 + 1 = 2 := by
    apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one]
    norm_num
  rw [hv] at h
  simpa only [P, one_mul] using h

/-- **Latent mean differences are not identified without invariance constraints.**
Take two groups with unit loadings and with both latent and independent error variance one.
Model A has intercepts `(0, 0)` and latent means `(0, 1)`; model B has intercepts `(0, 2)`
and latent means `(0, -1)`. The actual Gaussian product models have the same observed
laws, `N(0, 2)` in the first group and `N(1, 2)` in the second, but their latent mean
differences (second group minus first) are `1` and `-1`, respectively. -/
theorem gaussian_latent_mean_nonidentification :
    let observed := fun (ν κ : Fin 2 → ℝ) (g : Fin 2) =>
      ((gaussianReal (κ g) 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => ν g + p.1 + p.2)
    let νA : Fin 2 → ℝ := ![0, 0]
    let κA : Fin 2 → ℝ := ![0, 1]
    let νB : Fin 2 → ℝ := ![0, 2]
    let κB : Fin 2 → ℝ := ![0, -1]
    (∀ g, observed νA κA g = gaussianReal (if g = 0 then 0 else 1) 2 ∧
      observed νB κB g = gaussianReal (if g = 0 then 0 else 1) 2) ∧
      κA 1 - κA 0 = 1 ∧ κB 1 - κB 0 = -1 := by
  intro observed νA κA νB κB
  refine ⟨?_, by norm_num [κA], by norm_num [κB]⟩
  intro g
  constructor
  · change ((gaussianReal (κA g) 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => νA g + p.1 + p.2) = _
    rw [gaussian_unit_indicator_map]
    fin_cases g <;> norm_num [νA, κA]
  · change ((gaussianReal (κB g) 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => νB g + p.1 + p.2) = _
    rw [gaussian_unit_indicator_map]
    fin_cases g <;> norm_num [νB, κB]

end MathlibExt.Probability.Statistics.Measurement
