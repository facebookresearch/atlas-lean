/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_
section_add_weylIntertwiningIntegral.lean`
and
`P2M/Sol/S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_
section_add_weylIntertwiningIntegral.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.WeylIntertwiningIntegrable
public import MathlibExt.NumberTheory.NumberField.AdelicPeriodization

/-!
# Box average of the Bruhat sum of an induced section

Let `F` be a number field and `φ` a function on `GL(2, 𝔸_F)`. The explicit Bruhat sum
`bruhatEisenstein φ g = φ g + ∑' ξ : F, φ (w n(ξ) g)` evaluates `φ (γ g)` at the representatives
`γ = 1` and `γ = w n(ξ)`, `ξ ∈ F`, of `B(F) \ GL(2, F)` given by the Bruhat decomposition
`GL(2, F) = B(F) ∪ B(F) w N(F)`. Other representatives can give a different value unless `φ` is
left `B(F)`-invariant, and `∑'` is `0` where the family is not summable. The sum is the classical
Eisenstein series `∑_{γ ∈ B(F) \ GL(2, F)} φ (γ g)` when `φ` is induced from characters trivial
on the principal ideles and that series converges; nothing here assumes either.

The main result computes the normalised box average of the Bruhat sum: the average of
`bruhatEisenstein φ (n(x) g)` over `x` in the adelic fundamental box `adelicBox F`, against the
additive Haar measure normalised to give the box volume one. Let `μ, ν` be unitary idele
characters (the unitarity hypothesis is on `μ, ν`, not on the twists below), `Re s > 1/2`, and
`φ` a continuous section induced from `(μ |·|^(s+1/2), ν |·|^(-(s+1/2)))`. Then the average is
`φ g + vol(adelicBox F)⁻¹ * M φ g`, where `M` is the Weyl intertwining integral. The proof uses
the invariance of `φ` under `N(𝔸_F)` and the integrability of the Weyl integrand; it does not show
that the sum converges at every point.

## Main statements

* `AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral`
-/

@[expose] public section

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open scoped NNReal ENNReal

namespace AutomorphicForm

section BruhatSum

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **Explicit Bruhat sum.** For a function `φ` on `GL(2, 𝔸_K)`,
`bruhatEisenstein φ g = φ g + ∑' ξ : K, φ (w n(ξ) g)`: the values `φ (γ g)` at the representatives
`γ = 1` and `γ = w n(ξ)`, `ξ ∈ K`, of `B(K) \ GL(2, K)`. Nothing is assumed about `φ`: other
representatives can give a different value unless `φ` is left `B(K)`-invariant, and `∑'` is `0`
where the family is not summable. When `φ` is left `B(K)`-invariant and the sum converges, this
is the Eisenstein series `∑_{γ ∈ B(K) \ GL(2, K)} φ (γ g)`. -/
def bruhatEisenstein (φ : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) : ℂ :=
  φ g + ∑' ξ : K, φ (adelicWeyl R K * unipotentGL2 (algebraMap K (AdeleRing R K) ξ) * g)

theorem bruhatEisenstein_apply (φ : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) :
    bruhatEisenstein R K φ g =
      φ g + ∑' ξ : K, φ (adelicWeyl R K * unipotentGL2 (algebraMap K (AdeleRing R K) ξ) * g) :=
  rfl

end BruhatSum

section ConstantTerm

variable (F : Type*) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem constantTerm_cond_adelicBox_eq (μ : Measure 𝔸) [μ.IsAddHaarMeasure]
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hN : ∀ (x : 𝔸) (g : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 x * g) = φ g)
    (w g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun u : 𝔸 => φ (w * unipotentGL2 u * g)) μ) :
    constantTerm (ProbabilityTheory.cond μ (adelicBox F)) unipotentGL2
        (fun g' => φ g' + ∑' ξ : F, φ (w * unipotentGL2 (ι ξ) * g')) g
      = φ g + ((μ (adelicBox F)).toReal : ℂ)⁻¹ * ∫ u, φ (w * unipotentGL2 u * g) ∂μ := by
  have hS := NumberField.AdelicPeriodization.integrableOn_adelicBox_tsum_comp_add F μ hint
  have hunf := NumberField.AdelicPeriodization.setIntegral_adelicBox_tsum_comp_add F μ hint
  have hE : (fun t : 𝔸 => φ (unipotentGL2 t * g) +
      ∑' ξ : F, φ (w * unipotentGL2 (ι ξ) * (unipotentGL2 t * g)))
      = fun t => φ g + ∑' ξ : F, φ (w * unipotentGL2 (t + ι ξ) * g) := by
    funext t
    rw [hN t g]
    congr 1
    refine tsum_congr fun ξ => ?_
    rw [add_comm t, unipotentGL2_add]
    simp only [mul_assoc]
  have hpos : 0 < μ (adelicBox F) := measure_adelicBox_pos F μ
  have hlt : μ (adelicBox F) < ∞ := measure_adelicBox_lt_top F μ
  have : IsFiniteMeasure (μ.restrict (adelicBox F)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hlt⟩
  have hm : ((μ (adelicBox F)).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hlt.ne⟩)
  change ∫ t, (φ (unipotentGL2 t * g) +
      ∑' ξ : F, φ (w * unipotentGL2 (ι ξ) * (unipotentGL2 t * g)))
      ∂(ProbabilityTheory.cond μ (adelicBox F)) = _
  rw [hE, ProbabilityTheory.cond, integral_smul_measure, integral_add (integrable_const _) hS,
    integral_const, measureReal_restrict_apply_univ, measureReal_def, hunf, ENNReal.toReal_inv]
  simp only [Complex.real_smul, Complex.ofReal_inv]
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]

/-- **Box average of the Bruhat sum.** Let `μ, ν` be unitary idele characters (the unitarity
hypothesis is on `μ, ν`, not on the twists), `Re s > 1/2`, and `φ` a continuous section induced
from `(μ |·|^(s+1/2), ν |·|^(-(s+1/2)))`. The average of `bruhatEisenstein φ (n(x) g)` over `x` in
the adelic fundamental box, against the additive Haar measure normalised to give the box volume
one, is `φ g` plus the reciprocal volume of the box times the Weyl intertwining integral. When
`μ, ν` are trivial on the principal ideles and the Eisenstein series of `φ` converges, this is the
constant term of that series; neither is assumed. -/
theorem constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    {s : ℂ} (hs : 1 / 2 < s.re) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F
      (etaFst μ ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
        (fun _ => NNReal.coe_pos.mpr distribHaarChar_pos) s)
      (etaSnd ν ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
        (fun _ => NNReal.coe_pos.mpr distribHaarChar_pos) s) φ)
    (hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        unipotentGL2 (bruhatEisenstein (𝓞 F) F φ) g
      = φ g + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by
  have := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hint := weylIntertwiningIntegrand_integrable_of_re_gt_half F μ ν hμ hν hs hφ hφc g
  rw [adelicWeyl_inv] at hint
  unfold weylIntertwiningIntegral
  rw [adelicWeyl_inv]
  exact constantTerm_cond_adelicBox_eq F (adelicAddHaar (𝓞 F) F) φ
    (fun x g => isInducedSection_unipotent_mul hφ x g) (adelicWeyl (𝓞 F) F) g hint

end ConstantTerm

end AutomorphicForm
