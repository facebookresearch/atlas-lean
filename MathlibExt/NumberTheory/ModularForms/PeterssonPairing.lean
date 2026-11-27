/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CuspForm_Petersson.lean`,
`Definitions/Def_AutomorphicForm_FundamentalDomainVolume.lean`,
`Theorems/Thm_CuspForm_petersson_add_left.lean`
and
`P2M/Sol/S_CuspForm_petersson_add_left.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

import MathlibExt.NumberTheory.ModularForms.FundamentalDomainExactVolume

/-!
# The Petersson pairing on cusp forms for `Γ₀(N)`

The Petersson pairing of two cusp forms is the integral over the standard
fundamental domain of the sum, over coset representatives of `Γ₀(N)` in
`SL(2, ℤ)`, of the pointwise Petersson product of their translates. Using
the finiteness of the hyperbolic volume of the fundamental domain
(`ModularGroup.volume_fd_lt_top`), we prove additivity of the pairing in its
first argument.
-/

@[expose] public section

open MeasureTheory UpperHalfPlane
open scoped MatrixGroups ModularForm Modular NNReal ENNReal

namespace CuspForm

variable {N : ℕ} {k : ℤ}

/-- The integrand of the Petersson pairing: the sum over the cosets of
`Γ₀(N)` in `SL(2, ℤ)` of the pointwise Petersson products of translates. -/
noncomputable def peterssonIntegrand [NeZero N] (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
    UpperHalfPlane.petersson k (⇑f ∣[k] (q.out⁻¹ : SL(2, ℤ)))
      (⇑g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

/-- The Petersson pairing of two cusp forms for `Γ₀(N)`, as the integral
of `peterssonIntegrand` over the standard fundamental domain. -/
noncomputable def petersson [NeZero N] (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
    (peterssonIntegrand f g)

theorem petersson_def [NeZero N] (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    petersson f g =
      MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
        (peterssonIntegrand f g) :=
  rfl

end CuspForm

namespace CuspForm

variable {N : ℕ} {k : ℤ}

private noncomputable def peterssonTranslate (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (σ : SL(2, ℤ)) : ℍ → ℂ :=
  ⇑f ∣[k] (σ⁻¹ : SL(2, ℤ))

private theorem peterssonTranslate_mul_of_mem
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    peterssonTranslate f (σ * γ) = peterssonTranslate f σ := by
  unfold peterssonTranslate
  rw [mul_inv_rev, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq f _
    (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) (inv_mem hγ))

private theorem continuous_peterssonTranslate
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) :
    Continuous (peterssonTranslate f σ) := by
  have h : peterssonTranslate f σ = ⇑(CuspForm.translate f (σ⁻¹ : SL(2, ℤ))) := by
    rw [CuspForm.coe_translate]; rfl
  rw [h]
  exact (CuspForm.translate f (σ⁻¹ : SL(2, ℤ))).holo'.continuous

private noncomputable def peterssonSummand (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (τ : ℍ) : ℂ :=
  UpperHalfPlane.petersson k (peterssonTranslate f q.out) (peterssonTranslate g q.out) τ

private theorem peterssonSummand_mk (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (σ : SL(2, ℤ)) (τ : ℍ) :
    peterssonSummand f g (QuotientGroup.mk σ) τ =
      UpperHalfPlane.petersson k (peterssonTranslate f σ) (peterssonTranslate g σ) τ := by
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) σ
  unfold peterssonSummand
  rw [hγ, peterssonTranslate_mul_of_mem f σ γ γ.2,
    peterssonTranslate_mul_of_mem g σ γ γ.2]

private theorem peterssonIntegrand_eq_sum [NeZero N]
    [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    peterssonIntegrand f g τ = ∑ q, peterssonSummand f g q τ := by
  have h : peterssonIntegrand f g τ =
      ∑ᶠ q, peterssonSummand f g q τ :=
    rfl
  rw [h, finsum_eq_sum_of_fintype]

private theorem peterssonSummand_add (f₁ f₂ g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    peterssonSummand (f₁ + f₂) g q τ =
      peterssonSummand f₁ g q τ + peterssonSummand f₂ g q τ := by
  simp only [peterssonSummand, peterssonTranslate, FunLike.coe_add, SlashAction.add_slash,
    UpperHalfPlane.petersson, Pi.add_apply, map_add]
  ring

private theorem peterssonIntegrand_add [NeZero N]
    [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f₁ f₂ g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    peterssonIntegrand (f₁ + f₂) g τ =
      peterssonIntegrand f₁ g τ + peterssonIntegrand f₂ g τ := by
  rw [peterssonIntegrand_eq_sum, peterssonIntegrand_eq_sum, peterssonIntegrand_eq_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => peterssonSummand_add f₁ f₂ g q τ

private theorem continuous_peterssonIntegrand [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    Continuous (peterssonIntegrand f g) := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  have h : peterssonIntegrand f g = fun τ => ∑ q, peterssonSummand f g q τ :=
    funext (peterssonIntegrand_eq_sum f g)
  rw [h]
  refine continuous_finsetSum _ fun q _ => ?_
  exact UpperHalfPlane.petersson_continuous k (continuous_peterssonTranslate f _)
    (continuous_peterssonTranslate g _)

private theorem peterssonIntegrand_bounded [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ∃ C, ∀ τ, ‖peterssonIntegrand f g τ‖ ≤ C := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) f g
  refine ⟨∑ _q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, C, fun τ => ?_⟩
  rw [peterssonIntegrand_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  unfold peterssonSummand peterssonTranslate
  have htr : ∀ (h : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) (τ : ℍ),
      UpperHalfPlane.petersson k (⇑h ∣[k] (σ⁻¹ : SL(2, ℤ)))
          (⇑g ∣[k] (σ⁻¹ : SL(2, ℤ))) τ =
        UpperHalfPlane.petersson k ⇑h ⇑g ((σ⁻¹ : SL(2, ℤ)) • τ) :=
    fun h σ τ => UpperHalfPlane.petersson_slash_SL k ⇑h ⇑g σ⁻¹ τ
  rw [htr f q.out τ]
  exact hC _

private theorem integrableOn_peterssonIntegrand [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    IntegrableOn (peterssonIntegrand f g) ModularGroup.fd volume := by
  obtain ⟨C, hC⟩ := peterssonIntegrand_bounded f g
  refine Measure.integrableOn_of_bounded (M := C) ModularGroup.volume_fd_lt_top.ne
    (continuous_peterssonIntegrand f g).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall hC

/-- The Petersson pairing is additive in its first argument. -/
public theorem petersson_add_left [NeZero N] (f₁ f₂ g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    petersson (f₁ + f₂) g = petersson f₁ g + petersson f₂ g := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  rw [petersson_def, petersson_def, petersson_def,
    ← MeasureTheory.integral_add (integrableOn_peterssonIntegrand f₁ g)
      (integrableOn_peterssonIntegrand f₂ g)]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun τ => peterssonIntegrand_add f₁ f₂ g τ)

end CuspForm
