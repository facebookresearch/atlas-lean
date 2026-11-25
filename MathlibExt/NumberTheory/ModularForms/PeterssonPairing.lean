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

/-!
# The Petersson pairing on cusp forms for `Γ₀(N)`

The Petersson pairing of two cusp forms is the integral over the standard
fundamental domain of the sum, over coset representatives of `Γ₀(N)` in
`SL(2, ℤ)`, of the pointwise Petersson product of their translates. We
record the finiteness of the hyperbolic volume of the fundamental domain
(the dyadic band estimate) and prove additivity of the pairing in its
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

namespace PeterssonPairingAux

/-- A dyadic band in the upper half-plane. -/
private def band (A a : ℝ) (n : ℕ) : Set ℍ :=
  {z : ℍ | |z.re| ≤ A ∧ a * 2 ^ n ≤ z.im ∧ z.im ≤ a * 2 ^ (n + 1)}

private theorem verticalStrip_subset_iUnion_band (A : ℝ) {a : ℝ} (ha : 0 < a) :
    UpperHalfPlane.verticalStrip A a ⊆ ⋃ n : ℕ, band A a n := by
  rintro z ⟨hre, him⟩
  have hex : ∃ n : ℕ, z.im ≤ a * 2 ^ (n + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (z.im / a) (one_lt_two (α := ℝ))
    exact ⟨n, by
      rw [div_lt_iff₀ ha] at hn
      nlinarith [pow_pos (zero_lt_two (α := ℝ)) n, pow_succ (2 : ℝ) n]⟩
  classical
  refine Set.mem_iUnion.mpr ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · exact hre
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h0 | hsucc
  · rw [h0]; simpa using him
  · rw [hsucc]
    have hlt := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [not_le] at hlt
    exact le_of_lt hlt

private noncomputable def cbox (relo rehi imlo imhi : ℝ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Set.Icc relo rehi ×ˢ Set.Icc imlo imhi)

private lemma mem_cbox {relo rehi imlo imhi : ℝ} {w : ℂ} :
    w ∈ cbox relo rehi imlo imhi ↔
      (relo ≤ w.re ∧ w.re ≤ rehi) ∧ imlo ≤ w.im ∧ w.im ≤ imhi := by
  simp only [cbox, Set.mem_preimage, Complex.measurableEquivRealProd_apply, Set.mem_prod,
    Set.mem_Icc]

private lemma volume_cbox (relo rehi imlo imhi : ℝ) :
    volume (cbox relo rehi imlo imhi) =
      ENNReal.ofReal (rehi - relo) * ENNReal.ofReal (imhi - imlo) := by
  rw [cbox, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet)]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]

private theorem volume_band_le {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (n : ℕ) :
    volume (band A a n) ≤ ENNReal.ofReal (2 * A * (a⁻¹ * (1 / 2) ^ n)) := by
  have h2n : (0 : ℝ) < a * 2 ^ n := by positivity
  rw [UpperHalfPlane.volume_eq_lintegral]
  have himg : (UpperHalfPlane.coe '' band A a n) ⊆
      cbox (-A) A (a * 2 ^ n) (a * 2 ^ (n + 1)) := by
    rintro w ⟨z, ⟨hre, him₁, him₂⟩, rfl⟩
    rw [mem_cbox, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    exact ⟨abs_le.mp hre, him₁, him₂⟩
  refine le_trans (lintegral_mono_set himg) ?_
  have hbound : ∀ w ∈ cbox (-A) A (a * 2 ^ n) (a * 2 ^ (n + 1)),
      (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal ((a * 2 ^ n)⁻¹ ^ 2) := by
    intro w hw
    obtain ⟨-, him₁, -⟩ := mem_cbox.mp hw
    have hwim : (0 : ℝ) < w.im := lt_of_lt_of_le h2n him₁
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    rw [Real.norm_eq_abs, abs_of_pos hwim]
    have h1 : (a * 2 ^ n)⁻¹ ^ 2 = (1 / (a * 2 ^ n)) ^ 2 := by rw [one_div]
    rw [h1]
    gcongr
  refine le_trans (setLIntegral_mono measurable_const hbound) ?_
  rw [setLIntegral_const, volume_cbox]
  have harith₁ : A - -A = 2 * A := by ring
  have harith₂ : a * 2 ^ (n + 1) - a * 2 ^ n = a * 2 ^ n := by ring
  rw [harith₁, harith₂, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [show (a * 2 ^ n)⁻¹ ^ 2 * (2 * A * (a * 2 ^ n)) =
        2 * A * ((a * 2 ^ n)⁻¹ ^ 2 * (a * 2 ^ n)) by ring,
    pow_two, mul_assoc ((a * 2 ^ n)⁻¹), inv_mul_cancel₀ h2n.ne', mul_one, mul_inv,
    ← inv_pow]
  norm_num

private theorem volume_verticalStrip_lt_top (A : ℝ) {a : ℝ} (ha : 0 < a) :
    volume (UpperHalfPlane.verticalStrip A a) < ⊤ := by
  rcases le_or_gt 0 A with hA | hA
  swap
  · have hempty : UpperHalfPlane.verticalStrip A a = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hz
      exact absurd hz.1 (not_le.mpr (lt_of_lt_of_le hA (abs_nonneg _)))
    rw [hempty]
    simp
  calc volume (UpperHalfPlane.verticalStrip A a)
      ≤ volume (⋃ n : ℕ, band A a n) :=
        measure_mono (verticalStrip_subset_iUnion_band A ha)
    _ ≤ ∑' n : ℕ, volume (band A a n) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 * A * (a⁻¹ * (1 / 2) ^ n)) :=
        ENNReal.tsum_le_tsum fun n => volume_band_le hA ha n
    _ = ∑' n : ℕ, ENNReal.ofReal (2 * A * a⁻¹) * ENNReal.ofReal ((1 / 2) ^ n) :=
        tsum_congr fun n => by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
    _ = ENNReal.ofReal (2 * A * a⁻¹) * ∑' n : ℕ, ENNReal.ofReal ((1 / 2) ^ n) :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (2 * A * a⁻¹) * ∑' n : ℕ, ENNReal.ofReal (1 / 2) ^ n :=
        congrArg _ (tsum_congr fun n => ENNReal.ofReal_pow (by norm_num) n)
    _ = ENNReal.ofReal (2 * A * a⁻¹) * (1 - ENNReal.ofReal (1 / 2))⁻¹ := by
        rw [ENNReal.tsum_geometric]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [ENNReal.inv_lt_top, tsub_pos_iff_lt]
        exact ENNReal.ofReal_lt_one.mpr (by norm_num)

private theorem volume_fd_lt_top : volume ModularGroup.fd < ⊤ := by
  have hsub : ModularGroup.fd ⊆ UpperHalfPlane.verticalStrip (1 / 2) (1 / 2) := by
    intro z hz
    refine ⟨hz.2, ?_⟩
    have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
    nlinarith [z.im_pos]
  exact lt_of_le_of_lt (measure_mono hsub)
    (volume_verticalStrip_lt_top (1 / 2) (by norm_num))

end PeterssonPairingAux

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
  refine Measure.integrableOn_of_bounded (M := C) PeterssonPairingAux.volume_fd_lt_top.ne
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
