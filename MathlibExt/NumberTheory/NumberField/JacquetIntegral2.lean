/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_CubicInduction_absoluteJacquetIntegral_lt_top_
and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2.lean`,
`P2M/Sol/S_LanglandsTunnell_CubicInduction_absoluteJacquetIntegral_lt_top_
and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2.lean`,
`P2M/Sol/S_LanglandsTunnell_CubicInduction_integrable_apply_antidiagonal_mul_
unipotentGL2_mul_addChar_of_mem_principalSeries2.lean`,
`P2M/Sol/S_AdelicDock_isCompact_and_isOpen_localLevelOne.lean`,
`P2M/Sol/S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm.lean`,
`Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean`
and
`Definitions/Def_AdelicDock_LocalEmbedding.lean`
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

public import MathlibExt.NumberTheory.NumberField.PrincipalSeries2
public import MathlibExt.NumberTheory.NumberField.HigherUnits
public import MathlibExt.NumberTheory.NumberField.LocalLevelOne
public import MathlibExt.NumberTheory.AutomorphicForm.ConstantTerm
public import Mathlib.MeasureTheory.Group.Measure
import MathlibExt.NumberTheory.NumberField.AdeleLocallyCompact
import MathlibExt.RingTheory.DedekindDomain.AdicCompletionResidueField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The absolute Jacquet integral on the principal series of `GL₂(ℚ_p)`

Let `p` be a finite place of `ℚ`, `F = ℚ_p` its completion, `w₀ = !![0, 1; 1, 0]` and
`n(y) = !![1, y; 0, 1]`. For `f` in `principalSeries2 p χ` the absolute Jacquet integral
`g ↦ ∫⁻ y, ‖f (w₀ * n(y) * g)‖ₑ ∂ν` against an additive Haar measure `ν` on `F` is finite when
both characters have finite conductor and `‖χ₀(ϖ)‖ < ‖χ₁(ϖ)‖` for a uniformizer `ϖ`; it is
invariant under left translation of `g` by `n(x)`, scales by the explicit torus factor under
left translation by `diag(t₁, t₂)`, and, when `f` is right invariant under an open subgroup, is
bounded on the local level-one subgroup at the full ideal.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell.CubicInduction

open IsLocalRing

section HaarModulus

variable {K : Type*} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem isOpen_integers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring (v.adicCompletion K)

private theorem isCompact_integers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  HeightOneSpectrum.isCompact_adicCompletionIntegers K v

private theorem smul_integers_of_valued_eq_one (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    u • (v.adicCompletionIntegers K : Set (v.adicCompletion K)) =
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one,
    one_mul]

private theorem distribHaarChar_eq_one (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    distribHaarChar (v.adicCompletion K) u = 1 := by
  let _ : MeasurableSpace (v.adicCompletion K) := borel _
  have : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.addHaar)
    (s := (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (isOpen_integers.measure_ne_zero _ ⟨0, zero_mem _⟩) isCompact_integers.measure_lt_top.ne ?_
  rw [smul_integers_of_valued_eq_one u hu, ENNReal.coe_one, one_mul]

private theorem isUnit_integers_iff (a : v.adicCompletionIntegers K) :
    IsUnit a ↔ Valued.v (a : v.adicCompletion K) = 1 := by
  rw [ValuationSubring.valuation_eq_one_iff]
  exact ((Valuation.isEquiv_valuation_valuationSubring Valued.v).eq_one_iff_eq_one).symm

private theorem lt_one_iff_le_exp_neg_one (x : WithZero (Multiplicative ℤ)) :
    x < 1 ↔ x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
  norm_num

private theorem mem_integers_of_valued {ϖ : v.adicCompletion K}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) : ϖ ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hϖ, ← WithZero.exp_zero]
  exact WithZero.exp_le_exp.mpr (by norm_num)

private theorem irreducible_of_valued {ϖ : v.adicCompletion K}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    Irreducible (⟨ϖ, mem_integers_of_valued hϖ⟩ : v.adicCompletionIntegers K) := by
  refine irreducible_iff.mpr ⟨?_, ?_⟩
  · rw [isUnit_integers_iff]
    change ¬ Valued.v ϖ = 1
    rw [hϖ, ← WithZero.exp_zero]
    exact fun h => by norm_num [WithZero.exp_inj] at h
  · intro a b hab
    have ha : Valued.v (a : v.adicCompletion K) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp a.2
    have hb : Valued.v (b : v.adicCompletion K) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp b.2
    have hprod : Valued.v (a : v.adicCompletion K) * Valued.v (b : v.adicCompletion K) =
        WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, ← MulMemClass.coe_mul, ← hab]
      exact hϖ
    rw [isUnit_integers_iff, isUnit_integers_iff]
    by_contra h
    push Not at h
    have ha' := (lt_one_iff_le_exp_neg_one _).mp (lt_of_le_of_ne ha h.1)
    have hb' := (lt_one_iff_le_exp_neg_one _).mp (lt_of_le_of_ne hb h.2)
    have hle := mul_le_mul' ha' hb'
    rw [hprod, ← WithZero.exp_add, WithZero.exp_le_exp] at hle
    norm_num at hle

section CosetStep

/-- A chosen representative of a residue class of the integers. -/
private def out (k : v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K)) :
    v.adicCompletionIntegers K :=
  (Ideal.Quotient.mk_surjective k).choose

private theorem mk_out
    (k : v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K)) :
    Ideal.Quotient.mk _ (out k) = k :=
  (Ideal.Quotient.mk_surjective k).choose_spec

variable {ϖ : v.adicCompletionIntegers K}

private theorem exists_out_add_mul (hϖ : Irreducible ϖ) (Y : v.adicCompletionIntegers K) :
    ∃ z : v.adicCompletionIntegers K, Y = out (Ideal.Quotient.mk _ Y) + ϖ * z := by
  have hmem : Y - out (Ideal.Quotient.mk _ Y) ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, mk_out, sub_self])
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (hϖ.maximalIdeal_eq.le hmem)
  exact ⟨z, sub_eq_iff_eq_add'.mp hz⟩

private theorem mk_out_add_mul (hϖ : Irreducible ϖ)
    (k : v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K))
    (z : v.adicCompletionIntegers K) : Ideal.Quotient.mk _ (out k + ϖ * z) = k := by
  have hϖ0 : Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K)) ϖ = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self ϖ
  rw [map_add, map_mul, hϖ0, zero_mul, add_zero, mk_out]

/-- The affine map `y ↦ out k + ϖ y` sending the integers onto one residue class. -/
private abbrev cosetMap (ϖ : v.adicCompletionIntegers K)
    (k : v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K))
    (y : v.adicCompletion K) : v.adicCompletion K :=
  ((out k : v.adicCompletionIntegers K) : v.adicCompletion K) +
    ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) * y

private theorem integers_eq_iUnion (hϖ : Irreducible ϖ) :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) =
      ⋃ k : v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K),
        cosetMap ϖ k '' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := exists_out_add_mul hϖ (⟨y, hy⟩ : v.adicCompletionIntegers K)
    refine Set.mem_iUnion.mpr ⟨Ideal.Quotient.mk _ ⟨y, hy⟩, z, z.2, ?_⟩
    have hco := congrArg (fun w : v.adicCompletionIntegers K => (w : v.adicCompletion K)) hz
    push_cast at hco
    exact hco.symm
  · intro hy
    obtain ⟨k, z, hz, hzy⟩ := Set.mem_iUnion.mp hy
    rw [← hzy]
    exact add_mem (out k).2 (mul_mem ϖ.2 hz)

private theorem pairwise_disjoint_cosetMap (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint
      fun k : v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K) =>
        cosetMap ϖ k '' (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
  intro k k' hkk'
  refine Set.disjoint_left.mpr fun y hy hy' => hkk' ?_
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨z', hz', hzy'⟩ := hy'
  have hAeq : (out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers K) = out k' + ϖ * ⟨z', hz'⟩ :=
    Subtype.coe_injective (by push_cast; exact hzy.trans hzy'.symm)
  have := congrArg (Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K))) hAeq
  rwa [mk_out_add_mul hϖ, mk_out_add_mul hϖ] at this

private theorem cosetMap_image_eq
    (k : v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K)) :
    cosetMap ϖ k '' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) =
      ((out k : v.adicCompletionIntegers K) : v.adicCompletion K) +ᵥ
        (((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) •
          (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
  rw [← Set.image_vadd, ← Set.image_smul, ← Set.image_comp]
  rfl

private theorem card_quotient_eq_absNorm :
    Nat.card (v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (HeightOneSpectrum.completionResidueFieldEquiv v).toEquiv

private theorem measure_integers_eq_card_mul [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (hϖ : Irreducible ϖ) :
    μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) *
        μ (((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) •
          (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
  have hϖ0 : ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    simpa using Subtype.coe_injective.ne_iff.mpr hϖ.ne_zero
  have hTmeas : MeasurableSet (((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) •
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    (isOpen_integers.smul₀ hϖ0).measurableSet
  have hfin : Finite (v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K)) :=
    Finite.of_equiv _ (HeightOneSpectrum.completionResidueFieldEquiv v).symm.toEquiv
  have := Fintype.ofFinite (v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K))
  conv_lhs => rw [integers_eq_iUnion hϖ]
  rw [measure_iUnion (pairwise_disjoint_cosetMap hϖ)
    (fun k => by rw [cosetMap_image_eq k]; exact hTmeas.const_vadd _)]
  simp_rw [cosetMap_image_eq, measure_vadd]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← card_quotient_eq_absNorm,
    Nat.card_eq_fintype_card]

end CosetStep

private theorem distribHaarChar_of_valued_eq_exp_neg_one (ϖ : (v.adicCompletion K)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    distribHaarChar (v.adicCompletion K) ϖ = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  let _ : MeasurableSpace (v.adicCompletion K) := borel _
  have : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    have := HeightOneSpectrum.one_lt_absNorm v
    positivity
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.addHaar)
    (s := (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (isOpen_integers.measure_ne_zero _ ⟨0, zero_mem _⟩) isCompact_integers.measure_lt_top.ne ?_
  change Measure.addHaar (((⟨ϖ, mem_integers_of_valued hϖ⟩ : v.adicCompletionIntegers K) :
    v.adicCompletion K) • (v.adicCompletionIntegers K : Set (v.adicCompletion K))) = _
  rw [measure_integers_eq_card_mul Measure.addHaar (irreducible_of_valued hϖ),
    ENNReal.coe_inv hq0, ENNReal.coe_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hq0) (ENNReal.natCast_ne_top _), one_mul]

private theorem nnnorm_of_valued_eq_exp_neg_one {ϖ : v.adicCompletion K}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    ‖ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  refine NNReal.coe_injective ?_
  rw [coe_nnNorm, FinitePlace.norm_def, hϖ,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp, zpow_neg_one]

private theorem nnnorm_of_valued_eq_one {u : v.adicCompletion K} (hu : Valued.v u = 1) :
    ‖u‖₊ = 1 := by
  refine NNReal.coe_injective ?_
  rw [coe_nnNorm, FinitePlace.norm_def, hu, map_one, NNReal.coe_one]

/-- The modulus of the completion: scaling by a unit `u` multiplies additive Haar measure by
`‖u‖`. -/
private theorem distribHaarChar_eq_nnnorm (ϖ : (v.adicCompletion K)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (u : (v.adicCompletion K)ˣ) :
    distribHaarChar (v.adicCompletion K) u = ‖(u : v.adicCompletion K)‖₊ := by
  have hvu : Valued.v (u : v.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr u.ne_zero
  set n : ℤ := WithZero.log (Valued.v (u : v.adicCompletion K)) with hn
  set w : (v.adicCompletion K)ˣ := u * ϖ ^ n with hw_def
  have hw : Valued.v (w : v.adicCompletion K) = 1 := by
    rw [hw_def, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hϖ,
      ← WithZero.exp_log hvu, ← hn, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hu : u = w * ϖ ^ (-n) := by
    rw [hw_def, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hu, map_mul, map_zpow, distribHaarChar_eq_one w hw,
    distribHaarChar_of_valued_eq_exp_neg_one ϖ hϖ, Units.val_mul, Units.val_zpow_eq_zpow_val,
    nnNorm_mul, nnNorm_zpow, nnnorm_of_valued_eq_one hw, nnnorm_of_valued_eq_exp_neg_one hϖ]

private theorem map_mul_left_eq_smul [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion K)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (u : (v.adicCompletion K)ˣ) :
    ν.map (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) =
      ((‖(u : v.adicCompletion K)‖₊ : ℝ≥0∞))⁻¹ • ν := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, smul_apply, smul_eq_mul]
  have hpre : (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) ⁻¹' s = u⁻¹ • s := by
    ext x
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def,
      smul_eq_mul]
  rw [hpre, ← distribHaarChar_mul ν u⁻¹ s, map_inv, distribHaarChar_eq_nnnorm ϖ hϖ u,
    ENNReal.coe_inv (nnNorm_ne_zero_iff.mpr u.ne_zero)]

private theorem lintegral_comp_units_mul [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion K)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (u : (v.adicCompletion K)ˣ) (h : v.adicCompletion K → ℝ≥0∞) :
    ∫⁻ x, h ((u : v.adicCompletion K) * x) ∂ν =
      ((‖(u : v.adicCompletion K)‖₊ : ℝ≥0∞))⁻¹ * ∫⁻ x, h x ∂ν := by
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← map_mul_left_eq_smul ν ϖ hϖ u]
  exact (lintegral_map_equiv h
    (MeasurableEquiv.mulLeft₀ (u : v.adicCompletion K) u.ne_zero)).symm

end HaarModulus

section Jacquet

open Matrix Filter Topology

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- The Weyl element `!![0, 1; 1, 0]`. -/
private def antidiagonal2 : LocalGL2 v where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem antidiagonal2_coe :
    (antidiagonal2 v : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0] :=
  rfl

/-- The lower unipotent element `!![1, 0; y, 1]`. -/
private def lowerUnip (y : v.adicCompletion ℚ) : LocalGL2 v where
  val := !![1, 0; y, 1]
  inv := !![1, 0; -y, 1]
  val_inv := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem lowerUnip_coe (y : v.adicCompletion ℚ) :
    (lowerUnip v y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, 0; y, 1] :=
  rfl

private theorem lowerUnip_zero : lowerUnip v 0 = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [lowerUnip]

private theorem continuous_lowerUnip : Continuous (lowerUnip v) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      first | exact continuous_const | exact continuous_id
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      first | exact continuous_const | exact continuous_id.neg

private theorem continuous_upperUnipotent2 : Continuous (upperUnipotent2 v) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      first | exact continuous_const | exact continuous_id
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      first | exact continuous_const | exact continuous_id.neg

private theorem diagonal2_coe' (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    (diagonal2 v a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      !![(a 0 : v.adicCompletion ℚ), 0; 0, (a 1 : v.adicCompletion ℚ)] := by
  rw [diagonal2_coe]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

private theorem unipotentGL2_eq (y : v.adicCompletion ℚ) :
    (AutomorphicForm.unipotentGL2 y : LocalGL2 v) = upperUnipotent2 v y :=
  Units.ext (by rw [AutomorphicForm.unipotentGL2_coe, upperUnipotent2_coe])

private theorem eq_antidiagonal2 (w₀ : LocalGL2 v)
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    w₀ = antidiagonal2 v :=
  Units.ext (by rw [hw₀, antidiagonal2_coe])

private theorem weyl_upper_diag (y : v.adicCompletion ℚ) (t₁ t₂ : (v.adicCompletion ℚ)ˣ) :
    antidiagonal2 v * upperUnipotent2 v y * diagonal2 v ![t₁, t₂] =
      diagonal2 v ![t₂, t₁] * (antidiagonal2 v *
        upperUnipotent2 v (((t₂ * t₁⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y)) := by
  apply Units.ext
  simp only [Units.val_mul, upperUnipotent2_coe, antidiagonal2_coe, diagonal2_coe',
    Units.val_inv_eq_inv_val]
  have h1 : (t₁ : v.adicCompletion ℚ) ≠ 0 := t₁.ne_zero
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

private theorem coe_upper_diag (x : v.adicCompletion ℚ) (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    ((upperUnipotent2 v x * diagonal2 v a : LocalGL2 v) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      !![(a 0 : v.adicCompletion ℚ), x * (a 1 : v.adicCompletion ℚ); 0,
        (a 1 : v.adicCompletion ℚ)] := by
  rw [Units.val_mul, upperUnipotent2_coe, diagonal2_coe', Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

private theorem coe_weyl_upper (y : v.adicCompletion ℚ) :
    ((antidiagonal2 v * upperUnipotent2 v y : LocalGL2 v) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, y] := by
  rw [Units.val_mul, upperUnipotent2_coe, antidiagonal2_coe, Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

private theorem weyl_upper_eq (y : v.adicCompletion ℚ) (hy : y ≠ 0) :
    antidiagonal2 v * upperUnipotent2 v y =
      upperUnipotent2 v y⁻¹ * diagonal2 v ![Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy)),
        Units.mk0 y hy] * lowerUnip v y⁻¹ := by
  apply Units.ext
  rw [coe_weyl_upper, Units.val_mul, coe_upper_diag, lowerUnip_coe, Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  ring

variable {v}

private theorem norm_eq_zpow_of_valued {y : v.adicCompletion ℚ} {k : ℤ}
    (h : Valued.v y = WithZero.exp k) :
    ‖y‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ k := by
  rw [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    WithZero.log_exp]
  push_cast
  rfl

private theorem one_lt_absNorm : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  exact_mod_cast HeightOneSpectrum.one_lt_absNorm v

private theorem valued_eq_iff_norm_eq {x y : v.adicCompletion ℚ} :
    Valued.v x = Valued.v y ↔ ‖x‖ = ‖y‖ := by
  constructor
  · intro h
    exact le_antisymm (Valued.toNormedField.norm_le_iff.mpr h.le)
      (Valued.toNormedField.norm_le_iff.mpr h.ge)
  · intro h
    exact le_antisymm (Valued.toNormedField.norm_le_iff.mp h.le)
      (Valued.toNormedField.norm_le_iff.mp h.ge)

private theorem valued_zpow {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (((ϖ ^ k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  ring

variable (v) in
/-- The closed ball `{y | v(y) ≤ exp k}`. -/
private def vball (k : ℤ) : Set (v.adicCompletion ℚ) := {y | Valued.v y ≤ WithZero.exp k}

variable (v) in
/-- The sphere `{y | v(y) = exp m}`. -/
private def vshell (m : ℤ) : Set (v.adicCompletion ℚ) := {y | Valued.v y = WithZero.exp m}

private theorem vball_eq_smul {k : ℤ} (t : (v.adicCompletion ℚ)ˣ)
    (hvt : Valued.v (t : v.adicCompletion ℚ) = WithZero.exp k) :
    vball v k = t • (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul, map_mul,
    Units.val_inv_eq_inv_val, map_inv₀, hvt]
  change Valued.v y ≤ _ ↔ _
  rw [inv_mul_le_iff₀ (zero_lt_iff.mpr WithZero.exp_ne_zero), mul_one]

private theorem isCompact_vball {k : ℤ} (t : (v.adicCompletion ℚ)ˣ)
    (hvt : Valued.v (t : v.adicCompletion ℚ) = WithZero.exp k) : IsCompact (vball v k) := by
  rw [vball_eq_smul t hvt]
  exact isCompact_integers.smul _

private theorem vshell_subset_vball (m : ℤ) : vshell v m ⊆ vball v m := fun _ hy => le_of_eq hy

private theorem isCompact_vshell {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    IsCompact (vshell v m) := by
  have hv : Valued.v (((ϖ ^ (-m) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) =
      WithZero.exp m := by rw [valued_zpow hϖ, neg_neg]
  have heq : vshell v m =
      Metric.sphere 0 ‖((ϖ ^ (-m) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ := by
    ext y
    rw [mem_sphere_zero_iff_norm, ← valued_eq_iff_norm_eq, hv]
    rfl
  rw [heq]
  exact isCompact_sphere _ _

private theorem measureReal_vball [MeasurableSpace (v.adicCompletion ℚ)]
    [BorelSpace (v.adicCompletion ℚ)] {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure] (m : ℤ) :
    ν.real (vball v m) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ m *
      ν.real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  have hv : Valued.v (((ϖ ^ (-m) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) =
      WithZero.exp m := by rw [valued_zpow hϖ, neg_neg]
  rw [vball_eq_smul (ϖ ^ (-m)) hv, Measure.real,
    ← distribHaarChar_mul ν (ϖ ^ (-m)) (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)),
    distribHaarChar_eq_nnnorm ϖ hϖ, ENNReal.toReal_mul, Measure.real]
  congr 1
  rw [ENNReal.coe_toReal, coe_nnNorm, norm_eq_zpow_of_valued hv]

private theorem measureReal_vshell_le [MeasurableSpace (v.adicCompletion ℚ)]
    [BorelSpace (v.adicCompletion ℚ)] {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure] (m : ℤ) :
    ν.real (vshell v m) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ m *
      ν.real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  rw [← measureReal_vball hϖ ν m]
  exact measureReal_mono (vshell_subset_vball m)
    (isCompact_vball (ϖ ^ (-m)) (by rw [valued_zpow hϖ, neg_neg])).measure_lt_top.ne

variable (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private theorem law {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ) (x : v.adicCompletion ℚ)
    (a : Fin 2 → (v.adicCompletion ℚ)ˣ) (g : LocalGL2 v) :
    f (upperUnipotent2 v x * (diagonal2 v a * g)) = torusChar2 v χ a * halfModulus2 v a * f g := by
  obtain ⟨-, hn, ht⟩ := mem_principalSeries2_iff.mp hf
  rw [hn, ht]

private theorem halfModulus2_boundary (y : v.adicCompletion ℚ) (hy : y ≠ 0) :
    halfModulus2 v ![Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy)), Units.mk0 y hy] =
      ((‖y‖⁻¹ : ℝ) : ℂ) := by
  unfold halfModulus2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mk0, norm_neg, norm_inv]
  congr 1
  rw [div_eq_mul_inv, Real.sqrt_mul_self (inv_nonneg.mpr (norm_nonneg _))]

private theorem apply_weyl_upper {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ)
    (y : v.adicCompletion ℚ) (hy : y ≠ 0) (g : LocalGL2 v) :
    f (antidiagonal2 v * upperUnipotent2 v y * g) =
      ((χ 0 (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy))) : ℂˣ) : ℂ) *
        ((χ 1 (Units.mk0 y hy) : ℂˣ) : ℂ) * ((‖y‖⁻¹ : ℝ) : ℂ) * f (lowerUnip v y⁻¹ * g) := by
  rw [weyl_upper_eq v y hy]
  simp only [mul_assoc]
  rw [law χ hf, halfModulus2_boundary y hy]
  simp only [torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem exists_radius_lowerUnip {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ)
    (g : LocalGL2 v) : ∃ k₀ : ℕ, ∀ t : v.adicCompletion ℚ,
      Valued.v t ≤ WithZero.exp (-(k₀ : ℤ)) → f (lowerUnip v t * g) = f g := by
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf
  have hcont : Continuous fun t : v.adicCompletion ℚ => lowerUnip v t * g :=
    (continuous_lowerUnip v).mul continuous_const
  obtain ⟨U, hU, hgU, hfU⟩ := hlc.exists_open g
  have hU0 : (fun t : v.adicCompletion ℚ => lowerUnip v t * g) ⁻¹' U ∈ 𝓝 (0 : _) :=
    hcont.continuousAt.preimage_mem_nhds
      (by rw [lowerUnip_zero, one_mul]; exact hU.mem_nhds hgU)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU0
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt
    (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  refine ⟨k, fun t ht => hfU _ (hγ ?_)⟩
  change Valued.v.restrict t < _
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt ht hk

private theorem continuous_char (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hη : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v c, η u = 1)
    {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    Continuous fun a : (v.adicCompletion ℚ)ˣ => ((η a : ℂˣ) : ℂ) := by
  set t : v.adicCompletion ℚ := ((ϖ ^ ((c : ℤ) + 1) : (v.adicCompletion ℚ)ˣ) :
    v.adicCompletion ℚ) with ht_def
  have ht : t ≠ 0 := Units.ne_zero _
  have hvt : Valued.v t = WithZero.exp (-((c : ℤ) + 1)) := valued_zpow hϖ _
  have hc1 : Continuous fun u : (v.adicCompletion ℚ)ˣ => (u : v.adicCompletion ℚ) - 1 :=
    Units.continuous_val.sub continuous_const
  have hV : IsOpen ((fun u : (v.adicCompletion ℚ)ˣ => (u : v.adicCompletion ℚ) - 1) ⁻¹'
      {y | Valued.v y ≤ Valued.v t}) :=
    (AdelicLevel.isOpen_setOf_valued_le (𝓞 ℚ) ℚ v t ht).preimage hc1
  have hVker : ∀ u ∈ (fun u : (v.adicCompletion ℚ)ˣ => (u : v.adicCompletion ℚ) - 1) ⁻¹'
      {y | Valued.v y ≤ Valued.v t}, η u = 1 := by
    intro u hu
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hvt] at hu
    have hlt : Valued.v ((u : v.adicCompletion ℚ) - 1) < 1 := by
      refine lt_of_le_of_lt hu ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    apply hη
    refine ⟨?_, Or.inr (hu.trans ?_)⟩
    · have := Valuation.map_add_eq_of_lt_left (Valued.v : Valuation (v.adicCompletion ℚ) _)
        (x := (1 : v.adicCompletion ℚ)) (y := (u : v.adicCompletion ℚ) - 1)
        (by rwa [Valuation.map_one])
      rw [Valuation.map_one, add_sub_cancel] at this
      exact this
    · rw [WithZero.exp_le_exp]
      omega
  refine continuous_iff_continuousAt.mpr fun a => ?_
  have hev : ∀ᶠ b in 𝓝 a, ((η b : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) := by
    have hmem : (fun u => a * u) '' ((fun u : (v.adicCompletion ℚ)ˣ =>
        (u : v.adicCompletion ℚ) - 1) ⁻¹' {y | Valued.v y ≤ Valued.v t}) ∈ 𝓝 a :=
      ((Homeomorph.mulLeft a).isOpenMap _ hV).mem_nhds ⟨1, by simp, by simp⟩
    filter_upwards [hmem] with b hb
    obtain ⟨u, hu, rfl⟩ := hb
    rw [map_mul, hVker u hu, mul_one]
  exact continuousAt_const.congr (Filter.EventuallyEq.symm hev)

private theorem norm_char_eq_one (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hη : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v c, η u = 1)
    {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    ‖((η u : ℂˣ) : ℂ)‖ = 1 := by
  set S : Set (v.adicCompletion ℚ)ˣ := {u | Valued.v (u : v.adicCompletion ℚ) = 1} with hS
  have hSc : IsCompact S := by
    rw [Units.isEmbedding_val₀.isCompact_iff]
    have himg : ((↑) : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) '' S =
        Metric.sphere 0 1 := by
      ext x
      rw [mem_sphere_zero_iff_norm, Valued.toNormedField.norm_eq_one_iff]
      constructor
      · rintro ⟨u, hu, rfl⟩; exact hu
      · intro hx
        have hx0 : x ≠ 0 := by intro h; rw [h, map_zero] at hx; exact zero_ne_one hx
        exact ⟨Units.mk0 x hx0, hx, rfl⟩
    rw [himg]
    exact isCompact_sphere _ _
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (continuous_char η hη hϖ).continuousOn
  have hle : ∀ w ∈ S, ‖((η w : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro w hw
    by_contra hlt
    rw [not_le] at hlt
    have hpow : ∀ j : ℕ, ‖((η w : ℂˣ) : ℂ)‖ ^ j ≤ C := by
      intro j
      have hwj : w ^ j ∈ S := by
        change Valued.v (((w ^ j : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) = 1
        rw [Units.val_pow_eq_pow_val, map_pow, hw, one_pow]
      have := hC _ hwj
      rwa [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    obtain ⟨j, hj⟩ := Filter.tendsto_atTop_atTop.mp (tendsto_pow_atTop_atTop_of_one_lt hlt)
      (C + 1)
    linarith [hpow j, hj j le_rfl]
  have h1 := hle u hu
  have h2 := hle u⁻¹ (by
    change Valued.v (((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((η u : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  exact le_antisymm h1 (by rwa [inv_le_one₀ hpos] at h2)

private theorem norm_char_eq_zpow (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hη : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v c, η u = 1)
    {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (a : (v.adicCompletion ℚ)ˣ) (k : ℤ)
    (ha : Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k)) :
    ‖((η a : ℂˣ) : ℂ)‖ = ‖((η ϖ : ℂˣ) : ℂ)‖ ^ k := by
  have hu : Valued.v (((ϖ ^ (-k) * a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) = 1 := by
    rw [Units.val_mul, map_mul, valued_zpow hϖ, ha, ← WithZero.exp_add]
    simp
  have h := norm_char_eq_one η hη hϖ _ hu
  rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow] at h
  rw [eq_inv_of_mul_eq_one_right h, _root_.zpow_neg, inv_inv]

private theorem norm_apply_weyl_upper_of_mem_vshell (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v (cχ i), χ i u = 1)
    {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ) (g : LocalGL2 v) {k₀ : ℕ}
    (hk₀ : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-(k₀ : ℤ)) →
      f (lowerUnip v t * g) = f g)
    {m : ℕ} (hm : k₀ ≤ m) {y : v.adicCompletion ℚ} (hy : y ∈ vshell v m) :
    ‖f (antidiagonal2 v * upperUnipotent2 v y * g)‖ =
      (‖((χ 0 ϖ : ℂˣ) : ℂ)‖ / ‖((χ 1 ϖ : ℂˣ) : ℂ)‖) ^ m *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ m)⁻¹ * ‖f g‖ := by
  change Valued.v y = _ at hy
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact WithZero.exp_ne_zero hy.symm
  have hyi : Valued.v y⁻¹ = WithZero.exp (-(m : ℤ)) := by
    rw [map_inv₀, hy, WithZero.exp_neg]
  have hsmall : f (lowerUnip v y⁻¹ * g) = f g :=
    hk₀ _ (by rw [hyi, WithZero.exp_le_exp]; omega)
  rw [apply_weyl_upper χ hf y hy0 g, hsmall, norm_mul, norm_mul, norm_mul]
  have h0 : ‖((χ 0 (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy0))) : ℂˣ) : ℂ)‖ =
      ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ ^ (m : ℤ) :=
    norm_char_eq_zpow (χ 0) (hcχ 0) hϖ _ m (by rw [Units.val_mk0, Valuation.map_neg, hyi])
  have h1 : ‖(((χ 1) (Units.mk0 y hy0) : ℂˣ) : ℂ)‖ = ‖((χ 1 ϖ : ℂˣ) : ℂ)‖ ^ (-(m : ℤ)) :=
    norm_char_eq_zpow (χ 1) (hcχ 1) hϖ _ (-(m : ℤ)) (by rw [Units.val_mk0, hy, neg_neg])
  have hq : ‖(((‖y‖⁻¹ : ℝ) : ℂ))‖ = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ m)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      norm_eq_zpow_of_valued hy, zpow_natCast]
  rw [h0, h1, hq, zpow_natCast, _root_.zpow_neg, zpow_natCast, div_pow]
  ring

private theorem integrable_jacquet [MeasurableSpace (v.adicCompletion ℚ)]
    [BorelSpace (v.adicCompletion ℚ)] (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v (cχ i), χ i u = 1)
    {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hdom : ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖)
    {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ) (g : LocalGL2 v)
    (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure] :
    Integrable (fun y : v.adicCompletion ℚ => f (antidiagonal2 v * upperUnipotent2 v y * g)) ν := by
  set Φ : v.adicCompletion ℚ → ℂ := fun y => f (antidiagonal2 v * upperUnipotent2 v y * g)
    with hΦ
  set q : ℝ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) with hq_def
  have hq0 : 0 < q := lt_trans one_pos one_lt_absNorm
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf
  have hΦc : Continuous Φ :=
    hlc.continuous.comp ((continuous_const.mul (continuous_upperUnipotent2 v)).mul
      continuous_const)
  obtain ⟨k₀, hk₀⟩ := exists_radius_lowerUnip χ hf g
  set r : ℝ := ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ / ‖((χ 1 ϖ : ℂˣ) : ℂ)‖ with hr
  have h1pos : 0 < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) h1pos.le
  have hr1 : r < 1 := (div_lt_one h1pos).mpr hdom
  set V : ℝ := ν.real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) with hV
  have hcover : (Set.univ : Set (v.adicCompletion ℚ)) =
      vball v k₀ ∪ ⋃ j : ℕ, vshell v ((k₀ + 1 + j : ℕ) : ℤ) := by
    refine (Set.eq_univ_of_forall fun y => ?_).symm
    by_cases hy : Valued.v y ≤ WithZero.exp (k₀ : ℤ)
    · exact Or.inl hy
    · right
      rw [not_le] at hy
      have hy0 : Valued.v y ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hy)
      set L : ℤ := WithZero.log (Valued.v y) with hLdef
      have hlog : Valued.v y = WithZero.exp L := (WithZero.exp_log hy0).symm
      have hL : (k₀ : ℤ) < L := by
        rw [hlog, WithZero.exp_lt_exp] at hy
        exact hy
      refine Set.mem_iUnion.mpr ⟨(L - k₀ - 1).toNat, ?_⟩
      change Valued.v y = _
      rw [hlog]
      congr 1
      push_cast
      omega
  have hnear : IntegrableOn Φ (vball v k₀) ν :=
    hΦc.continuousOn.integrableOn_compact
      (isCompact_vball (ϖ ^ (-(k₀ : ℤ))) (by rw [valued_zpow hϖ, neg_neg]))
  have hfar : IntegrableOn Φ (⋃ j : ℕ, vshell v ((k₀ + 1 + j : ℕ) : ℤ)) ν := by
    refine integrableOn_iUnion_of_summable_integral_norm
      (fun j => hΦc.continuousOn.integrableOn_compact (isCompact_vshell hϖ _)) ?_
    have hbound : ∀ j : ℕ, ∫ y in vshell v ((k₀ + 1 + j : ℕ) : ℤ), ‖Φ y‖ ∂ν ≤
        (‖f g‖ * V * r ^ (k₀ + 1)) * r ^ j := by
      intro j
      set m : ℕ := k₀ + 1 + j with hm
      have hCm : 0 ≤ r ^ m * (q ^ m)⁻¹ * ‖f g‖ :=
        mul_nonneg (mul_nonneg (pow_nonneg hr0 m) (inv_nonneg.mpr (pow_nonneg hq0.le m)))
          (norm_nonneg _)
      have hpt : ∀ y ∈ vshell v (m : ℤ), ‖(fun y => ‖Φ y‖) y‖ ≤ r ^ m * (q ^ m)⁻¹ * ‖f g‖ := by
        intro y hy
        rw [Real.norm_of_nonneg (norm_nonneg _), hΦ]
        exact (norm_apply_weyl_upper_of_mem_vshell χ cχ hcχ hϖ hf g hk₀ (by omega) hy).le
      have hI := norm_setIntegral_le_of_norm_le_const
        ((isCompact_vshell hϖ (m : ℤ)).measure_lt_top (μ := ν)) hpt
      have hle : ∫ y in vshell v (m : ℤ), ‖Φ y‖ ∂ν ≤
          r ^ m * (q ^ m)⁻¹ * ‖f g‖ * ν.real (vshell v (m : ℤ)) :=
        (Real.le_norm_self _).trans hI
      refine hle.trans ?_
      have hsh := measureReal_vshell_le hϖ ν (m : ℤ)
      rw [zpow_natCast] at hsh
      have hqm : 0 < q ^ m := pow_pos hq0 m
      calc r ^ m * (q ^ m)⁻¹ * ‖f g‖ * ν.real (vshell v (m : ℤ))
          ≤ r ^ m * (q ^ m)⁻¹ * ‖f g‖ * (q ^ m * V) :=
            mul_le_mul_of_nonneg_left hsh hCm
        _ = ‖f g‖ * V * r ^ m := by field_simp
        _ = (‖f g‖ * V * r ^ (k₀ + 1)) * r ^ j := by rw [hm, pow_add]; ring
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _) hbound ?_
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have huniv : IntegrableOn Φ Set.univ ν := by
    rw [hcover]
    exact hnear.union hfar
  exact integrableOn_univ.mp huniv

private theorem jacquet_lt_top [MeasurableSpace (v.adicCompletion ℚ)]
    [BorelSpace (v.adicCompletion ℚ)] (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v (cχ i), χ i u = 1)
    {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hdom : ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖)
    {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ)
    (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure] (g : LocalGL2 v) :
    ∫⁻ y, ‖f (antidiagonal2 v * upperUnipotent2 v y * g)‖ₑ ∂ν < ∞ :=
  (integrable_jacquet χ cχ hcχ hϖ hdom hf g ν).hasFiniteIntegral

private theorem jacquet_upper_mul [MeasurableSpace (v.adicCompletion ℚ)]
    [BorelSpace (v.adicCompletion ℚ)] (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
    (f : LocalGL2 v → ℂ) (x : v.adicCompletion ℚ) (g : LocalGL2 v) :
    ∫⁻ y, ‖f (antidiagonal2 v * upperUnipotent2 v y * (upperUnipotent2 v x * g))‖ₑ ∂ν =
      ∫⁻ y, ‖f (antidiagonal2 v * upperUnipotent2 v y * g)‖ₑ ∂ν := by
  have h : (fun y => ‖f (antidiagonal2 v * upperUnipotent2 v y * (upperUnipotent2 v x * g))‖ₑ) =
      fun y => (fun z => ‖f (antidiagonal2 v * upperUnipotent2 v z * g)‖ₑ) (y + x) := by
    funext y
    simp only [← upperUnipotent2_mul, mul_assoc]
  rw [h]
  exact lintegral_add_right_eq_self (μ := ν)
    (fun z => ‖f (antidiagonal2 v * upperUnipotent2 v z * g)‖ₑ) x

private theorem norm_torus_factor (t₁ t₂ : (v.adicCompletion ℚ)ˣ) :
    ‖torusChar2 v χ ![t₂, t₁] * halfModulus2 v ![t₂, t₁]‖ =
      ‖((χ 0 t₂ : ℂˣ) : ℂ)‖ * ‖((χ 1 t₁ : ℂˣ) : ℂ)‖ *
        Real.sqrt (‖(t₂ : v.adicCompletion ℚ)‖ / ‖(t₁ : v.adicCompletion ℚ)‖) := by
  simp only [torusChar2, halfModulus2, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

private theorem jacquet_diag_mul [MeasurableSpace (v.adicCompletion ℚ)]
    [BorelSpace (v.adicCompletion ℚ)] {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ)
    (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
    (t₁ t₂ : (v.adicCompletion ℚ)ˣ) (g : LocalGL2 v) :
    ∫⁻ y, ‖f (antidiagonal2 v * upperUnipotent2 v y * (diagonal2 v ![t₁, t₂] * g))‖ₑ ∂ν =
      ENNReal.ofReal (‖((χ 0 t₂ : ℂˣ) : ℂ)‖ * ‖((χ 1 t₁ : ℂˣ) : ℂ)‖ *
          Real.sqrt (‖(t₁ : v.adicCompletion ℚ)‖ / ‖(t₂ : v.adicCompletion ℚ)‖)) *
        ∫⁻ y, ‖f (antidiagonal2 v * upperUnipotent2 v y * g)‖ₑ ∂ν := by
  obtain ⟨-, -, ht⟩ := mem_principalSeries2_iff.mp hf
  set u : (v.adicCompletion ℚ)ˣ := t₂ * t₁⁻¹ with hu
  have hpt : ∀ y : v.adicCompletion ℚ,
      ‖f (antidiagonal2 v * upperUnipotent2 v y * (diagonal2 v ![t₁, t₂] * g))‖ₑ =
        ENNReal.ofReal ‖torusChar2 v χ ![t₂, t₁] * halfModulus2 v ![t₂, t₁]‖ *
          (fun z => ‖f (antidiagonal2 v * upperUnipotent2 v z * g)‖ₑ)
            ((u : v.adicCompletion ℚ) * y) := by
    intro y
    simp only
    rw [← mul_assoc, weyl_upper_diag v y t₁ t₂, mul_assoc, ht, eNorm_mul, ofReal_norm]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_units_mul ν ϖ hϖ u
      (fun z => ‖f (antidiagonal2 v * upperUnipotent2 v z * g)‖ₑ), ← mul_assoc]
  congr 1
  have h1 : 0 < ‖(t₁ : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr t₁.ne_zero
  have h2 : 0 < ‖(t₂ : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr t₂.ne_zero
  have hmod : ((‖(u : v.adicCompletion ℚ)‖₊ : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (‖(t₁ : v.adicCompletion ℚ)‖ / ‖(t₂ : v.adicCompletion ℚ)‖) := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm, hu, Units.val_mul, Units.val_inv_eq_inv_val,
      norm_mul, norm_inv, ← ENNReal.ofReal_inv_of_pos (mul_pos h2 (inv_pos.mpr h1))]
    congr 1
    field_simp
  rw [hmod, norm_torus_factor, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hr : 0 < ‖(t₂ : v.adicCompletion ℚ)‖ / ‖(t₁ : v.adicCompletion ℚ)‖ := div_pos h2 h1
  have hs : Real.sqrt (‖(t₂ : v.adicCompletion ℚ)‖ / ‖(t₁ : v.adicCompletion ℚ)‖) *
      (‖(t₁ : v.adicCompletion ℚ)‖ / ‖(t₂ : v.adicCompletion ℚ)‖) =
        Real.sqrt (‖(t₁ : v.adicCompletion ℚ)‖ / ‖(t₂ : v.adicCompletion ℚ)‖) := by
    rw [show ‖(t₁ : v.adicCompletion ℚ)‖ / ‖(t₂ : v.adicCompletion ℚ)‖ =
        (‖(t₂ : v.adicCompletion ℚ)‖ / ‖(t₁ : v.adicCompletion ℚ)‖)⁻¹ by rw [inv_div],
      Real.sqrt_inv]
    have hsq : Real.sqrt (‖(t₂ : v.adicCompletion ℚ)‖ / ‖(t₁ : v.adicCompletion ℚ)‖) ≠ 0 :=
      (Real.sqrt_pos.mpr hr).ne'
    field_simp
    rw [Real.sq_sqrt hr.le]
    field_simp
  rw [mul_assoc _ (Real.sqrt _), hs]

private theorem isCompact_setOf_integral :
    IsCompact {g : LocalGL2 v |
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
        v.adicCompletionIntegers ℚ) ∧
      ∀ i j, ((g⁻¹ : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
        v.adicCompletionIntegers ℚ} := by
  set C : Set (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
    {m | ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
        (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_integers
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (hC.image MulOpposite.continuous_op))
  convert hK using 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    Set.mem_image, hC_def]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, _, h2, rfl⟩
  · rintro ⟨h1, m, hm, hm'⟩
    refine ⟨h1, ?_⟩
    have : m = ((g⁻¹ : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
      MulOpposite.op_injective hm'
    rw [← this]; exact hm

private theorem exists_bound_jacquet [MeasurableSpace (v.adicCompletion ℚ)]
    [BorelSpace (v.adicCompletion ℚ)] (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v (cχ i), χ i u = 1)
    {ϖ : (v.adicCompletion ℚ)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hdom : ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖)
    {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ)
    (hfsm : ∃ U : Subgroup (LocalGL2 v), IsOpen (U : Set (LocalGL2 v)) ∧
      ∀ k ∈ U, ∀ g : LocalGL2 v, f (g * k) = f g)
    (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure] :
    ∃ C : ℝ≥0, ∀ k ∈ AdelicLevel.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      ∫⁻ y, ‖f (antidiagonal2 v * upperUnipotent2 v y * k)‖ₑ ∂ν ≤ C := by
  obtain ⟨U, hU, hfU⟩ := hfsm
  set J : LocalGL2 v → ℝ≥0∞ := fun g =>
    ∫⁻ y, ‖f (antidiagonal2 v * upperUnipotent2 v y * g)‖ₑ ∂ν with hJ
  have hJlc : IsLocallyConstant J := by
    refine (IsLocallyConstant.iff_exists_open _).mpr fun x => ?_
    refine ⟨(fun h => x⁻¹ * h) ⁻¹' (U : Set (LocalGL2 v)),
      hU.preimage (continuous_const.mul continuous_id), by simp, fun y hy => ?_⟩
    have hxy : y = x * (x⁻¹ * y) := by rw [mul_inv_cancel_left]
    rw [hxy, hJ]
    simp_rw [← mul_assoc _ x, hfU _ hy]
  set S := {g : LocalGL2 v |
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
        v.adicCompletionIntegers ℚ) ∧
      ∀ i j, ((g⁻¹ : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
        v.adicCompletionIntegers ℚ} with hS
  have h1S : (1 : LocalGL2 v) ∈ S := by
    have h := (AdelicLevel.mem_localLevelOne_iff (R := 𝓞 ℚ) (K := ℚ) (v := v) (N := ⊤)).mp
      (Subgroup.one_mem _)
    exact ⟨h.1.integral, h.2.integral⟩
  obtain ⟨x₀, -, hmax⟩ := isCompact_setOf_integral.exists_isMaxOn ⟨1, h1S⟩
    hJlc.continuous.continuousOn
  refine ⟨(J x₀).toNNReal, fun k hk => ?_⟩
  rw [ENNReal.coe_toNNReal (jacquet_lt_top χ cχ hcχ hϖ hdom hf ν x₀).ne]
  have hk' := AdelicLevel.mem_localLevelOne_iff.mp hk
  exact hmax ⟨hk'.1.integral, hk'.2.integral⟩

-- Compared with the upstream statement: the source fixes the Borel σ-algebra on `F`; here any
-- σ-algebra making `F` a Borel space is allowed, which includes the source's. The source's
-- `AdelicDock.localLevelOne` is restated as `NumberField.AdelicLevel.localLevelOne`, with the
-- same definition.
variable (v) in
/-- **Absolute Jacquet integral on the principal series of `GL₂(ℚ_p)`.** Let `v` be a finite
place of `ℚ`, `F = ℚ_v`, and let `χ₀, χ₁ : Fˣ → ℂˣ` be characters trivial on the higher unit
groups `higherUnitsAt ℚ v (cχ i)`. Let `ϖ` have valuation `exp (-1)` and assume
`‖χ₀(ϖ)‖ < ‖χ₁(ϖ)‖`. Let `f` lie in `principalSeries2 v χ` and be right invariant under some open
subgroup, and let `w₀ = !![0, 1; 1, 0]`. Then, for the Borel σ-algebra on `F` and every additive
Haar measure `ν` on `F`, the integral `J(g) = ∫⁻ y, ‖f (w₀ * unipotentGL2 y * g)‖ₑ ∂ν`

* is finite for every `g`;
* satisfies `J(unipotentGL2 x * g) = J(g)`;
* satisfies `J(diag(t₁, t₂) * g) = ‖χ₀(t₂)‖ ‖χ₁(t₁)‖ √(‖t₁‖ / ‖t₂‖) J(g)`;
* is bounded on the local level-one subgroup `AdelicLevel.localLevelOne (𝓞 ℚ) ℚ v ⊤`. -/
public theorem
    absoluteJacquetIntegral_lt_top_and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2
    [MeasurableSpace (v.adicCompletion ℚ)] [BorelSpace (v.adicCompletion ℚ)]
    (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v (cχ i), χ i u = 1)
    (ϖ : (v.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hdom : ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖)
    (f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 v χ)
    (hfsm : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion ℚ), f (g * k) = f g)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    ∀ (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        ∫⁻ y, ‖f (w₀ * AutomorphicForm.unipotentGL2 y * g)‖ₑ ∂ν < ∞) ∧
      (∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
        ∫⁻ y, ‖f (w₀ * AutomorphicForm.unipotentGL2 y *
            (AutomorphicForm.unipotentGL2 x * g))‖ₑ ∂ν =
          ∫⁻ y, ‖f (w₀ * AutomorphicForm.unipotentGL2 y * g)‖ₑ ∂ν) ∧
      (∀ (t₁ t₂ : (v.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
        ∫⁻ y, ‖f (w₀ * AutomorphicForm.unipotentGL2 y * (diagonal2 v ![t₁, t₂] * g))‖ₑ ∂ν =
          ENNReal.ofReal (‖((χ 0 t₂ : ℂˣ) : ℂ)‖ * ‖((χ 1 t₁ : ℂˣ) : ℂ)‖ *
              Real.sqrt (‖(t₁ : v.adicCompletion ℚ)‖ / ‖(t₂ : v.adicCompletion ℚ)‖)) *
            ∫⁻ y, ‖f (w₀ * AutomorphicForm.unipotentGL2 y * g)‖ₑ ∂ν) ∧
      (∃ C : ℝ≥0, ∀ k ∈ AdelicLevel.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∫⁻ y, ‖f (w₀ * AutomorphicForm.unipotentGL2 y * k)‖ₑ ∂ν ≤ C) := by
  intro ν _
  obtain rfl := eq_antidiagonal2 v w₀ hw₀
  simp_rw [unipotentGL2_eq v]
  exact ⟨fun g => jacquet_lt_top χ cχ hcχ hϖ hdom hf ν g,
    fun x g => jacquet_upper_mul ν f x g, fun t₁ t₂ g => jacquet_diag_mul χ hϖ hf ν t₁ t₂ g,
    exists_bound_jacquet χ cχ hcχ hϖ hdom hf hfsm ν⟩

end Jacquet


end LanglandsTunnell.CubicInduction

end
