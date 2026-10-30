/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecificLimits.Normed
public import MathlibExt.Analysis.InnerProductSpace.RieszBasis

@[expose] public section

/-!
# Paley–Wiener stability of Hilbert bases

A Hilbert basis survives a small perturbation: if `b` is a Hilbert basis and
the perturbation `d i = f i - b i` satisfies `∑' i, ‖d i‖ ^ 2 < 1`, then `f`
is a Riesz basis. This is the classical **Paley–Wiener stability theorem**
(Paley–Wiener, *Fourier Transforms in the Complex Domain*, 1934); see also
Christensen, *An Introduction to Frames and Riesz Bases*, Theorem 5.3.1 (in
the form `∑ ‖f i - b i‖ ^ 2 < 1`).

The proof follows the standard route: the perturbation operator
`S x = ∑' i, ⟪b i, x⟫ • (f i - b i)` has operator norm at most
`√(∑' i, ‖f i - b i‖ ^ 2) < 1` by Cauchy–Schwarz for `ℓ²` (here
`lp.tsum_mul_le_mul_norm`), so `T = 1 + S` is a unit by the Neumann-series
criterion `IsUnit.one_sub_of_norm_lt_one`, and `T (b i) = f i`.

This is a companion to the v1 book's Hilbert-space material
(`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`): the book
treats orthonormal bases, but none of its 72 targets states the Paley–Wiener
stability theorem or anything about Riesz bases.

Main results:

* `synthesisCLM`: the synthesis operator `c ↦ ∑' i, c i • d i` from
  `ℓ²(ι, 𝕜)` to `E`, for a square-summable family `d`.
* `norm_synthesisCLM_le`: `‖synthesisCLM d hd‖ ≤ √(∑' i, ‖d i‖ ^ 2)`.
* `isRieszBasis_of_tsum_norm_sq_lt_one`: the Paley–Wiener stability theorem.
-/

section

variable {ι 𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

open scoped lp InnerProductSpace ENNReal

namespace MathlibExt.Analysis.InnerProductSpace.RieszBasisStability

open MathlibExt.Analysis.InnerProductSpace.RieszBasis

/-- The sequence of norms of a square-summable family, as an element of
`ℓ²(ι, ℝ)`. -/
noncomputable def normSeq (d : ι → E) (hd : Summable fun i => ‖d i‖ ^ 2) :
    ℓ²(ι, ℝ) :=
  ⟨fun i => ‖d i‖, by
    show Memℓp (fun i => ‖d i‖) (2 : ℝ≥0∞)
    rw [memℓp_gen_iff (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    have hni : ∀ i, |(‖d i‖ : ℝ)| = ‖d i‖ :=
      fun i => abs_of_nonneg (norm_nonneg _)
    simpa only [Real.norm_eq_abs, hni, ENNReal.toReal_ofNat, Real.rpow_two] using hd⟩

omit [CompleteSpace E] in
theorem norm_normSeq_apply (d : ι → E)
    (hd : Summable fun i => ‖d i‖ ^ 2) (i : ι) :
    ‖(normSeq d hd) i‖ = ‖d i‖ := by
  show ‖(‖d i‖ : ℝ)‖ = ‖d i‖
  exact Real.norm_of_nonneg (norm_nonneg _)

omit [CompleteSpace E] in
theorem norm_normSeq (d : ι → E) (hd : Summable fun i => ‖d i‖ ^ 2) :
    ‖normSeq d hd‖ = Real.sqrt (∑' i, ‖d i‖ ^ 2) := by
  have htsum : (∑' i, ‖(normSeq d hd) i‖ ^ (2 : ℝ≥0∞).toReal)
      = ∑' i, ‖d i‖ ^ 2 := by
    refine tsum_congr fun i => ?_
    show (‖(‖d i‖ : ℝ)‖) ^ (2 : ℝ≥0∞).toReal = ‖d i‖ ^ 2
    rw [Real.norm_of_nonneg (norm_nonneg _),
      show (2 : ℝ≥0∞).toReal = (2 : ℝ) by simp, Real.rpow_two]
  rw [lp.norm_eq_tsum_rpow (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal), htsum,
    show (1 : ℝ) / (2 : ℝ≥0∞).toReal = 1 / 2 by simp, Real.sqrt_eq_rpow]

/-- The sequence of norms of an `ℓ²` coefficient sequence, as an element of
`ℓ²(ι, ℝ)`. -/
noncomputable def normSeqLp (c : ℓ²(ι, 𝕜)) : ℓ²(ι, ℝ) :=
  ⟨fun i => ‖c i‖, (lp.memℓp c).norm⟩

theorem normSeqLp_apply (c : ℓ²(ι, 𝕜)) (i : ι) :
    (normSeqLp c) i = ‖c i‖ :=
  rfl

/-- The `ℓ²` norm of the norms of a coefficient sequence is the norm of the
sequence. -/
theorem norm_normSeqLp (c : ℓ²(ι, 𝕜)) : ‖normSeqLp c‖ = ‖c‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (normSeqLp c),
    lp.norm_eq_tsum_rpow (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) c]
  congr 1
  refine tsum_congr fun i => ?_
  show (‖(‖c i‖ : ℝ)‖) ^ (2 : ℝ≥0∞).toReal = ‖c i‖ ^ (2 : ℝ≥0∞).toReal
  rw [Real.norm_of_nonneg (norm_nonneg _)]

omit [CompleteSpace E] in
/-- The norms of the terms of a synthesis series are summable when the
coefficient sequence is in `ℓ²` and the synthesized family is square-summable:
this is Cauchy–Schwarz for `ℓ²`, via `lp.tsum_mul_le_mul_norm` applied to the
two real `ℓ²` sequences of norms. -/
theorem summable_norm_synthesis (d : ι → E)
    (hd : Summable fun i => ‖d i‖ ^ 2) (c : ℓ²(ι, 𝕜)) :
    Summable fun i => ‖c i • d i‖ := by
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa using Real.HolderConjugate.two_two
  have h := (lp.tsum_mul_le_mul_norm hpq (normSeqLp c) (normSeq d hd)).1
  have h2 : (fun i => ‖c i • d i‖)
      = fun i => ‖(normSeqLp c) i‖ * ‖(normSeq d hd) i‖ := by
    funext i
    rw [norm_smul, normSeqLp_apply, norm_normSeq_apply,
      Real.norm_of_nonneg (show (0 : ℝ) ≤ ‖c i‖ from norm_nonneg _)]
  rw [h2]
  exact h

/-- The terms of a synthesis series are summable when the coefficient sequence
is in `ℓ²` and the synthesized family is square-summable. -/
theorem summable_synthesis (d : ι → E) (hd : Summable fun i => ‖d i‖ ^ 2)
    (c : ℓ²(ι, 𝕜)) : Summable fun i => c i • d i :=
  Summable.of_norm (summable_norm_synthesis d hd c)

omit [CompleteSpace E] in
/-- Norm bound for a synthesis series, by Cauchy–Schwarz for `ℓ²`. -/
theorem norm_tsum_smul_le (d : ι → E) (hd : Summable fun i => ‖d i‖ ^ 2)
    (c : ℓ²(ι, 𝕜)) :
    ‖∑' i, c i • d i‖ ≤ Real.sqrt (∑' i, ‖d i‖ ^ 2) * ‖c‖ := by
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa using Real.HolderConjugate.two_two
  have h := (lp.tsum_mul_le_mul_norm hpq (normSeqLp c) (normSeq d hd)).2
  calc ‖∑' i, c i • d i‖ ≤ ∑' i, ‖c i • d i‖ :=
        norm_tsum_le_tsum_norm (summable_norm_synthesis d hd c)
    _ = ∑' i, ‖(normSeqLp c) i‖ * ‖(normSeq d hd) i‖ := by
        refine tsum_congr fun i => ?_
        rw [norm_smul, normSeqLp_apply, norm_normSeq_apply,
          Real.norm_of_nonneg (show (0 : ℝ) ≤ ‖c i‖ from norm_nonneg _)]
    _ ≤ ‖normSeqLp c‖ * ‖normSeq d hd‖ := h
    _ = Real.sqrt (∑' i, ‖d i‖ ^ 2) * ‖c‖ := by
        rw [norm_normSeq, norm_normSeqLp]
        ring

/-- The linear map underlying the synthesis operator. -/
noncomputable def synthesisLinearMap (d : ι → E)
    (hd : Summable fun i => ‖d i‖ ^ 2) :
    ℓ²(ι, 𝕜) →ₗ[𝕜] E where
  toFun c := ∑' i, c i • d i
  map_add' c c' := by
    rw [← Summable.tsum_add (summable_synthesis d hd c) (summable_synthesis d hd c')]
    refine tsum_congr fun i => ?_
    simp [add_smul]
  map_smul' a c := by
    simp only [RingHom.id_apply]
    rw [← (summable_synthesis d hd c).tsum_const_smul a]
    refine tsum_congr fun i => ?_
    simp [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]

/-- The **synthesis operator**: for a square-summable family `d : ι → E`, the
bounded operator `ℓ²(ι, 𝕜) →L[𝕜] E` sending `c` to `∑' i, c i • d i`. -/
noncomputable def synthesisCLM (d : ι → E) (hd : Summable fun i => ‖d i‖ ^ 2) :
    ℓ²(ι, 𝕜) →L[𝕜] E :=
  LinearMap.mkContinuous (synthesisLinearMap d hd) _
    fun c => norm_tsum_smul_le d hd c

@[simp]
theorem synthesisCLM_apply (d : ι → E) (hd : Summable fun i => ‖d i‖ ^ 2)
    (c : ℓ²(ι, 𝕜)) : synthesisCLM (𝕜 := 𝕜) d hd c = ∑' i, c i • d i :=
  rfl

/-- The operator norm of the synthesis operator is at most
`√(∑' i, ‖d i‖ ^ 2)`. -/
theorem norm_synthesisCLM_le (d : ι → E) (hd : Summable fun i => ‖d i‖ ^ 2) :
    ‖synthesisCLM (𝕜 := 𝕜) d hd‖ ≤ Real.sqrt (∑' i, ‖d i‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound (synthesisCLM (𝕜 := 𝕜) d hd)
    (Real.sqrt_nonneg _) fun c => ?_
  rw [synthesisCLM_apply]
  exact norm_tsum_smul_le d hd c

/-- The synthesis operator at a basis vector picks out one term of the
family. -/
theorem synthesisCLM_single (d : ι → E) (hd : Summable fun i => ‖d i‖ ^ 2)
    [DecidableEq ι] (i : ι) :
    synthesisCLM (𝕜 := 𝕜) d hd (lp.single 2 i (1 : 𝕜)) = d i := by
  classical
  rw [synthesisCLM_apply]
  have hfun : (fun j => ((lp.single 2 i (1 : 𝕜) : ℓ²(ι, 𝕜)) j) • d j)
      = fun j => if j = i then d i else 0 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [hfun]
  exact (hasSum_ite_eq i (d i)).tsum_eq

/-- **Paley–Wiener stability theorem.** If `b` is a Hilbert basis and
`∑' i, ‖f i - b i‖ ^ 2 < 1`, then `f` is a Riesz basis. -/
theorem isRieszBasis_of_tsum_norm_sq_lt_one (b : HilbertBasis ι 𝕜 E) (f : ι → E)
    (hd : Summable fun i => ‖f i - b i‖ ^ 2)
    (h : ∑' i, ‖f i - b i‖ ^ 2 < 1) : IsRieszBasis b f := by
  classical
  set d : ι → E := fun i => f i - b i with hd_def
  set S : E →L[𝕜] E :=
    synthesisCLM (𝕜 := 𝕜) d hd ∘L (b.repr.toContinuousLinearEquiv : E →L[𝕜] ℓ²(ι, 𝕜))
      with hS_def
  set T : E →L[𝕜] E := 1 + S with hT_def
  have hS_norm : ‖S‖ ≤ Real.sqrt (∑' i, ‖f i - b i‖ ^ 2) := by
    calc ‖S‖ ≤ ‖synthesisCLM d hd‖
          * ‖(b.repr.toContinuousLinearEquiv : E →L[𝕜] ℓ²(ι, 𝕜))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Real.sqrt (∑' i, ‖f i - b i‖ ^ 2) * 1 := by
          gcongr
          · exact norm_synthesisCLM_le d hd
          · exact ContinuousLinearMap.opNorm_le_bound
              (f := (b.repr.toContinuousLinearEquiv : E →L[𝕜] ℓ²(ι, 𝕜))) zero_le_one
              fun x => by
                have hx : ‖(b.repr.toContinuousLinearEquiv : E →L[𝕜] ℓ²(ι, 𝕜)) x‖ = ‖x‖ :=
                  LinearIsometryEquiv.norm_map b.repr x
                rw [hx, one_mul]
      _ = Real.sqrt (∑' i, ‖f i - b i‖ ^ 2) := mul_one _
  have hsqrt : Real.sqrt (∑' i, ‖f i - b i‖ ^ 2) < 1 := by
    have h1 : Real.sqrt (∑' i, ‖f i - b i‖ ^ 2) < Real.sqrt 1 :=
      Real.sqrt_lt_sqrt (by positivity) h
    simpa using h1
  have hT_norm : ‖1 - T‖ < 1 := by
    have hsub : (1 : E →L[𝕜] E) - T = -S := by
      rw [hT_def]
      simp
    rw [hsub, norm_neg]
    exact lt_of_le_of_lt hS_norm hsqrt
  have hunit : IsUnit T := by
    have h1 : IsUnit (1 - (1 - T)) := IsUnit.one_sub_of_norm_lt_one hT_norm
    simpa using h1
  have hbij : Function.Bijective T :=
    (ContinuousLinearMap.isUnit_iff_bijective).mp hunit
  set Te : E ≃L[𝕜] E :=
    ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2) with hTe_def
  refine ⟨Te, fun i => ?_⟩
  have hTe_apply : Te (b i) = T (b i) := by
    rw [hTe_def]
    exact congrFun (ContinuousLinearEquiv.coeFn_ofBijective T _ _) (b i)
  rw [hTe_apply, hT_def]
  simp only [add_apply, one_apply_eq_self]
  rw [hS_def]
  simp only [ContinuousLinearMap.comp_apply]
  have hrepr : (b.repr.toContinuousLinearEquiv : E →L[𝕜] ℓ²(ι, 𝕜)) (b i)
      = lp.single 2 i (1 : 𝕜) :=
    b.repr_self i
  rw [hrepr, synthesisCLM_single]
  show b i + (f i - b i) = f i
  exact add_sub_cancel _ _

end MathlibExt.Analysis.InnerProductSpace.RieszBasisStability

end
