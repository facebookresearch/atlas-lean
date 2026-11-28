/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.UniformSpace.Uniformizable
import MathlibExt.Probability.Distributions.ChiSquare

@[expose] public section

open scoped RealInnerProductSpace
open ProbabilityTheory MeasureTheory

-- `mgf_sq_stdGaussian` and `integrable_exp_mul_sq_stdGaussian` now live in
-- `MathlibExt.Probability.Distributions.ChiSquare` and are reused below.

private theorem mgf_sum_sq_pi (d : ℕ) (t : ℝ) :
    mgf (fun ω : Fin d → ℝ => ∑ i, (ω i) ^ 2)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) t =
      (Real.sqrt (1 - 2 * t))⁻¹ ^ d := by
  let X : Fin d → (Fin d → ℝ) → ℝ := fun i ω => (ω i) ^ 2
  have hIndep : iIndepFun X (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    exact iIndepFun_pi (μ := fun _ : Fin d => gaussianReal 0 1)
      (X := fun _ x => x ^ 2) (fun _ => by fun_prop)
  have hMeas : ∀ i, Measurable (X i) := by
    intro i
    fun_prop
  have hfun : (fun ω : Fin d → ℝ => ∑ i, (ω i) ^ 2) = ∑ i ∈ Finset.univ, X i := by
    funext ω
    simp [X]
  rw [hfun, hIndep.mgf_sum hMeas Finset.univ]
  calc
    (∏ i ∈ Finset.univ, mgf (X i)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) t) =
        ∏ _i : Fin d, (Real.sqrt (1 - 2 * t))⁻¹ := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [mgf_congr_of_identDistrib (X i) (fun x : ℝ => x ^ 2) _ t]
      · exact mgf_sq_stdGaussian t
      · simpa [X, Function.comp_def] using
          ((measurePreserving_eval
            (fun _ : Fin d => gaussianReal 0 1) i).hasLaw.identDistrib
              (HasLaw.id : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1))).comp
                (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
    _ = (Real.sqrt (1 - 2 * t))⁻¹ ^ d := by simp

private theorem integrable_exp_mul_sum_sq_pi (d : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun ω : Fin d → ℝ =>
      Real.exp (t * ∑ i, (ω i) ^ 2))
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  let X : Fin d → (Fin d → ℝ) → ℝ := fun i ω => (ω i) ^ 2
  have hIndep : iIndepFun X (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    exact iIndepFun_pi (μ := fun _ : Fin d => gaussianReal 0 1)
      (X := fun _ x => x ^ 2) (fun _ => by fun_prop)
  have hMeas : ∀ i, Measurable (X i) := by
    intro i
    fun_prop
  have hInt : ∀ i ∈ Finset.univ,
      Integrable (fun ω : Fin d → ℝ => Real.exp (t * X i ω))
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    intro i _hi
    simpa [X, Function.comp_def] using
      (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i).integrable_comp_of_integrable
        (integrable_exp_mul_sq_stdGaussian ht)
  simpa [X] using
    hIndep.integrable_exp_mul_sum hMeas (s := Finset.univ) hInt

private theorem sum_sq_pi_upper_chernoff (d : ℕ) (ε t : ℝ)
    (ht0 : 0 ≤ t) (ht : t < 1 / 2) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
        {ω | (d : ℝ) * (1 + ε) ≤ ∑ i, (ω i) ^ 2} ≤
      Real.exp (-t * ((d : ℝ) * (1 + ε))) *
        (Real.sqrt (1 - 2 * t))⁻¹ ^ d := by
  calc
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
        {ω | (d : ℝ) * (1 + ε) ≤ ∑ i, (ω i) ^ 2} ≤
        Real.exp (-t * ((d : ℝ) * (1 + ε))) *
          mgf (fun ω : Fin d → ℝ => ∑ i, (ω i) ^ 2)
            (Measure.pi fun _ : Fin d => gaussianReal 0 1) t :=
      measure_ge_le_exp_mul_mgf _ ht0 (integrable_exp_mul_sum_sq_pi d ht)
    _ = _ := by rw [mgf_sum_sq_pi]

private theorem sum_sq_pi_lower_chernoff (d : ℕ) (ε t : ℝ)
    (ht : t ≤ 0) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
        {ω | (∑ i, (ω i) ^ 2) ≤ (d : ℝ) * (1 - ε)} ≤
      Real.exp (-t * ((d : ℝ) * (1 - ε))) *
        (Real.sqrt (1 - 2 * t))⁻¹ ^ d := by
  have ht' : t < 1 / 2 := by linarith
  calc
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
        {ω | (∑ i, (ω i) ^ 2) ≤ (d : ℝ) * (1 - ε)} ≤
        Real.exp (-t * ((d : ℝ) * (1 - ε))) *
          mgf (fun ω : Fin d → ℝ => ∑ i, (ω i) ^ 2)
            (Measure.pi fun _ : Fin d => gaussianReal 0 1) t :=
      measure_le_le_exp_mul_mgf _ ht (integrable_exp_mul_sum_sq_pi d ht')
    _ = _ := by rw [mgf_sum_sq_pi]

private theorem neg_log_one_sub_le_add_two_sq {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 4) :
    -Real.log (1 - u) ≤ u + 2 * u ^ 2 := by
  have habs : |u| < 1 := by rw [abs_of_nonneg hu0]; linarith
  have hTaylor := Real.abs_log_sub_add_sum_range_le habs 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, zero_add, pow_one, div_one] at hTaylor
  rw [abs_of_nonneg hu0] at hTaylor
  have hden : 0 < 1 - u := by linarith
  have hquot : u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg u]
  have hneg : -(u + Real.log (1 - u)) ≤ |u + Real.log (1 - u)| :=
    neg_le_abs _
  linarith

private theorem sqrt_inv_pow_eq_exp (d : ℕ) {a : ℝ} (ha : 0 < a) :
    (Real.sqrt a)⁻¹ ^ d =
      Real.exp (-((d : ℝ) / 2) * Real.log a) := by
  calc
    (Real.sqrt a)⁻¹ ^ d = Real.exp (-Real.log (Real.sqrt a)) ^ d := by
      rw [Real.exp_neg, Real.exp_log (Real.sqrt_pos.2 ha)]
    _ = Real.exp ((d : ℝ) * (-Real.log (Real.sqrt a))) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (-((d : ℝ) / 2) * Real.log a) := by
      rw [Real.log_sqrt ha.le]
      congr 1
      ring_nf

private theorem sum_sq_pi_upper_tail (d : ℕ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
        {ω | (d : ℝ) * (1 + ε) ≤ ∑ i, (ω i) ^ 2} ≤
      Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
  have ht0 : 0 ≤ ε / 8 := by positivity
  have ht : ε / 8 < 1 / 2 := by linarith
  have ha : 0 < 1 - 2 * (ε / 8) := by linarith
  have hu : ε / 4 ≤ 1 / 4 := by linarith
  have hlog := neg_log_one_sub_le_add_two_sq (u := ε / 4) (by positivity) hu
  calc
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
        {ω | (d : ℝ) * (1 + ε) ≤ ∑ i, (ω i) ^ 2} ≤
        Real.exp (-(ε / 8) * ((d : ℝ) * (1 + ε))) *
          (Real.sqrt (1 - 2 * (ε / 8)))⁻¹ ^ d :=
      sum_sq_pi_upper_chernoff d ε (ε / 8) ht0 ht
    _ = Real.exp (-(ε / 8) * ((d : ℝ) * (1 + ε)) -
          ((d : ℝ) / 2) * Real.log (1 - ε / 4)) := by
      rw [sqrt_inv_pow_eq_exp d ha, ← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
      apply Real.exp_le_exp.mpr
      have hd : 0 ≤ (d : ℝ) := by positivity
      nlinarith

private theorem sub_sq_le_log_one_add {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 2 ≤ Real.log (1 + u) := by
  have hpos : 0 < 1 + u := by linarith
  have hbase := Real.one_sub_inv_le_log_of_pos hpos
  have hid : 1 - (1 + u)⁻¹ = u / (1 + u) := by
    field_simp
    ring
  rw [hid] at hbase
  apply le_trans ?_ hbase
  rw [le_div_iff₀ hpos]
  nlinarith [mul_nonneg hu (sq_nonneg u)]

private theorem sum_sq_pi_lower_tail (d : ℕ) {ε : ℝ}
    (hε0 : 0 ≤ ε) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
        {ω | (∑ i, (ω i) ^ 2) ≤ (d : ℝ) * (1 - ε)} ≤
      Real.exp (-((d : ℝ) * ε ^ 2 / 8)) := by
  have ht : -(ε / 4) ≤ 0 := neg_nonpos.mpr (div_nonneg hε0 (by norm_num))
  have ha : 0 < 1 - 2 * (-(ε / 4)) := by linarith
  have hlog := sub_sq_le_log_one_add (u := ε / 2)
    (div_nonneg hε0 (by norm_num))
  calc
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
        {ω | (∑ i, (ω i) ^ 2) ≤ (d : ℝ) * (1 - ε)} ≤
        Real.exp (-(-(ε / 4)) * ((d : ℝ) * (1 - ε))) *
          (Real.sqrt (1 - 2 * (-(ε / 4))))⁻¹ ^ d :=
      sum_sq_pi_lower_chernoff d ε (-(ε / 4)) ht
    _ = Real.exp (-(-(ε / 4)) * ((d : ℝ) * (1 - ε)) -
          ((d : ℝ) / 2) * Real.log (1 + ε / 2)) := by
      rw [sqrt_inv_pow_eq_exp d ha, ← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ Real.exp (-((d : ℝ) * ε ^ 2 / 8)) := by
      apply Real.exp_le_exp.mpr
      have hd : 0 ≤ (d : ℝ) := by positivity
      nlinarith

section ProjectionRows

private theorem stdGaussian_unit_projection_law
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (anchor : E) (hAnchorNorm : ‖anchor‖ = 1) :
    (stdGaussian E).map (innerSL ℝ anchor) = gaussianReal 0 1 := by
  have hMean :
      ∫ sample, (innerSL ℝ anchor) sample ∂stdGaussian E = 0 := by
    simpa using
      (integral_strongDual_stdGaussian (L := innerSL ℝ anchor))
  have hVar :
      Var[fun sample => (innerSL ℝ anchor) sample; stdGaussian E].toNNReal =
        1 := by
    have hVarReal :
        Var[fun sample => (innerSL ℝ anchor) sample; stdGaussian E] =
          1 := by
      calc
        Var[fun sample => (innerSL ℝ anchor) sample; stdGaussian E]
            = ‖innerSL ℝ anchor‖ ^ 2 :=
          variance_dual_stdGaussian (L := innerSL ℝ anchor)
        _ = 1 := by
          simp [innerSL_apply_norm, hAnchorNorm]
    rw [hVarReal]
    norm_num
  rw [IsGaussian.map_eq_gaussianReal
    (μ := stdGaussian E)
    (L := innerSL ℝ anchor)]
  rw [hMean, hVar]

private noncomputable def rowProjection {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (anchor : E) : (Fin d → E) → (Fin d → ℝ) :=
  fun rows i => (innerSL ℝ anchor) (rows i)

private theorem rowProjection_law
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) (anchor : E) (hAnchorNorm : ‖anchor‖ = 1) :
    (Measure.pi fun _ : Fin d => stdGaussian E).map (rowProjection d anchor) =
      Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  unfold rowProjection
  rw [Measure.pi_map_pi (fun _ => (innerSL ℝ anchor).measurable.aemeasurable)]
  congr 1
  funext i
  exact stdGaussian_unit_projection_law anchor hAnchorNorm

private theorem rowProjection_upper_tail
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) (anchor : E) (hAnchorNorm : ‖anchor‖ = 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (Measure.pi fun _ : Fin d => stdGaussian E).real
        {rows | (d : ℝ) * (1 + ε) ≤
          ∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2} ≤
      Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
  have hm : Measurable (rowProjection d anchor) := by
    unfold rowProjection
    fun_prop
  have hLaw : HasLaw (rowProjection d anchor)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1)
      (Measure.pi fun _ : Fin d => stdGaussian E) :=
    ⟨hm.aemeasurable, rowProjection_law d anchor hAnchorNorm⟩
  have heq := hLaw.measureReal_eq
    (p := fun coords : Fin d → ℝ =>
      (d : ℝ) * (1 + ε) ≤ ∑ i, (coords i) ^ 2)
    (measurableSet_le measurable_const (by fun_prop))
  change (Measure.pi fun _ : Fin d => stdGaussian E).real
      {rows | (d : ℝ) * (1 + ε) ≤
        ∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2} =
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
      {coords | (d : ℝ) * (1 + ε) ≤ ∑ i, (coords i) ^ 2} at heq
  rw [heq]
  exact sum_sq_pi_upper_tail d hε0 hε1

private theorem rowProjection_lower_tail
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) (anchor : E) (hAnchorNorm : ‖anchor‖ = 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) :
    (Measure.pi fun _ : Fin d => stdGaussian E).real
        {rows | (∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2) ≤
          (d : ℝ) * (1 - ε)} ≤
      Real.exp (-((d : ℝ) * ε ^ 2 / 8)) := by
  have hm : Measurable (rowProjection d anchor) := by
    unfold rowProjection
    fun_prop
  have hLaw : HasLaw (rowProjection d anchor)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1)
      (Measure.pi fun _ : Fin d => stdGaussian E) :=
    ⟨hm.aemeasurable, rowProjection_law d anchor hAnchorNorm⟩
  have heq := hLaw.measureReal_eq
    (p := fun coords : Fin d → ℝ =>
      (∑ i, (coords i) ^ 2) ≤ (d : ℝ) * (1 - ε))
    (measurableSet_le (by fun_prop) measurable_const)
  change (Measure.pi fun _ : Fin d => stdGaussian E).real
      {rows | (∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2) ≤
        (d : ℝ) * (1 - ε)} =
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
      {coords | (∑ i, (coords i) ^ 2) ≤ (d : ℝ) * (1 - ε)} at heq
  rw [heq]
  exact sum_sq_pi_lower_tail d hε0

private def projectionFailure {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (ε : ℝ) (anchor : E) : Set (Fin d → E) :=
  {rows | (∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2) ≤
      (d : ℝ) * (1 - ε)} ∪
    {rows | (d : ℝ) * (1 + ε) ≤
      ∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2}

private theorem projectionFailure_measurable
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) (ε : ℝ) (anchor : E) :
    MeasurableSet (projectionFailure d ε anchor) := by
  apply MeasurableSet.union
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurableSet_le measurable_const (by fun_prop)

private theorem projectionFailure_real_le
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) (anchor : E) (hAnchorNorm : ‖anchor‖ = 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (Measure.pi fun _ : Fin d => stdGaussian E).real
        (projectionFailure d ε anchor) ≤
      2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
  calc
    (Measure.pi fun _ : Fin d => stdGaussian E).real
        (projectionFailure d ε anchor) ≤
        (Measure.pi fun _ : Fin d => stdGaussian E).real
          {rows | (∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2) ≤
            (d : ℝ) * (1 - ε)} +
        (Measure.pi fun _ : Fin d => stdGaussian E).real
          {rows | (d : ℝ) * (1 + ε) ≤
            ∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-((d : ℝ) * ε ^ 2 / 8)) +
        Real.exp (-((d : ℝ) * ε ^ 2 / 16)) :=
      add_le_add (rowProjection_lower_tail d anchor hAnchorNorm hε0)
        (rowProjection_upper_tail d anchor hAnchorNorm hε0 hε1)
    _ ≤ 2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
      have hd : 0 ≤ (d : ℝ) := by positivity
      have he : 0 ≤ ε ^ 2 := sq_nonneg ε
      have hExp : Real.exp (-((d : ℝ) * ε ^ 2 / 8)) ≤
          Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      nlinarith

private noncomputable def pairFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (ε : ℝ) (x y : E) : Set (Fin d → E) := by
  classical
  exact if x = y then ∅
    else projectionFailure d ε (‖x - y‖⁻¹ • (x - y))

private theorem pairFailure_measurable
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) (ε : ℝ) (x y : E) :
    MeasurableSet (pairFailure d ε x y) := by
  by_cases h : x = y
  · simp [pairFailure, h]
  · simp only [pairFailure, h, ↓reduceIte]
    exact projectionFailure_measurable d ε _

private theorem pairFailure_real_le
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x y : E) :
    (Measure.pi fun _ : Fin d => stdGaussian E).real
        (pairFailure d ε x y) ≤
      2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
  by_cases h : x = y
  · simp only [pairFailure, h, ↓reduceIte, measureReal_empty, Nat.ofNat_pos,
      mul_nonneg_iff_of_pos_left]
    positivity
  · simp only [pairFailure, h, ↓reduceIte]
    apply projectionFailure_real_le d _ _ hε0 hε1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))

private noncomputable def anyPairFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (ε : ℝ) (X : Finset E) : Set (Fin d → E) :=
  ⋃ x ∈ X, ⋃ y ∈ X, pairFailure d ε x y

private theorem anyPairFailure_measurable
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) (ε : ℝ) (X : Finset E) :
    MeasurableSet (anyPairFailure d ε X) := by
  unfold anyPairFailure
  exact X.measurableSet_biUnion fun x _hx =>
    X.measurableSet_biUnion fun y _hy => pairFailure_measurable d ε x y

private theorem anyPairFailure_real_le
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (X : Finset E) :
    (Measure.pi fun _ : Fin d => stdGaussian E).real
        (anyPairFailure d ε X) ≤
      (X.card : ℝ) ^ 2 *
        (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) := by
  unfold anyPairFailure
  calc
    (Measure.pi fun _ : Fin d => stdGaussian E).real
        (⋃ x ∈ X, ⋃ y ∈ X, pairFailure d ε x y) ≤
        ∑ x ∈ X, (Measure.pi fun _ : Fin d => stdGaussian E).real
          (⋃ y ∈ X, pairFailure d ε x y) :=
      measureReal_biUnion_finset_le X _
    _ ≤ ∑ x ∈ X, ∑ y ∈ X,
        (Measure.pi fun _ : Fin d => stdGaussian E).real
          (pairFailure d ε x y) := by
      gcongr with x hx
      exact measureReal_biUnion_finset_le X _
    _ ≤ ∑ _x ∈ X, ∑ _y ∈ X,
        2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
      gcongr with x hx y hy
      exact pairFailure_real_le d hε0 hε1 x y
    _ = (X.card : ℝ) ^ 2 *
        (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) := by
      simp
      ring

private theorem exists_rows_not_anyPairFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (X : Finset E)
    (hbound : (X.card : ℝ) ^ 2 *
      (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) < 1) :
    ∃ rows : Fin d → E, rows ∉ anyPairFailure d ε X := by
  by_contra h
  push Not at h
  have hset : anyPairFailure d ε X = Set.univ := Set.eq_univ_of_forall h
  have hle := anyPairFailure_real_le d hε0 hε1 X
  rw [hset] at hle
  have hone : (Measure.pi fun _ : Fin d => stdGaussian E).real Set.univ = 1 := by simp
  rw [hone] at hle
  linarith

private theorem dimension_implies_failure_bound {N d : ℕ} {ε : ℝ}
    (hN : N ≥ 2) (hε : ε > 0)
    (hd : (d : ℝ) > 64 * ε⁻¹ ^ 2 * Real.log (N : ℝ)) :
    (N : ℝ) ^ 2 * (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) < 1 := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hmul := mul_lt_mul_of_pos_right hd (show 0 < ε ^ 2 / 16 by positivity)
  have hexponent : 4 * Real.log (N : ℝ) < (d : ℝ) * ε ^ 2 / 16 := by
    calc
      4 * Real.log (N : ℝ) =
          (64 * ε⁻¹ ^ 2 * Real.log (N : ℝ)) * (ε ^ 2 / 16) := by
        field_simp
        ring
      _ < (d : ℝ) * (ε ^ 2 / 16) := hmul
      _ = (d : ℝ) * ε ^ 2 / 16 := by ring
  have hexp : Real.exp (-((d : ℝ) * ε ^ 2 / 16)) <
      ((N : ℝ)⁻¹) ^ 4 := by
    calc
      Real.exp (-((d : ℝ) * ε ^ 2 / 16)) <
          Real.exp (-(4 * Real.log (N : ℝ))) := by
        apply Real.exp_lt_exp.mpr
        linarith
      _ = Real.exp (-Real.log (N : ℝ)) ^ 4 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      _ = ((N : ℝ)⁻¹) ^ 4 := by rw [Real.exp_neg, Real.exp_log hNreal]
  have hcoef : 0 < (N : ℝ) ^ 2 * 2 := by positivity
  have hmulExp := mul_lt_mul_of_pos_left hexp hcoef
  calc
    (N : ℝ) ^ 2 * (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) =
        ((N : ℝ) ^ 2 * 2) * Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by ring
    _ < ((N : ℝ) ^ 2 * 2) * ((N : ℝ)⁻¹) ^ 4 := hmulExp
    _ ≤ 1 := by
      have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      field_simp
      nlinarith

private noncomputable def gaussianMap
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (rows : Fin d → E) : E → EuclideanSpace ℝ (Fin d) :=
  fun x => WithLp.toLp 2 (fun i => (Real.sqrt (d : ℝ))⁻¹ *
    (innerSL ℝ x) (rows i))

private theorem gaussianMap_sub
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (rows : Fin d → E) (x y : E) :
    gaussianMap d rows x - gaussianMap d rows y =
      WithLp.toLp 2 (fun i => (Real.sqrt (d : ℝ))⁻¹ *
        (innerSL ℝ (x - y)) (rows i)) := by
  ext i
  simp [gaussianMap]
  ring

private theorem gaussianMap_norm_sq_sub
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (hd : 0 < d) (rows : Fin d → E) (x y : E) :
    ‖gaussianMap d rows x - gaussianMap d rows y‖ ^ 2 =
      ((d : ℝ)⁻¹) * ∑ i, ((innerSL ℝ (x - y)) (rows i)) ^ 2 := by
  rw [gaussianMap_sub, EuclideanSpace.real_norm_sq_eq]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  congr 1
  rw [inv_pow, Real.sq_sqrt hdreal.le]

private theorem sum_inner_sq_eq_norm_sq_mul_normalized
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (rows : Fin d → E) {z : E} (hz : z ≠ 0) :
    (∑ i, ((innerSL ℝ z) (rows i)) ^ 2) =
      ‖z‖ ^ 2 *
        ∑ i, ((innerSL ℝ (‖z‖⁻¹ • z)) (rows i)) ^ 2 := by
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  calc
    (∑ i, ((innerSL ℝ z) (rows i)) ^ 2) =
        ∑ i, (‖z‖ * ((innerSL ℝ (‖z‖⁻¹ • z)) (rows i))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      congr 1
      simp only [innerSL_apply_apply, real_inner_smul_left]
      field_simp
    _ = ‖z‖ ^ 2 *
        ∑ i, ((innerSL ℝ (‖z‖⁻¹ • z)) (rows i)) ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]

private theorem gaussianMap_pair_bounds
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (hd : 0 < d) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (rows : Fin d → E) (x y : E)
    (hgood : rows ∉ pairFailure d ε x y) :
    (1 - ε) * ‖x - y‖ ≤ ‖gaussianMap d rows x - gaussianMap d rows y‖ ∧
      ‖gaussianMap d rows x - gaussianMap d rows y‖ ≤ (1 + ε) * ‖x - y‖ := by
  by_cases hxy : x = y
  · simp [hxy]
  · have hgood' : rows ∉
        projectionFailure d ε (‖x - y‖⁻¹ • (x - y)) := by
      simpa [pairFailure, hxy] using hgood
    have htails :
        ¬((∑ i, ((innerSL ℝ (‖x - y‖⁻¹ • (x - y))) (rows i)) ^ 2) ≤
            (d : ℝ) * (1 - ε)) ∧
        ¬((d : ℝ) * (1 + ε) ≤
            ∑ i, ((innerSL ℝ (‖x - y‖⁻¹ • (x - y))) (rows i)) ^ 2) := by
      simpa [projectionFailure] using hgood'
    have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
    let S : ℝ := ∑ i, ((innerSL ℝ (‖x - y‖⁻¹ • (x - y))) (rows i)) ^ 2
    have hSlower : 1 - ε < (d : ℝ)⁻¹ * S := by
      have h := lt_of_not_ge htails.1
      change (d : ℝ) * (1 - ε) < S at h
      have hm := mul_lt_mul_of_pos_left h (inv_pos.mpr hdreal)
      have hinv : (d : ℝ)⁻¹ * (d : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hdreal)
      nlinarith
    have hSupper : (d : ℝ)⁻¹ * S < 1 + ε := by
      have h := lt_of_not_ge htails.2
      change S < (d : ℝ) * (1 + ε) at h
      have hm := mul_lt_mul_of_pos_left h (inv_pos.mpr hdreal)
      have hinv : (d : ℝ)⁻¹ * (d : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hdreal)
      nlinarith
    have hnormsq : ‖gaussianMap d rows x - gaussianMap d rows y‖ ^ 2 =
        ‖x - y‖ ^ 2 * ((d : ℝ)⁻¹ * S) := by
      rw [gaussianMap_norm_sq_sub d hd rows x y,
        sum_inner_sq_eq_norm_sq_mul_normalized d rows (sub_ne_zero.mpr hxy)]
      ring
    have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hlowerSq : ((1 - ε) * ‖x - y‖) ^ 2 ≤
        ‖gaussianMap d rows x - gaussianMap d rows y‖ ^ 2 := by
      rw [hnormsq]
      have hm := mul_lt_mul_of_pos_left hSlower (sq_pos_of_pos hr)
      nlinarith
    have hupperSq : ‖gaussianMap d rows x - gaussianMap d rows y‖ ^ 2 ≤
        ((1 + ε) * ‖x - y‖) ^ 2 := by
      rw [hnormsq]
      have hm := mul_lt_mul_of_pos_left hSupper (sq_pos_of_pos hr)
      nlinarith
    constructor
    · have hlower0 : 0 ≤ (1 - ε) * ‖x - y‖ := mul_nonneg (sub_nonneg.mpr hε1) (norm_nonneg _)
      nlinarith [norm_nonneg (gaussianMap d rows x - gaussianMap d rows y)]
    · have hupper0 : 0 ≤ (1 + ε) * ‖x - y‖ :=
        mul_nonneg (by linarith) (norm_nonneg _)
      nlinarith [norm_nonneg (gaussianMap d rows x - gaussianMap d rows y)]

end ProjectionRows

section
namespace MathlibExt.Geometry.Euclidean.JohnsonLindenstraussWanted

/-!
# Johnson–Lindenstrauss lemma (ATLAS item N147)

Source module path:
`Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/JohnsonLindenstrauss.lean`.

Source-to-API map: source lines 19--140 map to `johnson_lindenstrauss`.

Scope: `N ≥ 2` is an ATLAS-added exclusion; `X.card = N` is kept as stated;
`f` is an ordinary total map on the ambient spaces (equivalent by
restriction/extension to a map defined only on `X`); the `ε > 1` case is included
(the source quantifies over every `ε > 0`, discharging `ε > 1` via the zero map in the
intermediate lemmas). No linearity, randomness, probability distribution, or explicit
value of the constant is asserted.

This file proves the full outer ATLAS theorem; it does not state the distinct
explicit-constant linear-map variant.
-/

/--
**Johnson–Lindenstrauss lemma.** There is a constant $C > 0$ with the following property. Let
$\varepsilon > 0$, let $m$ and $N \ge 2$ be natural numbers, let $X$ be a set of exactly $N$
points of $\mathbb{R}^m$ with the Euclidean norm, and let $d$ be a natural number with
$d > C \varepsilon^{-2} \log N$. Then there is a map $f : \mathbb{R}^m \to \mathbb{R}^d$ such
that $(1 - \varepsilon) \|x - y\| \le \|f(x) - f(y)\| \le (1 + \varepsilon) \|x - y\|$ for all
$x, y \in X$, where $\mathbb{R}^d$ also carries the Euclidean norm.

The map $f$ is not required to be linear, and $\varepsilon \ge 1$ is allowed (there the zero
map works). The proof takes $C = 64$ and uses a Gaussian random projection with a union bound
over pairs of points.

Proves `Wanted` entry `johnson_lindenstrauss`.

Source: W. B. Johnson and J. Lindenstrauss, "Extensions of Lipschitz mappings into
a Hilbert space," Contemporary Mathematics 26, Conference on Modern Analysis and
Probability, American Mathematical Society (1984), 189--206, DOI 10.1090/conm/026/737400.
ATLAS source-to-API map, item N147, module
`Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/JohnsonLindenstrauss.lean`, source
lines 19--140, pinned commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`; ATLAS adds the
hypothesis that N is at least 2, and its proof rests on the placeholder
`jl_probabilistic_existence`, which this proof replaces.
-/
theorem johnson_lindenstrauss :
    ∃ C : ℝ, C > 0 ∧
      ∀ (ε : ℝ), ε > 0 →
        ∀ (m : ℕ) (N : ℕ), N ≥ 2 →
          ∀ (X : Finset (EuclideanSpace ℝ (Fin m))), X.card = N →
            ∀ (d : ℕ), (d : ℝ) > C * ε⁻¹ ^ 2 * Real.log (N : ℝ) →
              ∃ f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d),
                ∀ x ∈ X, ∀ y ∈ X,
                  (1 - ε) * ‖x - y‖ ≤ ‖f x - f y‖ ∧
                  ‖f x - f y‖ ≤ (1 + ε) * ‖x - y‖ := by
  refine ⟨64, by norm_num, ?_⟩
  intro ε hε m N hN X hcard d hd
  by_cases hε1 : ε ≤ 1
  · have hlog : 0 < Real.log (N : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
    have hdreal : 0 < (d : ℝ) := by
      have hright : 0 < 64 * ε⁻¹ ^ 2 * Real.log (N : ℝ) := by positivity
      linarith
    have hdpos : 0 < d := by exact_mod_cast hdreal
    have hbound : (X.card : ℝ) ^ 2 *
        (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) < 1 := by
      rw [hcard]
      exact dimension_implies_failure_bound hN hε hd
    obtain ⟨rows, hrows⟩ :=
      exists_rows_not_anyPairFailure d hε.le hε1 X hbound
    refine ⟨gaussianMap d rows, ?_⟩
    intro x hx y hy
    apply gaussianMap_pair_bounds d hdpos hε.le hε1 rows x y
    intro hpair
    apply hrows
    unfold anyPairFailure
    exact Set.mem_iUnion_of_mem x <| Set.mem_iUnion_of_mem hx <|
      Set.mem_iUnion_of_mem y <| Set.mem_iUnion_of_mem hy hpair
  · have hεge : 1 ≤ ε := le_of_not_ge hε1
    refine ⟨fun _ => 0, ?_⟩
    intro x hx y hy
    simp only [sub_self, norm_zero]
    constructor
    · have : (1 - ε) * ‖x - y‖ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hεge) (norm_nonneg _)
      simpa using this
    · exact mul_nonneg (by linarith) (norm_nonneg _)

end MathlibExt.Geometry.Euclidean.JohnsonLindenstraussWanted
