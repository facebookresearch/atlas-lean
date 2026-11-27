/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.NeuralNetworks.BarronSpace
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# The inverse approximation theorem for the Barron space

W. E, C. Ma and L. Wu, *The Barron space and the flow-induced function spaces for neural network
models*, Constr. Approx. 55 (2022), arXiv:1906.08039, §2.2:

* **Theorem 5 (inverse approximation).** A function on the cube that is the pointwise limit of
  two-layer networks with path norm at most `Q` lies in the Barron space with `‖f‖_B ≤ Q`
  (Prokhorov's theorem on the normalized parameter measures).

The direct approximation theorem, Theorem 4 of the same paper, is proved in
`CSLibExt.MachineLearning.NeuralNetworks.BarronApproximation`.

Networks are written with the normalisation of the paper,
`f_m(x; Θ) = (1/m) ∑ₖ aₖ σ(⟨bₖ, x⟩ + cₖ)` and `‖Θ‖_P = (1/m) ∑ₖ |aₖ| (‖bₖ‖₁ + |cₖ|)`, using
`CSLibExt.MachineLearning.NeuralNetworks.reluNeuron` for one neuron. The Barron norm is
`CSLibExt.MachineLearning.NeuralNetworks.barronNorm` (the `B₂` norm, which the paper's
Proposition 1 identifies with every `B_p` norm).
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.MachineLearning.NeuralNetworks

open MeasureTheory Filter Topology

namespace barron_inverse_approximation

open scoped NNReal ENNReal

private abbrev Param (d : ℕ) := ℝ × (Fin d → ℝ) × ℝ

variable {d : ℕ}

private noncomputable def inputSize (p : Param d) : ℝ := (∑ j, |p.2.1 j|) + |p.2.2|

private lemma size_nonneg (p : Param d) : 0 ≤ inputSize p := by
  exact add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)

private lemma coord_le_size (p : Param d) (j : Fin d) : |p.2.1 j| ≤ inputSize p :=
  (Finset.single_le_sum (f := fun i => |p.2.1 i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
    |>.trans (le_add_of_nonneg_right (abs_nonneg _))

private lemma bias_le_size (p : Param d) : |p.2.2| ≤ inputSize p :=
  le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _)

private def unitParams (d : ℕ) : Set (Param d) := {p | |p.1| ≤ 1 ∧ inputSize p ≤ 1}

private instance compactUnitParams : CompactSpace (unitParams d) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_Icc (α := Param d) (a := -1) (b := 1)).of_isClosed_subset
  · change IsClosed ({p : Param d | |p.1| ≤ 1} ∩ {p | inputSize p ≤ 1})
    apply IsClosed.inter <;> apply isClosed_le _ continuous_const
    · fun_prop
    · unfold inputSize
      fun_prop
  · intro p hp
    have ha := abs_le.mp hp.1
    have hb j := abs_le.mp ((coord_le_size p j).trans hp.2)
    have hc := abs_le.mp ((bias_le_size p).trans hp.2)
    exact ⟨⟨ha.1, (fun j => (hb j).1), hc.1⟩, ⟨ha.2, (fun j => (hb j).2), hc.2⟩⟩

private instance nonemptyUnitParams : Nonempty (unitParams d) :=
  ⟨⟨0, by simp [unitParams, inputSize]⟩⟩

/-- The direction of a neuron after factoring out its nonnegative path weight. -/
private noncomputable def direction (p : Param d) : unitParams d :=
  ⟨(if 0 ≤ p.1 then 1 else -1, fun j => (inputSize p)⁻¹ * p.2.1 j, (inputSize p)⁻¹ * p.2.2),
    by
      constructor
      · split <;> simp
      · change (∑ j, |(inputSize p)⁻¹ * p.2.1 j|) + |(inputSize p)⁻¹ * p.2.2| ≤ 1
        simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr (size_nonneg p)), ← Finset.mul_sum,
          ← mul_add]
        exact inv_mul_le_one_of_le₀ le_rfl (size_nonneg p)⟩

private lemma weight_mul_direction (p : Param d) (x : Fin d → ℝ) :
    (|p.1| * inputSize p) * reluNeuron (direction p) x = reluNeuron p x := by
  by_cases hz : inputSize p = 0
  · have hb (j : Fin d) : p.2.1 j = 0 := abs_nonpos_iff.mp (hz ▸ coord_le_size p j)
    have hc : p.2.2 = 0 := abs_nonpos_iff.mp (hz ▸ bias_le_size p)
    simp [hz, reluNeuron, hb, hc]
  · have ha : |p.1| * (if 0 ≤ p.1 then 1 else -1) = p.1 := by
      split_ifs with h
      · simp [abs_of_nonneg h]
      · simp [abs_of_neg (lt_of_not_ge h)]
    simp only [reluNeuron, direction, mul_assoc, ← Finset.mul_sum, ← mul_add]
    rw [show ∀ z : ℝ, max ((inputSize p)⁻¹ * z) 0 = (inputSize p)⁻¹ * max z 0 from
      fun z => by rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr (size_nonneg p)), mul_zero]]
    calc _ = (|p.1| * (if 0 ≤ p.1 then 1 else -1)) * (inputSize p * (inputSize p)⁻¹) *
            max ((∑ j, p.2.1 j * x j) + p.2.2) 0 := by ring
      _ = _ := by rw [ha, mul_inv_cancel₀ hz, mul_one]

private noncomputable def pathWeight (p : Param d) : ℝ≥0 :=
  ⟨|p.1| * inputSize p, mul_nonneg (abs_nonneg _) (size_nonneg p)⟩

/-- The empirical measure assigns each normalized direction its share of the path norm. -/
private noncomputable def empirical {m : ℕ} (θ : Fin m → Param d) :
    FiniteMeasure (unitParams d) :=
  ⟨(m : ℝ≥0)⁻¹ • ∑ i, pathWeight (θ i) • Measure.dirac (direction (θ i)), inferInstance⟩

private lemma integral_empirical {m : ℕ} (θ : Fin m → Param d) (g : C(unitParams d, ℝ)) :
    ∫ p, g p ∂(empirical θ) = (m : ℝ)⁻¹ * ∑ i, (pathWeight (θ i) : ℝ) * g (direction (θ i)) := by
  rw [empirical, FiniteMeasure.toMeasure_mk, integral_smul_nnreal_measure,
    integral_finsetSum_measure]
  · simp only [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul,
      NNReal.coe_inv, NNReal.coe_natCast]
  · intro i _
    exact g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma empirical_mass {m : ℕ} (θ : Fin m → Param d) :
    ((empirical θ).mass : ℝ) = (m : ℝ)⁻¹ * ∑ i, |(θ i).1| * inputSize (θ i) := by
  change (((empirical θ) Set.univ : ℝ≥0) : ℝ) = (m : ℝ)⁻¹ * ∑ i, (pathWeight (θ i) : ℝ)
  simpa only [ContinuousMap.const_apply, integral_const, smul_eq_mul, mul_one,
    FiniteMeasure.measureReal_eq_coe_coeFn] using integral_empirical θ (ContinuousMap.const _ 1)

private lemma continuous_eval (x : Fin d → ℝ) : Continuous fun p : Param d => reluNeuron p x := by
  unfold reluNeuron
  fun_prop

private noncomputable def eval (x : Fin d → ℝ) : C(unitParams d, ℝ) :=
  ⟨fun p => reluNeuron p.val x, (continuous_eval x).comp
    (show Continuous (Subtype.val : unitParams d → Param d) from continuous_subtype_val)⟩

private lemma empirical_integral {m : ℕ} (θ : Fin m → Param d) (x : Fin d → ℝ) :
    ∫ p, eval x p ∂(empirical θ) = (m : ℝ)⁻¹ * ∑ i, reluNeuron (θ i) x := by
  rw [integral_empirical]
  congr 1
  exact Finset.sum_congr rfl fun i _ => weight_mul_direction (θ i) x

/-- Evaluation on the cube takes the compact set of measures of bounded mass to a closed set
in the topology of pointwise convergence. -/
private lemma limit_measure {Q : ℝ≥0} (μ : ℕ → FiniteMeasure (unitParams d))
    (hμ : ∀ k, (μ k).mass ≤ Q) (f : unitCube d → ℝ)
    (hf : ∀ x, Tendsto (fun k => ∫ p, eval x.val p ∂(μ k)) atTop (𝓝 (f x))) :
    ∃ ν : FiniteMeasure (unitParams d), ν.mass ≤ Q ∧ ∀ x, ∫ p, eval x.val p ∂ν = f x := by
  let F (ν : FiniteMeasure (unitParams d)) (x : unitCube d) := ∫ p, eval x.val p ∂ν
  have hF : Continuous F := continuous_pi fun x =>
    FiniteMeasure.continuous_integral_continuousMap (eval x.val)
  have hc := (isCompact_setOfPred_finiteMeasure_le_of_compactSpace (unitParams d) Q).image hF
  obtain ⟨ν, hν, heq⟩ := hc.isClosed.mem_of_tendsto (tendsto_pi_nhds.mpr hf)
    (Eventually.of_forall fun k => ⟨μ k, hμ k, rfl⟩)
  exact ⟨ν, hν, congrFun heq⟩

private noncomputable def scaleOutput (r : ℝ≥0) (p : unitParams d) : Param d :=
  (r * p.val.1, p.val.2)

private lemma continuous_scaleOutput (r : ℝ≥0) :
    Continuous (scaleOutput (d := d) r) := by
  unfold scaleOutput
  fun_prop

private lemma eval_scaleOutput (r : ℝ≥0) (p : unitParams d) (x : Fin d → ℝ) :
    reluNeuron (scaleOutput r p) x = r * eval x p := by
  simp [scaleOutput, reluNeuron, eval, mul_assoc]

private lemma weight_scaleOutput_le (r : ℝ≥0) (p : unitParams d) :
    pathWeight (scaleOutput r p) ≤ r := by
  change |(r : ℝ) * p.val.1| * inputSize p.val ≤ r
  rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg r), mul_assoc]
  exact mul_le_of_le_one_right r.2
    ((mul_le_of_le_one_right (abs_nonneg _) p.property.2).trans p.property.1)

private lemma moment_eq (p : Param d) :
    ‖p.1‖ₑ ^ 2 * (∑ j, ‖p.2.1 j‖ₑ + ‖p.2.2‖ₑ) ^ 2 = (pathWeight p : ℝ≥0∞) ^ 2 := by
  rw [← mul_pow, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  change _ = ENNReal.ofReal (|p.1| * ((∑ j, |p.2.1 j|) + |p.2.2|))
  simp only [Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _),
    ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _]

/-- Normalize the limiting finite measure and put its mass in the output coefficient. -/
private lemma representation_of_measure (μ : FiniteMeasure (unitParams d))
    (f : (Fin d → ℝ) → ℝ) (hf : ∀ x : unitCube d, ∫ p, eval x.val p ∂μ = f x) :
    (∃ ρ, IsBarronRepresentation f ρ) ∧ barronNorm f ≤ (μ.mass : ℝ≥0∞) := by
  let ρ : Measure (Param d) := (μ.normalize : Measure _).map (scaleOutput μ.mass)
  have hmap := (continuous_scaleOutput (d := d) μ.mass).measurable
  have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have hrep : IsBarronRepresentation f ρ := by
    refine ⟨inferInstance, fun x hx => ⟨?_, ?_⟩⟩
    · apply (integrable_map_measure (continuous_eval x).aestronglyMeasurable hmap.aemeasurable).2
      exact Continuous.integrable_of_hasCompactSupport
        ((continuous_eval x).comp (continuous_scaleOutput μ.mass))
        (HasCompactSupport.of_compactSpace _)
    · rw [← hf ⟨x, hx⟩]
      have hm : (μ : Measure (unitParams d)) = μ.mass • (μ.normalize : Measure (unitParams d)) :=
        congrArg FiniteMeasure.toMeasure μ.self_eq_mass_smul_normalize
      dsimp only [ρ]
      rw [hm, integral_smul_nnreal_measure,
        integral_map_of_stronglyMeasurable hmap (continuous_eval x).stronglyMeasurable]
      simp only [eval_scaleOutput, integral_const_mul, NNReal.smul_def, smul_eq_mul]
  refine ⟨⟨ρ, hrep⟩, (iInf₂_le _ hrep).trans ?_⟩
  have hmoment : ∫⁻ p : Param d, (pathWeight p : ℝ≥0∞) ^ 2 ∂ρ ≤ (μ.mass : ℝ≥0∞) ^ 2 := by
    dsimp only [ρ]
    rw [lintegral_map _ hmap]
    · calc _ ≤ ∫⁻ _ : unitParams d, (μ.mass : ℝ≥0∞) ^ 2 ∂μ.normalize :=
            lintegral_mono fun p => pow_le_pow_left' (ENNReal.coe_le_coe.mpr
              (weight_scaleOutput_le μ.mass p)) 2
        _ = _ := by simp
    · simp_rw [← moment_eq]
      fun_prop
  simp_rw [moment_eq]
  refine (ENNReal.rpow_le_rpow hmoment (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq ?_
  rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.pow_rpow_inv_natCast two_ne_zero]

end barron_inverse_approximation

-- The hypotheses `hf` (continuity of `f`) and `hw` (positive widths) belong to the wanted
-- statement and are kept, but the proof does not use them: a pointwise limit of networks with
-- path norm at most `Q` is `Q`-Lipschitz on the cube for the sup norm, hence continuous, and a
-- network of width zero is the zero function. The unused-variables linter is off for this reason.
open barron_inverse_approximation in
set_option linter.unusedVariables false in
/-- **Inverse approximation theorem for the Barron space** (W. E, C. Ma and L. Wu, *The Barron
space and the flow-induced function spaces for neural network models*, Constr. Approx. 55 (2022),
Theorem 5). Let `f` be continuous on the cube `[0, 1]^d` and `Q` real. Suppose a sequence of
two-layer ReLU networks `f_k(x) = (1/w_k) ∑_{i < w_k} aᵢ σ(⟨bᵢ, x⟩ + cᵢ)` of widths `w_k ≥ 1`,
each with path norm `(1/w_k) ∑ᵢ |aᵢ| (‖bᵢ‖₁ + |cᵢ|) ≤ Q`, converges to `f` at every point of
the cube. Then `f` has a Barron representation `ρ` on the cube, and `‖f‖_B ≤ Q`. -/
theorem barron_inverse_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (unitCube d)) (Q : ℝ) (w : ℕ → ℕ) (hw : ∀ k, 0 < w k)
    (θ : (k : ℕ) → Fin (w k) → ℝ × (Fin d → ℝ) × ℝ)
    (hpath : ∀ k, (w k : ℝ)⁻¹ * ∑ i, |(θ k i).1| * (∑ j, |(θ k i).2.1 j| + |(θ k i).2.2|) ≤ Q)
    (hlim : ∀ x ∈ unitCube d,
      Tendsto (fun k => (w k : ℝ)⁻¹ * ∑ i, reluNeuron (θ k i) x) atTop (𝓝 (f x))) :
    (∃ ρ, IsBarronRepresentation f ρ) ∧ barronNorm f ≤ ENNReal.ofReal Q := by
  have hmass k : (empirical (θ k)).mass ≤ Q.toNNReal := by
    have h : ((empirical (θ k)).mass : ℝ) ≤ Q := (empirical_mass _).trans_le (hpath k)
    simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal h
  obtain ⟨μ, hμ, hμf⟩ := limit_measure (fun k => empirical (θ k)) hmass (fun x => f x.val)
    (fun x => by simpa only [empirical_integral] using hlim x.val x.property)
  obtain ⟨hrep, hnorm⟩ := representation_of_measure μ f hμf
  exact ⟨hrep, hnorm.trans (ENNReal.coe_le_coe.mpr hμ)⟩

end CSLibExt.MachineLearning.NeuralNetworks
