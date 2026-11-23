/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.WaldDiagonalTerms
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.IdentDistrib

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset ENNReal
open scoped NNReal
open MathlibExt.Probability.WaldDiagonalTerms

namespace MathlibExtTest.Probability.WaldDiagonalTerms

/-- The product of standard Gaussians, the test probability space. -/
noncomputable abbrev gaussPi : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

/-- The `n`-th Gaussian coordinate. -/
def coord (n : ℕ) (ω : ℕ → ℝ) : ℝ := ω n

/-- Membership form of `le_iSup` for a supremum over a set of indices. -/
theorem le_iSup_mem {s : Set ℕ} {g : ℕ → MeasurableSpace (ℕ → ℝ)} {a : ℕ} (ha : a ∈ s) :
    g a ≤ ⨆ i ∈ s, g i := by
  refine le_trans (le_iSup_of_le ha le_rfl) (le_iSup_of_le a le_rfl)

/-- The predictable filtration `ℱ k = σ(coord 0, …, coord (k - 1))`. -/
noncomputable def predFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) where
  seq k := ⨆ i ∈ {j : ℕ | j < k}, MeasurableSpace.comap (coord i) inferInstance
  mono' := by
    intro i j hij
    show (⨆ a ∈ {x : ℕ | x < i}, MeasurableSpace.comap (coord a) inferInstance) ≤
      (⨆ a ∈ {x : ℕ | x < j}, MeasurableSpace.comap (coord a) inferInstance)
    apply iSup_le
    intro a
    apply iSup_le
    intro ha
    have ha' : a < i := ha
    exact le_iSup_mem (s := {x : ℕ | x < j})
      (g := fun a => MeasurableSpace.comap (coord a) inferInstance)
      (lt_of_lt_of_le ha' hij)
  le' := by
    intro k
    show (⨆ a ∈ {x : ℕ | x < k}, MeasurableSpace.comap (coord a) inferInstance) ≤
      (inferInstance : MeasurableSpace (ℕ → ℝ))
    apply iSup_le
    intro a
    apply iSup_le
    intro _
    exact (measurable_pi_apply a).comap_le

theorem coord_measurable (n : ℕ) : Measurable (coord n) :=
  measurable_pi_apply n

theorem coord_map (n : ℕ) : gaussPi.map (coord n) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval (μ := fun _ : ℕ => gaussianReal 0 1) n

theorem coord_identDistrib (i j : ℕ) :
    IdentDistrib (coord i) (coord j) gaussPi gaussPi :=
  ⟨(coord_measurable i).aemeasurable, (coord_measurable j).aemeasurable,
    by rw [coord_map i, coord_map j]⟩

theorem coord_iIndepFun : iIndepFun coord gaussPi :=
  iIndepFun_infinitePi (X := fun _ : ℕ => id) (fun _ => measurable_id)

theorem coord_indep_of_filtration (k : ℕ) :
    Indep (MeasurableSpace.comap (coord k) inferInstance) (predFiltration k) gaussPi := by
  have h := indep_iSup_of_disjoint
    (m := fun i => MeasurableSpace.comap (coord i) inferInstance)
    (fun i => (coord_measurable i).comap_le) coord_iIndepFun.iIndep
    (S := {k}) (T := {j : ℕ | j < k})
    (Set.disjoint_singleton_left.mpr (by simp))
  rw [_root_.iSup_singleton] at h
  show Indep (MeasurableSpace.comap (coord k) inferInstance)
    (⨆ i ∈ {x : ℕ | x < k}, MeasurableSpace.comap (coord i) inferInstance) gaussPi
  exact h

/-- The zeroth Gaussian coordinate is square-integrable. -/
theorem coord_memLp_two : MemLp (coord 0) 2 gaussPi := by
  have hId : IdentDistrib (coord 0) id gaussPi (gaussianReal (0 : ℝ) 1) :=
    ⟨(coord_measurable 0).aemeasurable, aemeasurable_id, by rw [coord_map 0, Measure.map_id]⟩
  have hMem : MemLp id 2 (gaussianReal (0 : ℝ) (1 : ℝ≥0)) :=
    memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0))
  exact hId.memLp_iff.mpr hMem

/-- Square-integrability of the zeroth Gaussian coordinate. -/
theorem coord_sq_integrable : Integrable (fun ω => (coord 0 ω) ^ 2) gaussPi :=
  coord_memLp_two.integrable_sq

/-- The second moment of the standard Gaussian is `1`. -/
theorem coord_sq_integral : ∫ ω, (coord 0 ω) ^ 2 ∂gaussPi = 1 := by
  have h1 : ∫ ω, (coord 0 ω) ^ 2 ∂gaussPi = ∫ y, y ^ 2 ∂gaussianReal (0 : ℝ) 1 := by
    rw [← coord_map 0]
    exact (MeasureTheory.integral_map (coord_measurable 0).aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable).symm
  rw [h1]
  have h2 : ∫ y, y ^ 2 ∂gaussianReal (0 : ℝ) (1 : ℝ≥0) = 1 := by
    have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    rw [variance_eq_integral measurable_id'.aemeasurable] at hv
    simp only [integral_id_gaussianReal] at hv
    simpa using hv
  exact h2

/-- Diagonal-term identity for the Gaussian coordinates and the constant
stopping time `T = 2`: `E[X_0² + X_1²] = E[X_0²] · 2`. -/
theorem diagonal_terms_gaussian_coords :
    ∫ ω, (∑ i ∈ Finset.range 2, (coord i ω) ^ 2) ∂gaussPi =
      (∫ ω, (coord 0 ω) ^ 2 ∂gaussPi) * 2 := by
  have h := wald_diagonal_terms (X := coord) (f := predFiltration) (T := fun _ : ℕ → ℝ => 2)
    coord_identDistrib coord_sq_integrable (isStoppingTime_const _ _)
    coord_indep_of_filtration (integrable_const (2 : ℝ))
  simpa using h

/-- Numeric form: `E[X_0² + X_1²] = 2` for standard Gaussian coordinates. -/
theorem diagonal_terms_gaussian_coords_value :
    ∫ ω, (∑ i ∈ Finset.range 2, (coord i ω) ^ 2) ∂gaussPi = 2 := by
  rw [diagonal_terms_gaussian_coords, coord_sq_integral]
  norm_num

/-- Integrability of the stopped sum of squares for the Gaussian
coordinates and the constant stopping time `T = 2`. -/
theorem integrable_diagonal_gaussian_coords :
    Integrable (fun ω => ∑ i ∈ Finset.range 2, (coord i ω) ^ 2) gaussPi :=
  integrable_stopped_sum_sq_diag (X := coord) (f := predFiltration) (T := fun _ : ℕ → ℝ => 2)
    coord_identDistrib coord_sq_integrable (isStoppingTime_const _ _)
    coord_indep_of_filtration (integrable_const (2 : ℝ))

/-- Both sides vanish for the zero stopping time. -/
theorem diagonal_terms_zero_stopping_time :
    ∫ ω, (∑ i ∈ Finset.range 0, (coord i ω) ^ 2) ∂gaussPi = 0 := by
  have hT0 : Integrable (fun ω => (((fun _ : ℕ → ℝ => 0) ω : ℕ) : ℝ)) gaussPi := by
    simp
  have h := wald_diagonal_terms (X := coord) (f := predFiltration) (T := fun _ : ℕ → ℝ => 0)
    coord_identDistrib coord_sq_integrable (isStoppingTime_const _ _)
    coord_indep_of_filtration hT0
  rw [show (∫ ω, (((fun _ : ℕ → ℝ => 0) ω : ℕ) : ℝ) ∂gaussPi) = 0 from by simp,
    mul_zero] at h
  exact h

#print axioms wald_diagonal_terms
#print axioms integrable_stopped_sum_sq_diag

end MathlibExtTest.Probability.WaldDiagonalTerms
