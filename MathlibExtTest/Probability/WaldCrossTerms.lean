/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.WaldCrossTerms
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.IdentDistrib

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset ENNReal
open scoped NNReal
open MathlibExt.Probability.WaldCrossTerms

namespace MathlibExtTest.Probability.WaldCrossTerms

/-- Algebraic check: the square expansion for `f i = i`, `n = 3`. -/
theorem sum_sq_expansion_three :
    (∑ i ∈ Finset.range 3, (i : ℝ)) ^ 2 =
      ∑ i ∈ Finset.range 3, ((i : ℝ)) ^ 2 +
        2 * ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range i, (j : ℝ) * (i : ℝ) := by
  rw [sum_sq_expansion]

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

theorem coord_integrable : Integrable (coord 0) gaussPi := by
  have hgauss : Integrable id (gaussianReal (0 : ℝ) 1) :=
    (memLp_one_iff_integrable).mp (by
      simpa using ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ))
        (v := (1 : ℝ≥0)) (p := (1 : ℝ≥0)))
  have h := integrable_map_measure (μ := gaussPi) (f := coord 0) (g := id)
    aestronglyMeasurable_id (coord_measurable 0).aemeasurable
  rw [coord_map 0] at h
  exact h.mp hgauss

theorem coord_mean_zero : ∫ ω, coord 0 ω ∂gaussPi = 0 := by
  have hgauss : ∫ y, id y ∂gaussianReal (0 : ℝ) (1 : ℝ≥0) = 0 :=
    ProbabilityTheory.integral_id_gaussianReal
  have h : (∫ ω, id (coord 0 ω) ∂gaussPi) =
      ∫ y, id y ∂gaussianReal (0 : ℝ) (1 : ℝ≥0) := by
    rw [← coord_map 0]
    exact (MeasureTheory.integral_map (coord_measurable 0).aemeasurable
      aestronglyMeasurable_id).symm
  calc ∫ ω, coord 0 ω ∂gaussPi = ∫ ω, id (coord 0 ω) ∂gaussPi := rfl
    _ = ∫ y, id y ∂gaussianReal (0 : ℝ) (1 : ℝ≥0) := h
    _ = 0 := hgauss

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

theorem coord_adapted (j k : ℕ) (hjk : j < k) :
    @Measurable (ℕ → ℝ) ℝ (predFiltration k) inferInstance (coord j) := by
  have hbase : @Measurable (ℕ → ℝ) ℝ
      (MeasurableSpace.comap (coord j) inferInstance) inferInstance (coord j) :=
    measurable_iff_comap_le.mpr le_rfl
  show @Measurable (ℕ → ℝ) ℝ
    (⨆ a ∈ {x : ℕ | x < k}, MeasurableSpace.comap (coord a) inferInstance)
    inferInstance (coord j)
  rw [measurable_iff_comap_le]
  exact le_iSup_mem (s := {x : ℕ | x < k})
    (g := fun a => MeasurableSpace.comap (coord a) inferInstance) hjk

/-- Cross-term vanishing for the first two Gaussian coordinates and the
constant stopping time `T = 2`: `E[X₀ · X₁] = 0`. -/
theorem cross_pair_gaussian_coords :
    ∫ ω, (if 1 < 2 then coord 0 ω * coord 1 ω else 0) ∂gaussPi = 0 :=
  cross_pair_integral_zero (T := fun _ : ℕ → ℝ => 2)
    coord_identDistrib coord_integrable coord_mean_zero
    (isStoppingTime_const _ _) coord_indep_of_filtration coord_adapted 0 1 (by norm_num)

/-- Total cross-term vanishing for the Gaussian coordinates and the
constant stopping time `T = 2`. -/
theorem cross_terms_gaussian_coords :
    ∫ ω, (∑ i ∈ Finset.range 2, ∑ j ∈ Finset.range i,
      coord j ω * coord i ω) ∂gaussPi = 0 :=
  wald_cross_terms_zero_of_bounded (T := fun _ : ℕ → ℝ => 2) (N := 2)
    coord_identDistrib coord_integrable coord_mean_zero
    (isStoppingTime_const _ _) coord_indep_of_filtration
    (fun k => coord_adapted k (k + 1) (Nat.lt_succ_self k))
    (fun _ => le_refl 2)

#print axioms cross_terms_gaussian_coords

/-- The total cross-term API accepts canonical one-step adaptedness without
requiring a joint-independence argument. -/
theorem total_cross_terms_canonical_assumptions
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_int : Integrable (X 0) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hadapt : ∀ k, @Measurable Ω ℝ (f (k + 1)) inferInstance (X k))
    (hsumm : ∑' n, ∫⁻ ω,
      ‖(if n < T ω then ∑ j ∈ Finset.range n, X j ω * X n ω else 0)‖ₑ ∂μ ≠ ⊤) :
    ∫ ω, (∑ i ∈ Finset.range (T ω), ∑ j ∈ Finset.range i,
      X j ω * X i ω) ∂μ = 0 :=
  wald_cross_terms_zero hX_iid hX_int hmean hT hXf hadapt hsumm

/-- The bounded total cross-term API accepts the canonical Wald assumptions
without requiring joint independence. -/
theorem bounded_cross_terms_canonical_assumptions
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_int : Integrable (X 0) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hadapt : ∀ k, @Measurable Ω ℝ (f (k + 1)) inferInstance (X k))
    {N : ℕ} (hT_bdd : ∀ ω, T ω ≤ N) :
    ∫ ω, (∑ i ∈ Finset.range (T ω), ∑ j ∈ Finset.range i,
      X j ω * X i ω) ∂μ = 0 :=
  wald_cross_terms_zero_of_bounded hX_iid hX_int hmean hT hXf hadapt hT_bdd

end MathlibExtTest.Probability.WaldCrossTerms
