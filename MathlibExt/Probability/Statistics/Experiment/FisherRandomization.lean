/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Assignment
public import MathlibExt.Probability.Statistics.MultipleTesting.PermutationPValue
public import MathlibExt.Probability.Statistics.MultipleTesting.Basic

/-!
# Fisher randomization tests under the complete-randomization law

The full symmetric-group permutation p-value of any measurable treatment-set
statistic is valid under `completeRandomization`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExt.Probability.Statistics.Experiment

theorem fisher_image_cancel {ι : Type*} [DecidableEq ι] (e : Equiv.Perm ι)
    (S : Finset ι) :
    Finset.image e (Finset.image e.symm S) = S := by
  rw [Finset.image_image]
  have hcomp : (⇑e ∘ ⇑e.symm) = fun x => x := funext fun x => e.apply_symm_apply x
  rw [hcomp, Finset.image_id']

/-- Relabeling action of permutations on treated sets. Public by design:
consumers and the companion test slice must elaborate
`permutationPValue (Equiv.Perm ι) T`, which needs this instance visible.
Mathlib declares no global `MulAction (Equiv.Perm ι) (Finset ι)` instance,
verified by source search at the pinned Mathlib revision. Do not edit the
action definition; prove the two coherence fields. -/
instance fisherMulAction {ι : Type*} [Fintype ι] [DecidableEq ι] :
    MulAction (Equiv.Perm ι) (Finset ι) where
  smul e S := Finset.image e S
  one_smul := by
    intro S
    change Finset.image (1 : Equiv.Perm ι) S = S
    simp
  mul_smul := by
    intro e₁ e₂ S
    change Finset.image (e₁ * e₂) S = Finset.image e₁ (Finset.image e₂ S)
    rw [Equiv.Perm.coe_mul, Finset.image_image]

/-- Permuting unit labels preserves the complete-randomization law. -/
theorem invariant_completeRandomization_map_image {ι : Type*} [Fintype ι]
    [DecidableEq ι] {n₁ : ℕ} (e : Equiv.Perm ι) :
    Measure.map (fun S : Finset ι => Finset.image e S)
      (completeRandomization ι n₁) = completeRandomization ι n₁ := by
  classical
  rw [completeRandomization_eq]
  apply Measure.ext
  intro t ht
  have hmeas : Measurable (fun S : Finset ι => Finset.image e S) := Measurable.of_discrete
  rw [Measure.map_apply hmeas ht, Measure.uniformOfFinset_apply,
    Measure.uniformOfFinset_apply]
  have hcard : ((univ.powersetCard n₁).filter
      (fun x => x ∈ (fun S : Finset ι => Finset.image e S) ⁻¹' t)).card =
      ((univ.powersetCard n₁).filter (fun x => x ∈ t)).card := by
    refine Finset.card_bij (fun x _ => Finset.image e x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
        Set.mem_preimage] at hx ⊢
      refine ⟨?_, hx.2⟩
      rw [Finset.card_image_of_injective _ e.injective, hx.1]
    · intro a₁ _ a₂ _ hab
      exact Finset.image_injective e.injective hab
    · intro y hy
      refine ⟨Finset.image e.symm y, ?_, fisher_image_cancel e y⟩
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
        Set.mem_preimage] at hy ⊢
      refine ⟨by rw [Finset.card_image_of_injective _ e.symm.injective, hy.1], ?_⟩
      rw [fisher_image_cancel e y]
      exact hy.2
  rw [hcard]

/-- Fisher randomization test: the full symmetric-group permutation p-value of
any measurable treatment-set statistic is valid under complete randomization.
Clause map: fixed potential outcomes with no interference enter through the
arbitrary statistic `T` of the treated set and its measurability `hT`; the
sharp null is the use case `T = diffInMeans y₀ y₀` (see the test file);
relabeling invariance of the assignment law is
`invariant_completeRandomization_map_image`; validity is the `IsValidPValue`
conclusion, via `isValidPValue_permutationPValue`; the assignment law is
normalized by `h`, discharged through
`isProbabilityMeasure_completeRandomization`. -/
theorem isValidPValue_fisherRandomization {ι : Type*} [Fintype ι]
    [DecidableEq ι] {n₁ : ℕ} (h : n₁ ≤ Fintype.card ι)
    {T : Finset ι → ℝ} (hT : Measurable T) :
    IsValidPValue (completeRandomization ι n₁)
      (permutationPValue (Equiv.Perm ι) T) := by
  have _inst := isProbabilityMeasure_completeRandomization h
  have hsmul : ∀ g : Equiv.Perm ι, Measurable (fun S : Finset ι => g • S) :=
    fun _ => Measurable.of_discrete
  have hmap : ∀ c : Equiv.Perm ι,
      Measure.map (fun S : Finset ι => c • S) (completeRandomization ι n₁) =
        completeRandomization ι n₁ := by
    intro c
    have hfun : (fun S : Finset ι => c • S) = (fun S : Finset ι => Finset.image c S) :=
      rfl
    rw [hfun]
    exact invariant_completeRandomization_map_image c
  have _sinv : SMulInvariantMeasure (Equiv.Perm ι) (Finset ι)
      (completeRandomization ι n₁) := by
    rw [smulInvariantMeasure_iff]
    intro c s hs
    exact Measure.measure_preimage_of_map_eq_self (hmap c) (hsmul c).aemeasurable
      hs.nullMeasurableSet
  exact isValidPValue_permutationPValue _ hsmul hT

end MathlibExt.Probability.Statistics.Experiment
