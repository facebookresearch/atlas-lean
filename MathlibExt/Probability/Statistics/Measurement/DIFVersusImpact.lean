/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.GroupImpact
public import Mathlib.Topology.UnitInterval

/-! # Differential item functioning and marginal group impact -/

@[expose] public section

open MeasureTheory Finset
open scoped unitInterval

namespace MathlibExt.Probability.Statistics.Measurement

universe u

/-- The marginal success probability for a binary item. Mix the one-item Bernoulli
response law with success curve `q` over the latent law `π`, then take the expectation
of the success indicator. -/
noncomputable def itemSuccessMarginal {Z : Type*} (π : PMF Z) (q : Z → I) : ℝ :=
  ∫ x, (if x (0 : Fin 1) then (1 : ℝ) else 0)
    ∂(π.bind fun z => localIndepPMF (fun _ : Fin 1 => (q z : ℝ))
      (fun _ => (q z).2.1) (fun _ => (q z).2.2)).toMeasure

/-- On a finite ability grid, the marginal success probability is the average of the success
curve under the latent law. -/
theorem itemSuccessMarginal_eq_sum {Z : Type*} [Fintype Z] (π : PMF Z) (q : Z → I) :
    itemSuccessMarginal π q = ∑ z, (π z).toReal * (q z : ℝ) :=
  (latentMixture_coordinate_moments π (fun z (_ : Fin 1) => (q z : ℝ))
    (fun z _ => (q z).2.1) (fun z _ => (q z).2.2)).1 0

private noncomputable def twoPointAbility (p : I) : PMF (Fin 2) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (if z = 0 then (p : ℝ) else 1 - (p : ℝ))) (by
    rw [Fin.sum_univ_two]
    simp only [ite_true, one_ne_zero, ite_false]
    rw [← ENNReal.ofReal_add p.2.1 (sub_nonneg.mpr p.2.2)]
    simp)

private noncomputable def rising (z : Fin 2) : I :=
  ⟨if z = 0 then 1 / 4 else 3 / 4, by split <;> constructor <;> norm_num⟩

private noncomputable def flat (_ : Fin 2) : I := ⟨1 / 2, by constructor <;> norm_num⟩

private theorem twoPointMarginal (p : I) (q : Fin 2 → I) :
    itemSuccessMarginal (twoPointAbility p) q =
      (p : ℝ) * (q 0 : ℝ) + (1 - (p : ℝ)) * (q 1 : ℝ) := by
  rw [itemSuccessMarginal_eq_sum, Fin.sum_univ_two]
  simp only [twoPointAbility, PMF.ofFintype_apply, ite_true, one_ne_zero, ite_false,
    ENNReal.toReal_ofReal p.2.1, ENNReal.toReal_ofReal (sub_nonneg.mpr p.2.2)]

/-- **Differential item functioning and group impact are logically independent.**
Fix one common finite ability scale for both groups. If the success curves agree, the marginal
success gap is the weighted difference of the latent masses, with the common curve as weights.
On two ability points, equal curves can produce marginals `3/8` and `5/8`, while differing
curves with the same ability law can both produce marginal `1/2`. The comparisons use the
same ability points in both groups. -/
theorem dif_and_group_impact_independent :
    (∀ {Z : Type u} [Fintype Z] (πA πB : PMF Z) (qA qB : Z → I),
      (∀ z, qA z = qB z) → itemSuccessMarginal πA qA - itemSuccessMarginal πB qB =
        ∑ z, ((πA z).toReal - (πB z).toReal) * (qA z : ℝ)) ∧
    (∃ (πA πB : PMF (Fin 2)) (q : Fin 2 → I),
      itemSuccessMarginal πA q = 3 / 8 ∧ itemSuccessMarginal πB q = 5 / 8) ∧
    (∃ (π : PMF (Fin 2)) (qA qB : Fin 2 → I),
      (∃ z, qA z ≠ qB z) ∧
        itemSuccessMarginal π qA = 1 / 2 ∧ itemSuccessMarginal π qB = 1 / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Z _ πA πB qA qB hq
    exact impact_difference_of_equal_curves πA πB
      (fun z (_ : Fin 1) => (qA z : ℝ)) (fun z _ => (qB z : ℝ))
      (fun z _ => (qA z).2.1) (fun z _ => (qA z).2.2)
      (fun z _ => (qB z).2.1) (fun z _ => (qB z).2.2) 0
      (fun z => congrArg Subtype.val (hq z))
  · refine ⟨twoPointAbility ⟨3 / 4, by constructor <;> norm_num⟩,
      twoPointAbility ⟨1 / 4, by constructor <;> norm_num⟩, rising, ?_, ?_⟩ <;>
      rw [twoPointMarginal] <;> norm_num [rising]
  · refine ⟨twoPointAbility ⟨1 / 2, by constructor <;> norm_num⟩, rising, flat, ⟨0, ?_⟩, ?_, ?_⟩
    · intro h
      have h' := congrArg Subtype.val h
      norm_num [rising, flat] at h'
    all_goals
      rw [twoPointMarginal]
      norm_num [rising, flat]

end MathlibExt.Probability.Statistics.Measurement
