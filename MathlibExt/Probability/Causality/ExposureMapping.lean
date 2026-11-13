/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Sampling.HorvitzThompson
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Exposure mappings and the Horvitz-Thompson exposure-total estimator

Finite-population causal inference under interference, after Aronow and
Samii (2017). An exposure mapping sends each assignment to a per-unit
exposure value. Under an explicit exposure-sufficiency condition the
randomization outcomes factor through exposures, and the Horvitz-Thompson
total over the exposed set is design-unbiased for the exposure-specific
potential-outcome total (Lemma 4.1).

## References

- P. M. Aronow and C. Samii, "Estimating average causal effects under
  general interference, with application to a social network experiment",
  Annals of Applied Statistics 11(4) (2017), 1912-1947.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality

open MeasureTheory MathlibExt.Probability.Sampling

/-- Units receiving exposure `d` under assignment `z`. -/
def exposedSet {α Ω Δ : Type*} [Fintype α] [DecidableEq Δ]
    (e : α → Ω → Δ) (d : Δ) (z : Ω) : Finset α :=
  Finset.univ.filter (fun i => e i z = d)

/-- Exposure probability `πᵢ(d)`: design mass of assignments exposing `i`
to `d`, as the inclusion probability of the exposed set under the
pushed-forward design. -/
noncomputable def exposureProbability {α Ω Δ : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq Δ] (e : α → Ω → Δ) (p : PMF Ω)
    (i : α) (d : Δ) : ℝ :=
  inclusionProbability (p.map (exposedSet e d)) i

/-- Bridge lemma: `πᵢ(d)` equals the source sum of design masses over
assignments with `e i z = d`. -/
theorem exposureProbability_eq_sum {α Ω Δ : Type*} [Fintype α]
    [DecidableEq α] [Fintype Ω] [DecidableEq Δ] (e : α → Ω → Δ)
    (p : PMF Ω) (i : α) (d : Δ) :
    exposureProbability e p i d
      = ∑ z, (if e i z = d then (p z).toReal else 0) := by
  unfold exposureProbability inclusionProbability
  classical
  have hmap : ∀ s : Finset α, ((p.map (exposedSet e d)) s).toReal
      = ∑ z, (if s = exposedSet e d z then (p z).toReal else 0) := by
    intro s
    have hne : ∀ z ∈ (Finset.univ : Finset Ω),
        (@ite _ (s = exposedSet e d z) (Classical.propDecidable _)
          (p z) 0) ≠ ⊤ := by
      intro z _
      by_cases h : s = exposedSet e d z
      · rw [ite_eq_left h]
        exact ne_of_lt
          (lt_of_le_of_lt (PMF.coe_le_one p z) ENNReal.one_lt_top)
      · rw [ite_eq_right h]
        exact ENNReal.zero_ne_top
    rw [PMF.map_apply, tsum_fintype]
    refine (ENNReal.toReal_sum hne).trans ?_
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : s = exposedSet e d z <;> simp [h]
  have hpush : ∀ s : Finset α, (if i ∈ s then
      (∑ z, (if s = exposedSet e d z then (p z).toReal else 0)) else 0)
      = ∑ z, (if i ∈ s then
        (if s = exposedSet e d z then (p z).toReal else 0) else 0) := by
    intro s
    by_cases hi : i ∈ s <;> simp [hi]
  calc ∑ s, (if i ∈ s then ((p.map (exposedSet e d)) s).toReal else 0)
      = ∑ s, ∑ z, (if i ∈ s then
        (if s = exposedSet e d z then (p z).toReal else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [hmap s]
        exact hpush s
    _ = ∑ z, ∑ s, (if i ∈ s then
        (if s = exposedSet e d z then (p z).toReal else 0) else 0) :=
        Finset.sum_comm
    _ = ∑ z, (if e i z = d then (p z).toReal else 0) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.sum_eq_single (exposedSet e d z)]
        · simp only [ite_true, exposedSet, Finset.mem_filter,
            Finset.mem_univ, true_and]
        · intro s' _ hs'
          by_cases hi : i ∈ s' <;> simp [hs', hi]
        · intro hcon
          exact absurd (Finset.mem_univ _) hcon

/-- Condition 1 of Aronow and Samii (2017): the randomization outcomes
depend on the assignment only through the exposure, on the support of
the design. Individual SUTVA is not assumed. -/
def ExposureSufficiency {α Ω Δ : Type*} (e : α → Ω → Δ) (p : PMF Ω)
    (yr : α → Ω → ℝ) : Prop :=
  ∀ i z z', p z ≠ 0 → p z' ≠ 0 → e i z = e i z' → yr i z = yr i z'

open Classical in
/-- Exposure-specific potential outcome, defined from the randomization
outcomes under Condition 1 by evaluating `yr` at a supported assignment
with the required exposure (junk value `0` off the support). -/
noncomputable def exposurePotential {α Ω Δ : Type*}
    (e : α → Ω → Δ) (p : PMF Ω) (yr : α → Ω → ℝ)
    (_hcond : ExposureSufficiency e p yr) (i : α) (d : Δ) : ℝ :=
  if h : ∃ z, p z ≠ 0 ∧ e i z = d then yr i (Classical.choose h) else 0

/-- The potential outcome agrees with `yr` at every supported assignment
carrying the exposure. -/
theorem exposurePotential_eq_of_mem {α Ω Δ : Type*}
    (e : α → Ω → Δ) (p : PMF Ω) (yr : α → Ω → ℝ)
    (hcond : ExposureSufficiency e p yr) (i : α) (z : Ω) (d : Δ)
    (hp : p z ≠ 0) (he : e i z = d) :
    exposurePotential e p yr hcond i d = yr i z := by
  unfold exposurePotential
  have hex : ∃ w, p w ≠ 0 ∧ e i w = d := ⟨z, hp, he⟩
  rw [dite_eq_left hex]
  obtain ⟨hw, hew⟩ := Classical.choose_spec hex
  exact hcond i _ z hw hp (hew.trans he.symm)

/-- Randomization outcomes factor through the exposure under Condition 1. -/
theorem exposurePotential_factorization {α Ω Δ : Type*}
    (e : α → Ω → Δ) (p : PMF Ω) (yr : α → Ω → ℝ)
    (hcond : ExposureSufficiency e p yr) (i : α) (z : Ω)
    (hp : p z ≠ 0) :
    yr i z = exposurePotential e p yr hcond i (e i z) :=
  (exposurePotential_eq_of_mem e p yr hcond i z _ hp rfl).symm

/-- Horvitz-Thompson exposure-total estimator at assignment `z`: the HT
total over the exposed set, weighting observed outcomes by `πᵢ(d)`. -/
noncomputable def exposureHTTotal {α Ω Δ : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq Δ] (e : α → Ω → Δ) (p : PMF Ω)
    (yr : α → Ω → ℝ) (hcond : ExposureSufficiency e p yr) (d : Δ)
    (z : Ω) : ℝ :=
  horvitzThompsonTotal (p.map (exposedSet e d))
    (fun i => exposurePotential e p yr hcond i d) (exposedSet e d z)

/-- Design-unbiasedness of the exposure-total estimator (Aronow and
Samii (2017), Lemma 4.1): with `πᵢ(d) > 0` for the target exposure,
the design expectation equals the potential-outcome total. Only
positivity at `d` is needed; the source's `< 1` is not. -/
theorem integral_exposureHTTotal {α Ω Δ : Type*} [Fintype α]
    [DecidableEq α] [Countable Ω] [DecidableEq Δ] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [MeasurableSpace (Finset α)]
    [MeasurableSingletonClass (Finset α)] (e : α → Ω → Δ) (p : PMF Ω)
    (yr : α → Ω → ℝ) (hcond : ExposureSufficiency e p yr) (d : Δ)
    (hpos : ∀ i, 0 < exposureProbability e p i d) :
    ∫ z, exposureHTTotal e p yr hcond d z ∂p.toMeasure
      = ∑ i, exposurePotential e p yr hcond i d := by
  have hmeas : Measurable (exposedSet e d) := measurable_of_countable _
  have hAES : AEStronglyMeasurable
      (horvitzThompsonTotal (p.map (exposedSet e d))
        (fun i => exposurePotential e p yr hcond i d))
      (Measure.map (exposedSet e d) p.toMeasure) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hAEM : AEMeasurable (exposedSet e d) p.toMeasure :=
    hmeas.aemeasurable
  unfold exposureHTTotal
  rw [← MeasureTheory.integral_map hAEM hAES,
    PMF.toMeasure_map _ _ hmeas]
  exact integral_horvitzThompsonTotal _ _ hpos

end MathlibExt.Probability.Causality
