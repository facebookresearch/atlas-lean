/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Sampling.HorvitzThompson
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Exposure mappings and the Horvitz-Thompson exposure-total estimator

Finite-population causal inference under interference, after Aronow and
Samii (2017). An exposure mapping `e` sends each assignment `z` to a
per-unit exposure `e i z`, and `yr i z` is unit `i`'s randomization
potential outcome under assignment `z`, so the observed outcome at the
realized assignment `z` is `yr i z`. The Horvitz-Thompson exposure-total
estimator weights these observed outcomes over the exposed set by the
exposure probabilities `πᵢ(d)`.

Aronow and Samii's estimand is the mean `μ(d) = (1 / N) ∑ᵢ yᵢ(d) = yᵀ(d) / N`.
Their estimator (1), `ŷᵀ_HT(d) = ∑ᵢ I(Dᵢ = d) Yᵢ / πᵢ(d)`, estimates the total
`yᵀ(d)`, and their Lemma 4.1 states `E[ŷᵀ_HT(d)] = ∑ᵢ yᵢ(d)`. `exposureHTTotal`
is that total estimator; dividing it by `N = Fintype.card α` estimates `μ(d)`
(`integral_exposureHTTotal_div_card`).

* `integral_exposureHTTotal_of_consistent` (Lemma 4.1 of Aronow and Samii,
  expectation part): if fixed exposure potentials `y i d` agree with the
  observed outcomes on the support of the design (their Conditions 1 and 2,
  which they state on the support `Ω = {z : p_z > 0}`, with the potentials
  given explicitly), and `πᵢ(d) > 0` for every unit, the estimator is
  design-unbiased for the total `∑ i, y i d`.
* `integral_exposureHTTotal`: the corollary under `ExposureSufficiency`, a
  design-free strengthening of their Condition 1 (required at every
  assignment, not only on the support), under which the potentials
  `exposurePotential e yr i d` are defined without reference to the design.
* `integral_exposureHTTotal_div_card_of_consistent`,
  `integral_exposureHTTotal_div_card`: the same for the mean estimator
  `exposureHTTotal / N` and the mean `μ(d)`.

The source assumes `0 < πᵢ(d) < 1`; only `0 < πᵢ(d)` is used here.

## References

- P. M. Aronow and C. Samii, "Estimating average causal effects under
  general interference, with application to a social network experiment",
  Annals of Applied Statistics 11(4) (2017), 1912-1947 (Conditions 1 and 2,
  estimator (1) and Lemma 4.1; numbering as in arXiv:1305.6156v4).
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

/-- Design-free form of Condition 1 of Aronow and Samii (2017), properly
specified exposure mapping: for every unit, the randomization outcomes agree
at any two assignments carrying the same exposure. The source quantifies over
the support `Ω = {z : p_z > 0}` of the design; requiring the condition at
every assignment makes `exposurePotential` independent of the design. The
support-restricted setting is `integral_exposureHTTotal_of_consistent`.
Individual SUTVA is not assumed. -/
def ExposureSufficiency {α Ω Δ : Type*} (e : α → Ω → Δ)
    (yr : α → Ω → ℝ) : Prop :=
  ∀ i z z', e i z = e i z' → yr i z = yr i z'

open Classical in
/-- Exposure-specific potential outcome `yᵢ(d)`: the randomization outcome
at some assignment giving unit `i` exposure `d` (junk value `0` if no
assignment does). Under `ExposureSufficiency` the choice does not matter
(`exposurePotential_eq_of_mem`), so this agrees with the source's choice of
an assignment in the support, and the definition does not depend on the
design. -/
noncomputable def exposurePotential {α Ω Δ : Type*}
    (e : α → Ω → Δ) (yr : α → Ω → ℝ) (i : α) (d : Δ) : ℝ :=
  if h : ∃ z, e i z = d then yr i (Classical.choose h) else 0

/-- Under Condition 1, the potential outcome agrees with `yr` at every
assignment carrying the exposure. -/
theorem exposurePotential_eq_of_mem {α Ω Δ : Type*}
    (e : α → Ω → Δ) (yr : α → Ω → ℝ) (hcond : ExposureSufficiency e yr)
    (i : α) (z : Ω) (d : Δ) (he : e i z = d) :
    exposurePotential e yr i d = yr i z := by
  unfold exposurePotential
  have hex : ∃ w, e i w = d := ⟨z, he⟩
  rw [dite_eq_left hex]
  exact hcond i _ z ((Classical.choose_spec hex).trans he.symm)

/-- Randomization outcomes factor through the exposure under Condition 1. -/
theorem exposurePotential_factorization {α Ω Δ : Type*}
    (e : α → Ω → Δ) (yr : α → Ω → ℝ) (hcond : ExposureSufficiency e yr)
    (i : α) (z : Ω) :
    yr i z = exposurePotential e yr i (e i z) :=
  (exposurePotential_eq_of_mem e yr hcond i z _ rfl).symm

/-- Horvitz-Thompson exposure-total estimator at assignment `z`
(Aronow and Samii (2017), estimator (1), `ŷᵀ_HT(d)`, which estimates the
total `yᵀ(d)`): the observed outcomes `yr i z` of the units with exposure
`d`, each weighted by `1 / πᵢ(d)`. Dividing by `N` gives the estimator of
the mean `μ(d)`. -/
noncomputable def exposureHTTotal {α Ω Δ : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq Δ] (e : α → Ω → Δ) (p : PMF Ω)
    (yr : α → Ω → ℝ) (d : Δ) (z : Ω) : ℝ :=
  ∑ i ∈ exposedSet e d z, yr i z / exposureProbability e p i d

/-- **Design-unbiasedness of the exposure-total estimator** (Aronow and
Samii (2017), Lemma 4.1, expectation part `E[ŷᵀ_HT(d)] = ∑ᵢ yᵢ(d)`), for
fixed exposure potentials `y` that agree with the observed outcomes on the
support of the design (the source's Conditions 1 and 2 on the support): with
`πᵢ(d) > 0` for every unit, the design expectation is the potential-outcome
total `∑ i, y i d`. Only positivity at `d` is needed; the source's
`πᵢ(d) < 1` is not. -/
theorem integral_exposureHTTotal_of_consistent {α Ω Δ : Type*}
    [Fintype α] [DecidableEq α] [Countable Ω] [DecidableEq Δ]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)]
    (e : α → Ω → Δ) (p : PMF Ω) (yr : α → Ω → ℝ) (y : α → Δ → ℝ)
    (hy : ∀ i z, p z ≠ 0 → yr i z = y i (e i z)) (d : Δ)
    (hpos : ∀ i, 0 < exposureProbability e p i d) :
    ∫ z, exposureHTTotal e p yr d z ∂p.toMeasure = ∑ i, y i d := by
  have hsupp : ∀ᵐ z ∂p.toMeasure, p z ≠ 0 := by
    rw [ae_iff]
    refine (p.toMeasure_apply_eq_zero_iff (Set.to_countable _).measurableSet).2 ?_
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hz' ((p.mem_support_iff z).1 hz)
  have hae : (fun z => exposureHTTotal e p yr d z) =ᵐ[p.toMeasure]
      (fun z => horvitzThompsonTotal (p.map (exposedSet e d))
        (fun i => y i d) (exposedSet e d z)) := by
    filter_upwards [hsupp] with z hz
    unfold exposureHTTotal horvitzThompsonTotal
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiz : e i z = d := by
      simpa only [exposedSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    rw [hy i z hz, hiz]
    rfl
  have hmeas : Measurable (exposedSet e d) := measurable_of_countable _
  have hAES : AEStronglyMeasurable
      (horvitzThompsonTotal (p.map (exposedSet e d)) (fun i => y i d))
      (Measure.map (exposedSet e d) p.toMeasure) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hAEM : AEMeasurable (exposedSet e d) p.toMeasure :=
    hmeas.aemeasurable
  rw [integral_congr_ae hae,
    ← MeasureTheory.integral_map (f := horvitzThompsonTotal (p.map (exposedSet e d))
      (fun i => y i d)) hAEM hAES,
    PMF.toMeasure_map _ _ hmeas]
  exact integral_horvitzThompsonTotal _ _ hpos

/-- **Design-unbiasedness under the design-free Condition 1**: if
`ExposureSufficiency e yr` holds and `πᵢ(d) > 0` for every unit, the
expectation of the estimator is `∑ i, exposurePotential e yr i d`. This is
`integral_exposureHTTotal_of_consistent` with the potentials
`exposurePotential e yr`, consistent at every assignment by
`exposurePotential_factorization`. -/
theorem integral_exposureHTTotal {α Ω Δ : Type*} [Fintype α]
    [DecidableEq α] [Countable Ω] [DecidableEq Δ] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [MeasurableSpace (Finset α)]
    [MeasurableSingletonClass (Finset α)] (e : α → Ω → Δ) (p : PMF Ω)
    (yr : α → Ω → ℝ) (hcond : ExposureSufficiency e yr) (d : Δ)
    (hpos : ∀ i, 0 < exposureProbability e p i d) :
    ∫ z, exposureHTTotal e p yr d z ∂p.toMeasure
      = ∑ i, exposurePotential e yr i d :=
  integral_exposureHTTotal_of_consistent e p yr (exposurePotential e yr)
    (fun i z _ => exposurePotential_factorization e yr hcond i z) d hpos

/-- The mean estimator `exposureHTTotal / N` is unbiased for the mean
`(1 / N) ∑ i, y i d` of fixed potentials that agree with the observed
outcomes on the design support. The identity also holds at `N = 0` under
Lean's division convention. -/
theorem integral_exposureHTTotal_div_card_of_consistent {α Ω Δ : Type*}
    [Fintype α] [DecidableEq α] [Countable Ω] [DecidableEq Δ]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)]
    (e : α → Ω → Δ) (p : PMF Ω) (yr : α → Ω → ℝ) (y : α → Δ → ℝ)
    (hy : ∀ i z, p z ≠ 0 → yr i z = y i (e i z)) (d : Δ)
    (hpos : ∀ i, 0 < exposureProbability e p i d) :
    ∫ z, exposureHTTotal e p yr d z / (Fintype.card α : ℝ) ∂p.toMeasure
      = (∑ i, y i d) / (Fintype.card α : ℝ) := by
  rw [MeasureTheory.integral_div,
    integral_exposureHTTotal_of_consistent e p yr y hy d hpos]

/-- **Design-unbiasedness of the mean estimator under the design-free
Condition 1**: the estimator `exposureHTTotal / N` of Aronow and Samii's estimand
`μ(d) = (1 / N) ∑ᵢ yᵢ(d)` is unbiased when `πᵢ(d) > 0` for every unit. The
identity also holds at `N = 0` under Lean's division convention. -/
theorem integral_exposureHTTotal_div_card {α Ω Δ : Type*} [Fintype α]
    [DecidableEq α] [Countable Ω] [DecidableEq Δ] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [MeasurableSpace (Finset α)]
    [MeasurableSingletonClass (Finset α)] (e : α → Ω → Δ) (p : PMF Ω)
    (yr : α → Ω → ℝ) (hcond : ExposureSufficiency e yr) (d : Δ)
    (hpos : ∀ i, 0 < exposureProbability e p i d) :
    ∫ z, exposureHTTotal e p yr d z / (Fintype.card α : ℝ) ∂p.toMeasure
      = (∑ i, exposurePotential e yr i d) / (Fintype.card α : ℝ) := by
  rw [MeasureTheory.integral_div, integral_exposureHTTotal e p yr hcond d hpos]

end MathlibExt.Probability.Causality
