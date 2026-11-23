/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.ConfigSpace
public import MathlibExt.Probability.ProductBondPercolation

/-!
# Bernoulli product measures on configuration space

The Bernoulli product measure with parameter `p ∈ [0, 1]` on `ConfigSpace E = E → Bool` makes the
coordinates independent, each `true` with probability `p`. It is the law of Bernoulli site or bond
percolation, and the reference measure of the random-cluster and Ising models.

## Main definitions

* `StatMech.bernoulliMeasure p hp`: the Bernoulli distribution on `Bool`; it is Mathlib's
  `ProbabilityTheory.bernoulliMeasure true false p`.
* `StatMech.bernoulliProductMeasure p hp`: the product measure `Measure.infinitePi` of copies of
  `bernoulliMeasure p hp`.

## Main results

* `StatMech.bernoulliProductMeasure.real_singleton`: for finite `E`, the mass of a configuration
  is `∏ e, p^{ω e} (1 - p)^{1 - ω e}`.
* `StatMech.bernoulliProductMeasure.real_eq_sum`,
  `StatMech.bernoulliProductMeasure.sum_real_singleton`: finite sums of configuration masses.
* `StatMech.bernoulliProductMeasure.real_singleton_logModular`: the weights satisfy
  `w(a) w(b) = w(a ⊔ b) w(a ⊓ b)`, so the FKG lattice condition holds with equality.
* `StatMech.bernoulliProductMeasure_eq_gbernoulliLaw`: on bond configurations this is the law
  `MathlibExt.Probability.ProductBondPercolation.gbernoulliLaw`.

Mathlib's `ProbabilityTheory.setBernoulli` is the same product measure on `Set E` instead of
`E → Bool`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatMech

variable {E : Type*}

/-- The Bernoulli distribution on `Bool` with success probability `p`: mass `p` on `true` and
`1 - p` on `false`. This is Mathlib's `ProbabilityTheory.bernoulliMeasure true false p`, with the
parameter given as an `ℝ≥0` bounded by `1`. -/
noncomputable def bernoulliMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false ⟨p, p.2, hp⟩

/-- `bernoulliMeasure p hp` is Mathlib's `ProbabilityTheory.bernoulliMeasure true false p`. -/
lemma bernoulliMeasure_eq (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliMeasure p hp = ProbabilityTheory.bernoulliMeasure true false ⟨p, p.2, hp⟩ := rfl

/-- The Bernoulli distribution is a probability measure. -/
instance (p : ℝ≥0) (hp : p ≤ 1) : IsProbabilityMeasure (bernoulliMeasure p hp) := by
  unfold bernoulliMeasure; infer_instance

@[simp] lemma bernoulliMeasure_apply_true (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliMeasure p hp {true} = (p : ℝ≥0∞) := by
  classical
  rw [bernoulliMeasure, ProbabilityTheory.bernoulliMeasure_apply _ (measurableSet_singleton _)]
  simp only [Set.mem_singleton_iff, ite_true, Bool.false_eq_true, ite_false]
  rfl

@[simp] lemma bernoulliMeasure_apply_false (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliMeasure p hp {false} = ((1 - p : ℝ≥0) : ℝ≥0∞) := by
  classical
  rw [bernoulliMeasure, ProbabilityTheory.bernoulliMeasure_apply _ (measurableSet_singleton _)]
  simp only [Set.mem_singleton_iff, Bool.true_eq_false, ite_false, ite_true]
  congr 1
  ext
  rw [NNReal.coe_sub hp]
  rfl

/-- The Bernoulli product measure on `ConfigSpace E`: the coordinates are independent and each is
`true` with probability `p` (`Measure.infinitePi` of `bernoulliMeasure p hp`). See also Mathlib's
`ProbabilityTheory.setBernoulli`, the same product measure on `Set E`. -/
noncomputable def bernoulliProductMeasure (p : ℝ≥0) (hp : p ≤ 1) :
    Measure (ConfigSpace E) :=
  Measure.infinitePi (fun _ : E => bernoulliMeasure p hp)

/-- The Bernoulli product measure is a probability measure. -/
instance (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernoulliProductMeasure (E := E) p hp) := by
  unfold bernoulliProductMeasure; infer_instance

/-- On bond configurations `Sym2 V → Bool`, `bernoulliProductMeasure` is the bond percolation law
`MathlibExt.Probability.ProductBondPercolation.gbernoulliLaw`. -/
lemma bernoulliProductMeasure_eq_gbernoulliLaw {V : Type*} (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliProductMeasure (E := Sym2 V) p hp
      = MathlibExt.Probability.ProductBondPercolation.gbernoulliLaw (p : ℝ) p.2 hp := rfl

namespace bernoulliProductMeasure

variable {p : ℝ≥0} {hp : p ≤ 1}

/-- For finite `E`, the mass of a configuration is the product of its coordinate masses. -/
theorem apply_singleton [Fintype E] (ω : ConfigSpace E) :
    bernoulliProductMeasure (E := E) p hp {ω} = ∏ e, bernoulliMeasure p hp {ω e} := by
  unfold bernoulliProductMeasure
  rw [Measure.infinitePi_singleton_of_fintype]

/-- For finite `E`, the mass of a configuration is the product of its coordinate masses. -/
theorem real_singleton [Fintype E] (ω : ConfigSpace E) :
    (bernoulliProductMeasure (E := E) p hp).real {ω}
      = ∏ e, (bernoulliMeasure p hp).real {ω e} := by
  rw [Measure.real, apply_singleton, ENNReal.toReal_prod]
  rfl

/-- For finite `E`, the probability of an event is the sum of the masses of its configurations. -/
theorem real_eq_sum [Fintype E] [DecidableEq E] (S : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real S
      = ∑ ω : ConfigSpace E,
          S.indicator (fun _ => (1 : ℝ)) ω * (bernoulliProductMeasure (E := E) p hp).real {ω} := by
  classical
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  have key : μ.real S = ∑ ω ∈ Finset.univ.filter (· ∈ S), μ.real {ω} := by
    have h1 : μ S = ∑ ω ∈ Finset.univ.filter (· ∈ S), μ {ω} := by
      rw [sum_measure_singleton]; congr 1; ext x; simp
    rw [Measure.real, h1, ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
    rfl
  rw [key, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases h : ω ∈ S
  · rw [ite_eq_left h, Set.indicator_of_mem h]; ring
  · rw [ite_eq_right h, Set.indicator_of_notMem h]; ring

/-- Configuration masses are nonnegative. -/
theorem real_singleton_nonneg (ω : ConfigSpace E) :
    0 ≤ (bernoulliProductMeasure (E := E) p hp).real {ω} :=
  ENNReal.toReal_nonneg

/-- For finite `E`, the configuration masses sum to `1`. -/
theorem sum_real_singleton [Fintype E] [DecidableEq E] :
    ∑ ω : ConfigSpace E, (bernoulliProductMeasure (E := E) p hp).real {ω} = 1 := by
  classical
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  have h : ∑ ω : ConfigSpace E, μ {ω} = μ Set.univ := by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
  have h2 : ∑ ω : ConfigSpace E, μ.real {ω} = (μ Set.univ).toReal := by
    simp only [Measure.real]
    rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top _ _), h]
  rw [h2, measure_univ, ENNReal.toReal_one]

set_option linter.unusedFintypeInType false in
/-- The configuration weights of a Bernoulli product measure are log-modular:
`w(a) w(b) = w(a ⊔ b) w(a ⊓ b)`. In particular they satisfy the FKG lattice condition. -/
theorem real_singleton_logModular [Fintype E] (a b : ConfigSpace E) :
    (bernoulliProductMeasure (E := E) p hp).real {a}
        * (bernoulliProductMeasure (E := E) p hp).real {b}
      = (bernoulliProductMeasure (E := E) p hp).real {a ⊔ b}
        * (bernoulliProductMeasure (E := E) p hp).real {a ⊓ b} := by
  have coord : ∀ (φ : Bool → ℝ) (x y : Bool), φ x * φ y = φ (x ⊔ y) * φ (x ⊓ y) := by
    intro φ x y
    rcases le_total x y with h | h
    · rw [sup_eq_right.mpr h, inf_eq_left.mpr h]; ring
    · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]
  simp_rw [real_singleton]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  simp only [Pi.sup_apply, Pi.inf_apply]
  exact coord (fun b => (bernoulliMeasure p hp).real {b}) (a e) (b e)

end bernoulliProductMeasure

end StatMech
