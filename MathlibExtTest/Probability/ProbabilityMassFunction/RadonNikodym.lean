/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ProbabilityMassFunction.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-!
# Tests for Radon–Nikodym derivatives at atoms and of probability mass functions
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.ProbabilityMassFunction.RadonNikodym

/-- The law on `Bool` with mass `a` at `true` and `b` at `false`. -/
noncomputable def coin (a b : ℝ≥0) (h : a + b = 1) : PMF Bool :=
  PMF.ofFintype (fun x => ((cond x a b : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, ← ENNReal.coe_add, h, ENNReal.coe_one])

theorem coin_apply (a b : ℝ≥0) (h : a + b = 1) (x : Bool) :
    coin a b h x = ((cond x a b : ℝ≥0) : ℝ≥0∞) :=
  PMF.ofFintype_apply _ x

/-- Masses `1/2, 1/2`. -/
noncomputable def P : PMF Bool := coin (1 / 2) (1 / 2) (by norm_num)

/-- Masses `1/4, 3/4`. -/
noncomputable def Q : PMF Bool := coin (1 / 4) (3 / 4) (by norm_num)

/-! ### The general lemma -/

/-- A non-probability measure against counting measure: `3 • δ_true` has derivative `3` at
`true` and `0` at `false`. -/
example : (3 • Measure.dirac true : Measure Bool).rnDeriv Measure.count true = 3 := by
  rw [Measure.rnDeriv_eq_measure_singleton_div _ _ (by simp) (by simp)]
  simp

example : (3 • Measure.dirac true : Measure Bool).rnDeriv Measure.count false = 0 := by
  rw [Measure.rnDeriv_eq_measure_singleton_div _ _ (by simp) (by simp)]
  simp

/-- A reference mass other than `1` at the atom: against `2 • count`, the measure `3 • δ_true`
has derivative `3 / 2` at `true`, so the division by `ν {x}` matters. -/
example : (3 • Measure.dirac true : Measure Bool).rnDeriv (2 • Measure.count) true = 3 / 2 := by
  rw [Measure.rnDeriv_eq_measure_singleton_div _ _ (by simp) (by simp)]
  simp

/-- Absolute continuity is not needed: `δ_true + δ_false` is not absolutely continuous with
respect to `δ_true`, yet its derivative at the atom `true` is pinned to `1`. -/
example : ¬ (Measure.dirac true + Measure.dirac false : Measure Bool) ≪ Measure.dirac true := by
  intro h
  have h1 := h (s := {false}) (by simp)
  simp at h1

example :
    (Measure.dirac true + Measure.dirac false : Measure Bool).rnDeriv (Measure.dirac true) true =
      1 := by
  rw [Measure.rnDeriv_eq_measure_singleton_div _ _ (by simp) (by simp)]
  simp

/-! ### PMF measures -/

/-- The mass ratio at `true`: `(1/2) / (1/4) = 2`. -/
example : P.toMeasure.rnDeriv Q.toMeasure true = 2 := by
  rw [PMF.rnDeriv_toMeasure_apply _ _ (by simp [Q, coin_apply]), P, Q, coin_apply, coin_apply,
    Bool.cond_true, Bool.cond_true, ← ENNReal.coe_div (by norm_num)]
  norm_num

/-- The mass ratio at `false`: `(1/2) / (3/4) = 2/3`. -/
example : P.toMeasure.rnDeriv Q.toMeasure false = ((2 / 3 : ℝ≥0) : ℝ≥0∞) := by
  rw [PMF.rnDeriv_toMeasure_apply _ _ (by simp [Q, coin_apply]), P, Q, coin_apply, coin_apply,
    Bool.cond_false, Bool.cond_false, ← ENNReal.coe_div (by norm_num)]
  norm_num

/-- Support inclusion gives absolute continuity of a point mass inside a full-support law. -/
example : (PMF.pure true).toMeasure ≪ Q.toMeasure :=
  PMF.toMeasure_absolutelyContinuous_iff.mpr fun x _ => by
    rw [PMF.mem_support_iff, Q, coin_apply]
    cases x <;> norm_num

/-- Disjoint point masses are not absolutely continuous. -/
example : ¬ (PMF.pure true).toMeasure ≪ (PMF.pure false).toMeasure := by
  rw [PMF.toMeasure_absolutelyContinuous_iff, PMF.support_pure, PMF.support_pure]
  simp

/-- Measurable singletons cannot be dropped: under the trivial σ-algebra the point masses at
`true` and `false` have the same measure, so absolute continuity holds without support
inclusion. -/
example : @Measure.AbsolutelyContinuous Bool ⊥ (@PMF.toMeasure Bool ⊥ (PMF.pure true))
      (@PMF.toMeasure Bool ⊥ (PMF.pure false)) ∧
    ¬ (PMF.pure true).support ⊆ (PMF.pure false).support := by
  let : MeasurableSpace Bool := ⊥
  have h : (PMF.pure true).toMeasure = (PMF.pure false).toMeasure := Measure.ext fun s hs => by
    rcases MeasurableSpace.measurableSet_bot_iff.mp hs with rfl | rfl <;>
      simp only [measure_empty, measure_univ]
  refine ⟨h ▸ Measure.AbsolutelyContinuous.rfl, ?_⟩
  rw [PMF.support_pure, PMF.support_pure]
  simp

/-! ### Necessity of the hypotheses -/

/-- The finiteness hypothesis `ν {x} ≠ ∞` cannot be dropped: for `μ = ν = ∞ • δ_x`, at a point
`x` of any measurable space, `μ.rnDeriv ν x` is nonzero, while `μ {x} / ν {x} = ∞ / ∞ = 0`. -/
example {α : Type*} [MeasurableSpace α] (x : α) :
    (∞ • Measure.dirac x : Measure α).rnDeriv (∞ • Measure.dirac x) x ≠
      (∞ • Measure.dirac x : Measure α) {x} / (∞ • Measure.dirac x : Measure α) {x} := by
  set ν : Measure α := ∞ • Measure.dirac x with hν
  have htop : ν {x} = ∞ := by simp [hν]
  rw [htop, ENNReal.div_top]
  have h := Measure.eq_withDensity_rnDeriv (s := 0) (f := 1) measurable_const
    Measure.MutuallySingular.zero_left (by rw [withDensity_one, zero_add] : ν = 0 + ν.withDensity 1)
  rw [withDensity_one] at h
  intro hz
  have hZ : MeasurableSet (ν.rnDeriv ν ⁻¹' {0}) :=
    Measure.measurable_rnDeriv ν ν (measurableSet_singleton 0)
  have h1 : ν (ν.rnDeriv ν ⁻¹' {0}) = ∞ := by
    rw [hν, smul_apply, Measure.dirac_apply' _ hZ, Set.indicator_of_mem (by exact hz)]
    simp
  have h2 : ν.withDensity (ν.rnDeriv ν) (ν.rnDeriv ν ⁻¹' {0}) = 0 := by
    rw [withDensity_apply _ hZ]
    exact setLIntegral_eq_zero hZ fun y hy => hy
  rw [← h, h1] at h2
  exact ENNReal.top_ne_zero h2

/-- The PMF mass-ratio formula needs measurable singletons: under the trivial `σ`-algebra,
`pure true` against the coin `Q` of masses `1/4, 3/4` violates it at `false`, where the
derivative is `1` but the mass ratio is `0 / (3 / 4) = 0`. -/
example : ∃ x, (@PMF.toMeasure Bool ⊥ (PMF.pure true)).rnDeriv (@PMF.toMeasure Bool ⊥ Q) x ≠
    (PMF.pure true) x / Q x := by
  let : MeasurableSpace Bool := ⊥
  have hmeas_eq : (@PMF.toMeasure Bool ⊥ (PMF.pure true)) = (@PMF.toMeasure Bool ⊥ Q) :=
    Measure.ext fun s hs => by
      rcases MeasurableSpace.measurableSet_bot_iff.mp hs with rfl | rfl <;>
        simp only [measure_empty, measure_univ]
  rw [hmeas_eq]
  have hself := Measure.rnDeriv_self (@PMF.toMeasure Bool ⊥ Q)
  have hnull : (@PMF.toMeasure Bool ⊥ Q) {y | (@PMF.toMeasure Bool ⊥ Q).rnDeriv
      (@PMF.toMeasure Bool ⊥ Q) y ≠ 1} = 0 := mem_ae_iff.mp hself
  have hmeas : MeasurableSet {y : Bool | (@PMF.toMeasure Bool ⊥ Q).rnDeriv
      (@PMF.toMeasure Bool ⊥ Q) y ≠ 1} :=
    ((Measure.measurable_rnDeriv _ _) (measurableSet_singleton (1 : ℝ≥0∞))).compl
  rcases MeasurableSpace.measurableSet_bot_iff.mp hmeas with h | h
  · have hfalse : (@PMF.toMeasure Bool ⊥ Q).rnDeriv (@PMF.toMeasure Bool ⊥ Q) false = 1 := by
      have hnm := Set.eq_empty_iff_forall_notMem.mp h false
      simpa using hnm
    refine ⟨false, ?_⟩
    rw [hfalse, PMF.pure_apply_of_ne _ _ (by decide)]
    simp
  · rw [h, measure_univ] at hnull
    exact absurd hnull one_ne_zero

end MathlibExtTest.Probability.ProbabilityMassFunction.RadonNikodym
