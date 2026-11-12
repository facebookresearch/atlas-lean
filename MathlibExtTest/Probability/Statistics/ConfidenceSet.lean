/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ConfidenceSet
public import MathlibExt.Probability.Statistics.ExactTests.ClopperPearson
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics
open MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.ConfidenceSet

/-- The coverage section is the complement of the rejection set. -/
example {X T : Type*} (R : T → Set X) (t : T) :
    {x | t ∈ confSetOfTests R x} = (R t)ᶜ := by
  rfl

/-- Hence the coverage section is measurable exactly when the rejection set is: `hR` is the
measurability hypothesis of `coverage_iff_level` and cannot be dropped. -/
example {X T : Type*} [MeasurableSpace X] (R : T → Set X) (t : T) :
    MeasurableSet {x | t ∈ confSetOfTests R x} ↔ MeasurableSet (R t) := by
  exact MeasurableSet.compl_iff

/-- `α = 0` with empty rejection regions: coverage is `1`. -/
example {Θ X T : Type*} [MeasurableSpace X] (P : Θ → Measure X)
    [∀ θ, IsProbabilityMeasure (P θ)] (τ : Θ → T) (θ : Θ) :
    (P θ).real {x | τ θ ∈ confSetOfTests (fun _ : T => (∅ : Set X)) x} = 1 := by
  simp [confSetOfTests]

/-- `α = 1` with full rejection regions: level `1` holds and the confidence set is empty. -/
example {X T : Type*} (x : X) : confSetOfTests (fun _ : T => (Set.univ : Set X)) x = ∅ := by
  simp [confSetOfTests]

/-- Round trip: inverting the tests `t ↦ {x | t ∉ C x}` of a confidence set `C` returns `C`. -/
example {X T : Type*} (C : X → Set T) : confSetOfTests (fun t => {x | t ∉ C x}) = C := by
  ext x t
  simp [confSetOfTests]

/-- An estimand fiber with two parameters (`τ` constant on `Bool`) and different laws: the test
`{true}` has level `0` under `δ_false` but not under `δ_true`, so coverage `≥ 1` fails for one
member of the fiber. Level must hold at every parameter of the fiber. -/
example :
    ¬ ∀ θ : Bool, 1 - (0 : ℝ) ≤ (Measure.dirac θ).real
      {x | (fun _ : Bool => ()) θ ∈ confSetOfTests (fun _ : Unit => ({true} : Set Bool)) x} := by
  intro h
  have := h true
  norm_num [confSetOfTests, Measure.dirac_real_apply] at this

/-- **Use test: Clopper–Pearson through `confSetOfTests`.** The Clopper–Pearson interval is the
inversion of the tests that reject `t` when `t ∉ [L(x), U(x)]`; its Atlas coverage theorem
`ExactTests.clopperPearson_coverage` (provided) restates as coverage of `confSetOfTests` under
`Bin(n, p)`. -/
example (n : ℕ) (p : unitInterval) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    1 - α ≤ (binomial n p).real {x | p ∈ confSetOfTests
      (fun t : unitInterval => {k : ℕ | ¬ (ExactTests.clopperPearsonLower n k α ≤ t ∧
        (t : ℝ) ≤ ExactTests.clopperPearsonUpper n k α)}) x} := by
  simpa [confSetOfTests] using
    ExactTests.clopperPearson_coverage (HasLaw.id (μ := binomial n p)) hα0 hα1

/-- **Use test: the Clopper–Pearson tests have level `α`,** obtained from the coverage above
through `coverage_iff_level` (parameter = estimand = `p`). -/
example (n : ℕ) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ p : unitInterval, (binomial n p).real {k : ℕ | ¬ (ExactTests.clopperPearsonLower n k α ≤ p ∧
      (p : ℝ) ≤ ExactTests.clopperPearsonUpper n k α)} ≤ α := by
  refine (coverage_iff_level (fun q : unitInterval => binomial n q) id
    (fun t : unitInterval => {k : ℕ | ¬ (ExactTests.clopperPearsonLower n k α ≤ t ∧
      (t : ℝ) ≤ ExactTests.clopperPearsonUpper n k α)}) (fun _ => .of_discrete)).2 (fun q => ?_)
  simpa [confSetOfTests] using
    ExactTests.clopperPearson_coverage (HasLaw.id (μ := binomial n q)) hα0 hα1

end MathlibExtTest.Probability.Statistics.ConfidenceSet
