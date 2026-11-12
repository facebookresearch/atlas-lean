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
measurability hypothesis of `level_iff_coverage` and cannot be dropped. -/
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
through `level_iff_coverage` (parameter = estimand = `p`). -/
example (n : ℕ) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ p : unitInterval, (binomial n p).real {k : ℕ | ¬ (ExactTests.clopperPearsonLower n k α ≤ p ∧
      (p : ℝ) ≤ ExactTests.clopperPearsonUpper n k α)} ≤ α := by
  refine (level_iff_coverage (fun q : unitInterval => binomial n q) id
    (fun t : unitInterval => {k : ℕ | ¬ (ExactTests.clopperPearsonLower n k α ≤ t ∧
      (t : ℝ) ≤ ExactTests.clopperPearsonUpper n k α)}) (fun _ => .of_discrete)).2 (fun q => ?_)
  simpa [confSetOfTests] using
    ExactTests.clopperPearson_coverage (HasLaw.id (μ := binomial n q)) hα0 hα1

/-- Use: the inclusion can be equality. -/
example {Θ X T : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (τ : Θ → T) {C : X → Set T} {α : ℝ}
    (hcov : ∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ C x}) (θ : Θ) :
    1 - α ≤ (P θ).real {x | τ θ ∈ C x} := by
  exact coverage_mono_of_subset P τ (fun x => Set.Subset.rfl) hcov θ

/-- Use: rounding outward to the trivial set gives coverage `1`. -/
example {Θ X T : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (τ : Θ → T) {C : X → Set T} {α : ℝ}
    (hcov : ∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ C x}) (θ : Θ) :
    1 - α ≤ (P θ).real {x | τ θ ∈ (fun _ => Set.univ) x} := by
  exact coverage_mono_of_subset P τ (fun x _ _ => Set.mem_univ _) hcov θ

/-- Negative: a shrunken computed set can lose coverage (Bool-parameter model). -/
example : ∃ (P : Bool → Measure ℕ) (_ : ∀ θ, IsProbabilityMeasure (P θ))
    (τ : Bool → ℕ) (C C' : ℕ → Set ℕ) (α : ℝ),
    (∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ C x})
      ∧ ∃ θ, (P θ).real {x | τ θ ∈ C' x} < 1 - α := by
  refine ⟨fun _ => Measure.dirac 0, fun _ => inferInstance, fun _ => 0,
    fun _ => Set.univ, fun _ => ∅, 0, ?_, ?_⟩
  · intro θ
    simp [probReal_univ]
  · exact ⟨false, by simp [measureReal_empty]⟩

/-- Use: `ε = 0` with pointwise inclusion recovers `coverage_mono_of_subset`. -/
example {Θ X T : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (τ : Θ → T) {C C' : X → Set T} {α : ℝ}
    (hsub : ∀ x, C x ⊆ C' x)
    (hcov : ∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ C x}) (θ : Θ) :
    1 - α - 0 ≤ (P θ).real {x | τ θ ∈ C' x} := by
  have h := coverage_of_subset_ae_budget (C' := C') (ε := fun _ => (0 : ℝ)) P τ hcov ?hbad θ
  · exact h
  · intro θ'
    have hempty : {x | τ θ' ∈ C x ∧ τ θ' ∉ C' x} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact h.2 (hsub x h.1)
    rw [hempty, measureReal_empty]

/-- Negative: a budget on the wrong event (misses where `C'` adds points) proves nothing. -/
example : ∃ (P : Bool → Measure ℕ) (_ : ∀ θ, IsProbabilityMeasure (P θ))
    (τ : Bool → ℕ) (C C' : ℕ → Set ℕ) (α ε : ℝ),
    (∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ C x})
      ∧ (∀ θ, (P θ).real {x | τ θ ∉ C x ∧ τ θ ∈ C' x} ≤ ε)
      ∧ ∃ θ, (P θ).real {x | τ θ ∈ C' x} < 1 - α - ε := by
  refine ⟨fun _ => Measure.dirac 0, fun _ => inferInstance, fun _ => 0,
    fun _ => ({0} : Set ℕ), fun _ => (∅ : Set ℕ), 0, 0, ?_, ?_, ?_⟩
  · intro θ
    show (1 : ℝ) - 0 ≤ (Measure.dirac 0).real {x : ℕ | (0 : ℕ) ∈ ({0} : Set ℕ)}
    have hset : {x : ℕ | (0 : ℕ) ∈ ({0} : Set ℕ)} = Set.univ := by ext x; simp
    rw [hset, probReal_univ]
    norm_num
  · intro θ
    show (Measure.dirac 0).real
      {x : ℕ | (0 : ℕ) ∉ ({0} : Set ℕ) ∧ (0 : ℕ) ∈ (∅ : Set ℕ)} ≤ (0 : ℝ)
    have hset : {x : ℕ | (0 : ℕ) ∉ ({0} : Set ℕ) ∧ (0 : ℕ) ∈ (∅ : Set ℕ)} = ∅ := by
      ext x; simp
    rw [hset, measureReal_empty]
  · refine ⟨true, ?_⟩
    show (Measure.dirac 0).real {x : ℕ | (0 : ℕ) ∈ (∅ : Set ℕ)} < 1 - 0 - 0
    have hset : {x : ℕ | (0 : ℕ) ∈ (∅ : Set ℕ)} = ∅ := by ext x; simp
    rw [hset, measureReal_empty]
    norm_num

end MathlibExtTest.Probability.Statistics.ConfidenceSet
