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
/-- A fair coin on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairCoin := by
  constructor
  simp [fairCoin, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- Positive: exact non-rejected-image inversion is the reflexive case, over a countable
parameter space so the estimand-fiber union is measurable. -/
example {Θ X T : Type*} [MeasurableSpace X] [Countable Θ]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (τ : Θ → T)
    (R : Θ → Set X) (hR : ∀ θ, MeasurableSet (R θ))
    {α : ℝ} (hα : α ∈ Set.Icc 0 1) (hlev : ∀ θ, (P θ).real (R θ) ≤ α) :
    ∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ {t | ∃ θ', τ θ' = t ∧ x ∉ R θ'}} := by
  exact MathlibExt.Probability.Statistics.coverage_of_projected_pointTests P τ R hR hα hlev
    (fun x => {t | ∃ θ', τ θ' = t ∧ x ∉ R θ'}) (fun _ => Set.Subset.rfl) (fun θ => by
      have heq : {x | τ θ ∈ {t | ∃ θ', τ θ' = t ∧ x ∉ R θ'}}
          = ⋃ (θ' : Θ), {x | τ θ' = τ θ ∧ x ∉ R θ'} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      rw [heq]
      exact MeasurableSet.iUnion fun θ' => by
        by_cases h : τ θ' = τ θ
        · have hset : {x | τ θ' = τ θ ∧ x ∉ R θ'} = (R θ')ᶜ := by
            ext x
            simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, h, true_and]
          rw [hset]
          exact (hR θ').compl
        · have hset : {x | τ θ' = τ θ ∧ x ∉ R θ'} = ∅ := by
            ext x
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
            exact fun hτ => absurd hτ h
          rw [hset]
          exact MeasurableSet.empty)

/-- Boundary: enlarging to everything keeps coverage. -/
example {Θ X T : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (τ : Θ → T)
    (R : Θ → Set X) (hR : ∀ θ, MeasurableSet (R θ))
    {α : ℝ} (hα : α ∈ Set.Icc 0 1) (hlev : ∀ θ, (P θ).real (R θ) ≤ α) :
    ∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ (Set.univ : Set T)} := by
  exact MathlibExt.Probability.Statistics.coverage_of_projected_pointTests P τ R hR hα hlev
    (fun _ => Set.univ) (fun _ => Set.subset_univ _) (fun _ => MeasurableSet.univ)

/-- Negative: dropping the image inclusion falsifies coverage. Here level holds and
`α = 1 / 2`, but `false` is not rejected while `C false` is empty, so the projected event
is empty and `1 - α` is positive. -/
example :
    let P : Bool → Measure Bool := fun _ => fairCoin;
    let τ : Bool → Unit := fun _ => ();
    let R : Bool → Set Bool := fun _ => {true};
    let α : ℝ := 1 / 2;
    let C : Bool → Set Unit := fun _ => ∅;
    (α ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ θ, MeasurableSet (R θ)) ∧
    (∀ θ, (P θ).real (R θ) ≤ α) ∧
    ¬ (∀ x, {t | ∃ θ, τ θ = t ∧ x ∉ R θ} ⊆ C x) ∧
    ¬ (∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ C x}) := by
  have hFairTrue : fairCoin.real {true} = 1 / 2 := by
    have hmeas : MeasurableSet ({true} : Set Bool) := MeasurableSet.singleton true
    have h1 : (Measure.dirac true) {true} = 1 := Measure.dirac_apply_of_mem (by simp)
    have h0 : (Measure.dirac false) {true} = 0 :=
      (dirac_eq_zero_iff_not_mem hmeas).mpr (by simp)
    unfold fairCoin
    rw [measureReal_def, Measure.smul_apply, Measure.add_apply, h1, h0, add_zero,
      smul_eq_mul, mul_one]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (1 / 2 : ℝ) ∈ Set.Icc 0 1
    constructor <;> norm_num
  · intro θ
    exact MeasurableSet.singleton true
  · intro θ
    show fairCoin.real {true} ≤ 1 / 2
    exact hFairTrue.le
  · intro h
    have hfalse := h false
    have hcon := hfalse ⟨false, rfl, by simp⟩
    simp at hcon
  · intro hcov
    have h0 := hcov false
    have h0' : (1 : ℝ) - 1 / 2 ≤ fairCoin.real ∅ := h0
    rw [measureReal_empty] at h0'
    norm_num at h0'

/-- Strict conservativeness: two same-estimand parameters with different rejection regions.
`R false = ∅` never rejects while `R true = {true}` rejects half the time, so the projected
set is everything and coverage is `1`, strictly above `1 - 1 / 2`. -/
example :
    let P : Bool → Measure Bool := fun _ => fairCoin;
    let R : Bool → Set Bool := fun b => if b then {true} else ∅;
    let C : Bool → Set Unit := fun _ => {()};
    (∀ θ, (P θ).real (R θ) ≤ 1 / 2) ∧
    (∀ θ, 1 - (1 / 2 : ℝ) ≤ (P θ).real {x | (fun _ : Bool => ()) θ ∈ C x}) ∧
    (∃ θ, (1 / 2 : ℝ) < (P θ).real {x | (fun _ : Bool => ()) θ ∈ C x}) := by
  have hFairTrue : fairCoin.real {true} = 1 / 2 := by
    have hmeas : MeasurableSet ({true} : Set Bool) := MeasurableSet.singleton true
    have h1 : (Measure.dirac true) {true} = 1 := Measure.dirac_apply_of_mem (by simp)
    have h0 : (Measure.dirac false) {true} = 0 :=
      (dirac_eq_zero_iff_not_mem hmeas).mpr (by simp)
    unfold fairCoin
    rw [measureReal_def, Measure.smul_apply, Measure.add_apply, h1, h0, add_zero,
      smul_eq_mul, mul_one]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro θ
    cases θ
    · show fairCoin.real ∅ ≤ 1 / 2
      rw [measureReal_empty]
      norm_num
    · show fairCoin.real {true} ≤ 1 / 2
      exact hFairTrue.le
  · intro θ
    have hev : {x : Bool | (fun _ : Bool => ()) θ ∈ (fun _ : Bool => ({()} : Set Unit)) x} =
        Set.univ := by
      ext x
      simp
    rw [hev]
    show (1 : ℝ) - 1 / 2 ≤ fairCoin.real Set.univ
    rw [probReal_univ]
    norm_num
  · refine ⟨false, ?_⟩
    have hev : {x : Bool | (fun _ : Bool => ()) false ∈ (fun _ : Bool => ({()} : Set Unit)) x} =
        Set.univ := by
      ext x
      simp
    rw [hev]
    show (1 / 2 : ℝ) < fairCoin.real Set.univ
    rw [probReal_univ]
    norm_num

/-- Use: the theorem applies the cutoff hypothesis directly. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hT : HasLaw (fun _ : Ω => (5 : ℝ)) (Measure.dirac (5 : ℝ)) P)
    (c : ℝ) (hc : 1 - (0 : ℝ) ≤ cdf (Measure.dirac (5 : ℝ)) c) :
    P.real {_ω | c < (5 : ℝ)} ≤ (0 : ℝ) := by
  exact measureReal_lt_le_of_le_cdf hT hc

/-- Negative: below the quantile the level fails; at `c = 0` a point mass at `5` rejects everything. -/
example : (Measure.dirac (5 : ℝ)).real {ω | (0 : ℝ) < ω} > (0.05 : ℝ) := by
  have hmem : (5 : ℝ) ∈ {ω : ℝ | (0 : ℝ) < ω} := by
    show (0 : ℝ) < (5 : ℝ)
    norm_num
  rw [measureReal_def, Measure.dirac_apply_of_mem hmem, ENNReal.toReal_one]
  norm_num

end MathlibExtTest.Probability.Statistics.ConfidenceSet
