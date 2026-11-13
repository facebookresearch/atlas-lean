/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import MathlibExt.SetTheory.Cardinal.LargeCardinal.RealValued

@[expose] public section

open Set Cardinal Function MeasureTheory

namespace MathlibExtTest.SetTheory.Cardinal.LargeCardinal.RealValued

open MetaMathlibExt

-- Logic 57: Nontrivial probability measure

/-- Sanity check: no countable set carries a nontrivial probability measure on all of its
subsets.  `univ` is the disjoint union of its singletons, so σ-additivity forces
`1 = μ univ = ∑' n, μ {n} = 0`.

This check shows both conjuncts are load-bearing — drop
`IsProbabilityMeasure` and `μ = 0` qualifies; drop `NullSingletonClass` and the Dirac measure `δ₀`
does.  And it exercises the `⊤`: `measure_iUnion`'s measurability side condition is
discharged by `MeasurableSpace.measurableSet_top`. -/

theorem not_isNontrivialProbMeasure_nat (μ : @Measure ℕ ⊤) :
    ¬ IsNontrivialProbabilityMeasure μ := by
  rintro ⟨hprob, hatom⟩
  let : MeasurableSpace ℕ := ⊤
  have := hprob
  have := hatom
  have hcover : (Set.univ : Set ℕ) = ⋃ n, ({n} : Set ℕ) := by
    ext m; simp
  have hdisj : Pairwise (Function.onFun Disjoint (fun n => ({n} : Set ℕ))) := by
    intro m n hmn
    simpa [Function.onFun] using hmn
  have h1 : μ (Set.univ : Set ℕ) = ∑' n, μ ({n} : Set ℕ) := by
    rw [hcover]
    exact measure_iUnion hdisj fun _ => MeasurableSpace.measurableSet_top
  rw [measure_univ] at h1
  simp [measure_singleton] at h1

-- Logic 333: Carries nontrivial measure

theorem aleph0_lt_of_carriesNontrivialMeasure.{u} {c : Cardinal.{u}}
    (h : CarriesNontrivialMeasure c) : ℵ₀ < c := by
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨I, hI, μ, hμ⟩ := h
  letI: MeasurableSpace I := ⊤
  have : Countable I := Cardinal.mk_le_aleph0_iff.1 (hI ▸ hle)
  have := hμ.1
  have := hμ.2
  have h0 : μ (Set.univ : Set I) = 0 := Set.countable_univ.measure_zero μ
  rw [measure_univ] at h0
  exact one_ne_zero h0

-- Logic 334: Least cardinal that carries nontrivial measure

/-- Sanity check: the `IsLeast` packaging unfolds to exactly the two clauses of
the English statement — κ carries a nontrivial measure, and no smaller cardinal
does. -/

theorem isLeast_spec.{u} (κ : Cardinal.{u}) :
    IsLeastCardinalWithNontrivialMeasure κ ↔
      (CarriesNontrivialMeasure κ ∧
        ∀ c : Cardinal.{u}, c < κ → ¬ CarriesNontrivialMeasure c) := by
  constructor
  · intro h
    exact ⟨h.1, fun c hc hcar => absurd (h.2 hcar) (not_le.2 hc)⟩
  · intro h
    exact ⟨h.1, fun c hcar => not_lt.1 fun hlt => h.2 c hlt hcar⟩

-- Logic 58: Null ideal

theorem nullIdeal_downward.{u} {I : Type u} [MeasurableSpace I] (μ : Measure I)
    {A B : Set I} (hB : B ∈ nullIdeal μ) (hAB : A ⊆ B) : A ∈ nullIdeal μ := by
  have hB' : μ B = 0 := hB
  have h : μ A ≤ μ B := measure_mono hAB
  rw [hB'] at h
  exact le_antisymm h zero_le

end MathlibExtTest.SetTheory.Cardinal.LargeCardinal.RealValued

end
