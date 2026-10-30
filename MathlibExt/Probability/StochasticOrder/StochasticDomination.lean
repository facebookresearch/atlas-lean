/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent

/-!
# Stochastic domination of measures on configuration space

A measure `μ` on `ConfigSpace E` is stochastically dominated by `ν`, written `μ ≼ ν`, if its
`ENNReal` mass satisfies `μ(A) ≤ ν(A)` for every measurable increasing event `A` (an event closed
under raising coordinates from `false` to `true`). This is the order used in the Holley and FKG
comparison inequalities and in the monotone construction of infinite-volume limits.

## Main definitions

* `StatMech.StochasticallyDominated μ ν` (notation `μ ≼ ν`, scoped): stochastic domination.

## Main results

* `StatMech.StochasticallyDominated.refl`, `StatMech.StochasticallyDominated.trans`: `≼` is a
  preorder.

Strassen's theorem, which characterizes `≼` by monotone couplings, is in
`MathlibExt.Probability.StochasticOrder.Strassen` and
`MathlibExt.Probability.StochasticOrder.StrassenFull`.

## References

* G. Grimmett, *The Random-Cluster Model*, Springer, 2006, Section 2.1.
-/

@[expose] public section

open MeasureTheory

namespace StatMech

variable {E : Type*}

/-- `μ` is stochastically dominated by `ν` if their actual `ENNReal` masses satisfy
`μ(A) ≤ ν(A)` for every measurable increasing event `A ⊆ ConfigSpace E`. -/
def StochasticallyDominated (μ ν : Measure (ConfigSpace E)) : Prop :=
  ∀ A : Set (ConfigSpace E), MeasurableSet A → IsIncreasing A → μ A ≤ ν A

@[inherit_doc]
scoped infix:50 " ≼ " => StochasticallyDominated

/-- Stochastic domination is reflexive. -/
@[refl] theorem StochasticallyDominated.refl (μ : Measure (ConfigSpace E)) : μ ≼ μ :=
  fun _ _ _ => le_refl _

/-- Stochastic domination is transitive. -/
theorem StochasticallyDominated.trans {μ ν ρ : Measure (ConfigSpace E)}
    (h₁ : μ ≼ ν) (h₂ : ν ≼ ρ) : μ ≼ ρ :=
  fun A hA hAinc => (h₁ A hA hAinc).trans (h₂ A hA hAinc)

/-- For a finite upper measure, stochastic domination also compares real-valued masses. -/
theorem StochasticallyDominated.real {μ ν : Measure (ConfigSpace E)} (h : μ ≼ ν)
    [IsFiniteMeasure ν] (A : Set (ConfigSpace E)) (hAm : MeasurableSet A)
    (hA : IsIncreasing A) : μ.real A ≤ ν.real A := by
  rw [measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top ν A) (h A hAm hA)

end StatMech
