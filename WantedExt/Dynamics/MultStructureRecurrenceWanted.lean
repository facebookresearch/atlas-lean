/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
AMR-047-0034: In a measure-preserving system with multiplicative
structure, does every positive-measure A satisfy μ(T_{2mn}A ∩
T_{(m-n)(m+n)}A) > 0 for some m > n?
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Dynamics.MultStructureRecurrenceWanted

universe u

/-! Source record `AMR-047-0034`. Concrete formulation: a
multiplicative action `T : ℕ → (X ≃ᵐ X)` (that is,
`T (a * b) = T a * T b` and `T 1 = 1`) by measure-preserving
equivalences. -/

/-- [AMR-047-0034] For every multiplicative measure-preserving action
by bimeasurable transformations (measurable equivalences), indexed
by the positive naturals so the action is not collapsed by a zero
index, and every measurable set `A` of positive measure, there exist
positive `m > n` with
`μ(T_{2mn} '' A ∩ T_{(m-n)(m+n)} '' A) > 0`. (Resolved: see the
registry status.) -/
def conjecture : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ]
    (T : ℕ+ → (X ≃ᵐ X)),
    T 1 = MeasurableEquiv.refl X →
    (∀ a b : ℕ+, (T (a * b)).toEquiv = (T a).toEquiv * (T b).toEquiv) →
    (∀ a, MeasureTheory.MeasurePreserving (T a : X → X) μ μ) →
    ∀ A : Set X, MeasurableSet A → 0 < μ A →
      ∃ m n : ℕ+, n < m ∧
        0 < μ (⇑(T (2 * m * n)) '' A ∩
          ⇑(T ((m - n) * (m + n))) '' A)

/--
Resolved true: Resolved by Frantzikinakis-Klurman-Moreira, Partition Regularity of Pythagorean
Pairs (arXiv:2309.10636), Theorem 2.1(i): applied with coefficients 1 and 2 to the inverse
family, it yields the two forward-image indices of AMR-047-0034. The statement is retained as a
resolved target. Source: Frantzikinakis, Klurman, Moreira, Partition Regularity of Pythagorean
Pairs, arXiv:2309.10636, Theorem 2.1(i), https://arxiv.org/abs/2309.10636. Moved from
`OpenConjectures/Dynamics/MultStructureRecurrence`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Dynamics.MultStructureRecurrenceWanted
