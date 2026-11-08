/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Tactic.Measurability
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

namespace MathlibExt.MeasureTheory.ScottishBook169Wanted

/-- Two plane sets are congruent when an isometry of the plane carries
one onto the other. -/
def AreCongruent (E F : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ T : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2), T '' E = F

/-- `μ` is equal on congruent sets. -/
def IsCongruenceInvariant (μ : Set (EuclideanSpace ℝ (Fin 2)) → ENNReal) : Prop :=
  ∀ E F : Set (EuclideanSpace ℝ (Fin 2)), AreCongruent E F → μ E = μ F

/-- `μ` is countably additive on pairwise-disjoint families. This is the
countably-additive reading of "additive" in Problem 169; the typescript
does not say whether finite or countable additivity is meant. -/
def IsCountablyAdditive (μ : Set (EuclideanSpace ℝ (Fin 2)) → ENNReal) : Prop :=
  ∀ E : ℕ → Set (EuclideanSpace ℝ (Fin 2)),
    Pairwise fun i j => Disjoint (E i) (E j) → μ (⋃ i, E i) = ∑' i, μ (E i)

/-- The countably additive reading of Problem 169: there is a function
`μ`, defined for all plane sets, equal on congruent sets, countably
additive, extending the Caratheodory linear measure (read as Lebesgue
volume on measurable sets), with values in `[0, +∞]` (automatic for
`ENNReal`). -/
def CountablyAdditiveCongruenceClaim : Prop :=
  ∃ μ : Set (EuclideanSpace ℝ (Fin 2)) → ENNReal,
    IsCongruenceInvariant μ ∧ IsCountablyAdditive μ ∧
    ∀ E : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet E →
      μ E = MeasureTheory.volume E

/--
The countably additive reading is false in ZFC. Sketch: let
`V₀ ⊆ [0,1]` meet each `ℚ`-coset of `ℝ` exactly once (Vitali selector)
and put `V = V₀ × [0,1]`. Enumerating `ℚ ∩ [-1,1]` as `(qₙ)`, the
translates `Tₙ = V + (qₙ, 0)` are pairwise disjoint, each congruent to
`V`, so all have the same mass `c = μ V`. Their union contains the unit
square `Q = [0,1] × [0,1]` and lies in the strip `[-1,2] × [0,1]` of
volume 3, so countable additivity and monotonicity give
`1 = μ Q ≤ μ U ≤ 3`, while countable additivity also gives
`μ U = ∑'ₙ c`, which is `0` if `c = 0` and `+∞` if `c > 0`, a
contradiction. Hence no such `μ` exists. This refutes the countably
additive formalization only. The typescript says bare "additive"; the
finite-additivity reading is Banach's 1923 theorem (a Banach measure: a
finitely additive, isometry-invariant function on all plane sets
extending Lebesgue measure), not this claim, and is not asserted here.
Source: E. Szpilrajn, Problem 169 of the Scottish Book; typescript
PDF p.78, printed p.75. Banach, Fund. Math. 4 (1923), 7-33.
-/
theorem_wanted no_countably_additive_congruence_measure :
  ¬ CountablyAdditiveCongruenceClaim

end MathlibExt.MeasureTheory.ScottishBook169Wanted
