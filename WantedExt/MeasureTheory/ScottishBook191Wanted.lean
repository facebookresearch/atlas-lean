/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace MathlibExt.MeasureTheory.ScottishBook191Wanted

/-- A measure `μ` is convex (in Fréchet's sense, "sans singularités") if
`μ X = 1` and every set of positive measure contains a subset of strictly
smaller positive measure. -/
def IsConvexMeasure {X : Type} [MeasurableSpace X] (μ : MeasureTheory.Measure X) :
    Prop :=
  μ Set.univ = 1 ∧ ∀ A : Set X, MeasurableSet A → 0 < μ A →
    ∃ B : Set X, B ⊆ A ∧ MeasurableSet B ∧ μ A > μ B ∧ 0 < μ B

/-- A class `B` of sets is stochastically independent with respect to `μ`
if every finite collection of distinct sets in `B` satisfies the product
formula for the measure of their intersection. -/
def IsIndependentClass {X : Type} [MeasurableSpace X] (B : Set (Set X))
    (μ : MeasureTheory.Measure X) : Prop :=
  ∀ s : Finset (Set X), (↑s : Set (Set X)) ⊆ B →
    μ (⋂₀ (↑s : Set (Set X))) = ∏ A ∈ s, μ A

/-- A class `B` is a base of `μ` if it is a stochastically independent
class of measurable sets, and every measurable set agrees, up to a set
of measure zero, with a set in the smallest countably additive class of
sets containing `B`. -/
def IsBase {X : Type} [MeasurableSpace X] (B : Set (Set X))
    (μ : MeasureTheory.Measure X) : Prop :=
  (∀ A ∈ B, MeasurableSet A) ∧ IsIndependentClass B μ ∧
    ∀ A : Set X, MeasurableSet A → ∃ C : Set X,
      @MeasurableSet X (MeasurableSpace.generateFrom B) C ∧
        μ (A \ C ∪ C \ A) = 0

/-- Szpilrajn's Problem 191 from the Scottish Book, in its original form:
does every convex measure possess a base? -/
def ScottishBookProblem191Claim : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X),
    IsConvexMeasure μ → ∃ B : Set (Set X), IsBase B μ

/--
Szpilrajn's Problem 191 is false: not every convex measure possesses a
base. A non-atomic (convex) measure has a base if and only if its
measure algebra is homogeneous, and the direct sum of Lebesgue measure
spaces gives a counterexample whose measure algebra is not homogeneous.
Source: E. Szpilrajn, Problem 191 of the Scottish Book; the sets `B n`
of numbers in `[0, 1]` whose `n`-th binary digit is `1` form a base for
Lebesgue measure on `[0, 1]`. See the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted szpilrajn191_refuted : ¬ ScottishBookProblem191Claim

end MathlibExt.MeasureTheory.ScottishBook191Wanted
