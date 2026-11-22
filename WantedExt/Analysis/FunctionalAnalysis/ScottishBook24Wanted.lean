/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook24Wanted

/--
In a Banach space `E`, let `F` be an additive functional with the following
property: whenever `x` is a continuous function on `[0, 1]` with values in
`E`, the function `t ↦ F (x t)` is (Borel) measurable. Is `F` continuous?
Source: S. Mazur, Problem 24 of the Scottish Book (prize: two small beers).
Solved affirmatively by I. Labuda and R. D. Mauldin, "Problem 24 of the
Scottish Book concerning additive functionals", Colloquium Mathematicum 48,
as quoted in Ger (2016); the proof covers additive operators into a
Hausdorff topological vector space.
-/
theorem_wanted additiveFunctionalMeasurableOnCurvesContinuous :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (F : E → ℝ), (∀ x y, F (x + y) = F x + F y) →
      (∀ (x : C(↥(Set.Icc (0 : ℝ) 1), E)), Measurable fun t => F (x t)) →
      Continuous F

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook24Wanted
