/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook144Wanted

/-- Mazur and Ulam's Problem 144 from the Scottish Book, as printed: in a
separable Banach space, is there an injective map from the unit sphere
`K` into the interval `[0, 1]` under which the image of every nonempty
open subset of `K` has positive measure? -/
def ScottishBookProblem144Claim : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E],
    ∃ f : ↥(Metric.sphere (0 : E) 1) → ℝ,
      Function.Injective f ∧ (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (U : Set ↥(Metric.sphere (0 : E) 1)), IsOpen U → U.Nonempty →
        0 < MeasureTheory.volume (f '' U)

/--
Mazur–Ulam Problem 144 is false as stated: take `E = ℝ`. Its unit sphere
is `{-1, 1}`, so the singleton `U = {1}` is a nonempty open subset of the
sphere, but for every `f` its image `f '' U` is a singleton, hence of
Lebesgue measure zero, contradicting `0 < volume (f '' U)`. The source
contains no dimension restriction (it says "infinite-dimensional"
explicitly when it means it, e.g. Problem 7), so no
`¬ Module.Finite ℝ E` restriction is added here. Status: solved-negative.
Source: S. Mazur and S. Ulam, Problem 144 of the Scottish Book,
typescript p. 63 (printed), PDF p. 66; see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted mazurUlam144_refuted : ¬ ScottishBookProblem144Claim

end MathlibExt.Analysis.ScottishBook144Wanted
