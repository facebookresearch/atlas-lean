/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1038
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Interval.Set.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

open MeasureTheory ENNReal

namespace MathlibExt.Analysis.ErdosProblem1038Wanted

/-! Source record `FC-ErdosProblem1038`, ported from FormalConjectures
`ErdosProblems/1038.lean` (`theorem erdos_1038.parts.ii`,
`inf_upperBound`, `inf_lowerBound`) and checked against
erdosproblems.com/1038. A problem of Erdős, Herzog, and Piranian
[EHP58]: determine the infimum and supremum sublevel volume over
non-constant monic real-rooted polynomials with all roots in `[-1, 1]`.
Status: resolved true as formalized (every registered target is
established; the exact infimum is unknown). The source bounds are infima
(⨅): the supremum form is false (e.g. `f = X` is admissible with
sublevel volume `2`, contradicting `< 1.835`). The supremum value and
both infimum bounds are established targets; the exact infimum is
unknown and no value is conjectured, so it is recorded in gaps rather
than as a target. -/

open Classical in
/-- The infimum sublevel-set volume over non-constant admissible
polynomials (`f ≠ 1` excludes the trivial empty-sublevel case). -/
noncomputable def infVolume : ℝ≥0∞ :=
  ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1}

open Classical in
/-- Supremum value `2√2` (established companion; Tao). -/
def supremumValue : Prop :=
  2 * 2 ^ (1 / 2 : ℝ) =
    ⨆ f : {f : Polynomial ℝ // f.Monic ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1}

/-- Infimum upper bound (established companion). -/
def infimumUpperBound : Prop := infVolume < 1.835

/-- Infimum lower bound (established companion). -/
def infimumLowerBound : Prop := 2 ^ (4 / 3 : ℝ) - 1 ≤ infVolume

/--
Resolved true: Every formalized target is established, per erdosproblems.com/1038 (checked
2026-10-22): the supremum is 2√2 (supremumValue; Erdős, Herzog and Piranian [EHP58] proved the
bound when all roots are ±1, and the page records sup = 2√2 from its forum discussion), and
2^{4/3} - 1 ≤ inf < 1.835 (infimumLowerBound, infimumUpperBound). The exact infimum, which the
source also asks for, is open and has no formal target (see gaps). This target holds: The page
records sup = 2 sqrt 2 for the sublevel measure over monic real-rooted polynomials with roots in
[-1, 1], which is supremumValue. Source: Terence Tao (sup = 2√2), per erdosproblems.com/1038,
https://www.erdosproblems.com/1038; Erdős Problems commenters (best-known infimum bounds
2^{4/3}-1 ≤ inf ≤ 1.835⋯), per erdosproblems.com/1038, https://www.erdosproblems.com/1038. Moved
from `OpenConjectures/Analysis/ErdosProblem1038`.
-/
public theorem_wanted supremumValue_holds : supremumValue

/--
Resolved true: Every formalized target is established, per erdosproblems.com/1038 (checked
2026-10-22): the supremum is 2√2 (supremumValue; Erdős, Herzog and Piranian [EHP58] proved the
bound when all roots are ±1, and the page records sup = 2√2 from its forum discussion), and
2^{4/3} - 1 ≤ inf < 1.835 (infimumLowerBound, infimumUpperBound). The exact infimum, which the
source also asks for, is open and has no formal target (see gaps). This target holds: The page
records inf <= 1.835... (an explicit measure with sublevel length between 1.8344 and 1.8345 in
the forum), so the infimum over non-constant admissible polynomials is below 1.835. Source:
Terence Tao (sup = 2√2), per erdosproblems.com/1038, https://www.erdosproblems.com/1038; Erdős
Problems commenters (best-known infimum bounds 2^{4/3}-1 ≤ inf ≤ 1.835⋯), per
erdosproblems.com/1038, https://www.erdosproblems.com/1038. Moved from
`OpenConjectures/Analysis/ErdosProblem1038`.
-/
public theorem_wanted infimumUpperBound_holds : infimumUpperBound

/--
Resolved true: Every formalized target is established, per erdosproblems.com/1038 (checked
2026-10-22): the supremum is 2√2 (supremumValue; Erdős, Herzog and Piranian [EHP58] proved the
bound when all roots are ±1, and the page records sup = 2√2 from its forum discussion), and
2^{4/3} - 1 ≤ inf < 1.835 (infimumLowerBound, infimumUpperBound). The exact infimum, which the
source also asks for, is open and has no formal target (see gaps). This target holds: The page
records 2^(4/3) - 1 <= inf as the current best lower bound, which is infimumLowerBound. Source:
Terence Tao (sup = 2√2), per erdosproblems.com/1038, https://www.erdosproblems.com/1038; Erdős
Problems commenters (best-known infimum bounds 2^{4/3}-1 ≤ inf ≤ 1.835⋯), per
erdosproblems.com/1038, https://www.erdosproblems.com/1038. Moved from
`OpenConjectures/Analysis/ErdosProblem1038`.
-/
public theorem_wanted infimumLowerBound_holds : infimumLowerBound

end MathlibExt.Analysis.ErdosProblem1038Wanted
