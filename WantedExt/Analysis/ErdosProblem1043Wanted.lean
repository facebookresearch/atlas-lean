/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1043
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Batteries.Util.ProofWanted

@[expose] public section

open MeasureTheory Polynomial
open scoped ENNReal

namespace MathlibExt.Analysis.ErdosProblem1043Wanted

/-! Source record `FC-ErdosProblem1043`, ported from FormalConjectures
`ErdosProblems/1043.lean` (`theorem erdos_1043` and its weak variant)
and checked against erdosproblems.com/1043. Status: resolved false (Pommerenke
[Po61]). The historical positive length-2 claim is preserved as
`conjecture` (disproved); its negation is the unregistered companion
`disprovedConjecture`. The 3.3 bound is the established companion target
`weakVariant`. -/

/-- The sublevel set `{z : |f(z)| ≤ 1}`. -/
def levelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

/-- One-dimensional Hausdorff length of the orthogonal projection of the
sublevel set onto the real line spanned by `u`. -/
noncomputable def projectionLength (f : Polynomial ℂ) (u : ℂ) : ℝ≥0∞ :=
  MeasureTheory.Measure.hausdorffMeasure 1
    ((ℝ ∙ u).orthogonalProjectionOnto '' levelSet f)

/-- The historical uniform length-2 projection claim (disproved). -/
def conjecture : Prop :=
  ∀ (f : ℂ[X]), f.Monic → f.degree ≥ 1 →
    ∃ (u : ℂ), ‖u‖ = 1 ∧
    projectionLength f u ≤ 2

/-- Its disproof (companion). -/
def disprovedConjecture : Prop := ¬ conjecture

/-- The 3.3 projection bound (established). -/
def weakVariant : Prop :=
  ∀ (f : ℂ[X]), f.Monic → f.degree ≥ 1 →
    ∃ (u : ℂ), ‖u‖ = 1 ∧
    projectionLength f u ≤ 3.3

/--
Resolved false: Answered negatively per erdosproblems.com/1043 (DISPROVED (LEAN)): Pommerenke
[Po61] proved that some monic f has every line projection of {z : |f(z)| ≤ 1} of measure at
least 2.386, and that for every monic f some line projection has measure at most 3.3. The
registered conjecture is refuted; the companion target weakVariant (the 3.3 bound) holds. This
target is refuted: Pommerenke's polynomial ([Po61], recorded on erdosproblems.com/1043) has
every line projection of {z : |f(z)| ≤ 1} of measure at least 2.386 > 2; formal-conjectures
erdos_1043 states this negation (category research solved), proved in Lean in plby/lean-proofs
(ErdosProblems/Erdos1043.lean). Source: Pommerenke [Po61], per erdosproblems.com/1043,
https://www.erdosproblems.com/1043. Moved from `OpenConjectures/Analysis/ErdosProblem1043`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

/--
Resolved false: Answered negatively per erdosproblems.com/1043 (DISPROVED (LEAN)): Pommerenke
[Po61] proved that some monic f has every line projection of {z : |f(z)| ≤ 1} of measure at
least 2.386, and that for every monic f some line projection has measure at most 3.3. The
registered conjecture is refuted; the companion target weakVariant (the 3.3 bound) holds. This
target holds: Pommerenke's 3.3 bound ([Po61], recorded on erdosproblems.com/1043): for every
monic non-constant f some line projection of {z : |f(z)| ≤ 1} has measure at most 3.3;
formal-conjectures erdos_1043.variants.weak (category research solved). Source: Pommerenke
[Po61], per erdosproblems.com/1043, https://www.erdosproblems.com/1043. Moved from
`OpenConjectures/Analysis/ErdosProblem1043`.
-/
public theorem_wanted weakVariant_holds : weakVariant

end MathlibExt.Analysis.ErdosProblem1043Wanted
