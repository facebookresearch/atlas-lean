/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1048
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

open Filter Polynomial

namespace MathlibExt.Analysis.ErdosProblem1048Wanted

/-! Source record `FC-ErdosProblem1048`, ported from FormalConjectures
`ErdosProblems/1048.lean` (`theorem erdos_1048` and its six variants)
and checked against erdosproblems.com/1048. `levelSet` (cf. Erdos1043,
same repository) is inlined. Status: resolved false (Pommerenke [Po61]). The
historical positive large-diameter claim is preserved as `conjecture`
(disproved); its negation is the unregistered companion
`disprovedConjecture`. Pommerenke's counterexamples and positive bounds
are the established targets below. -/

/-- The sublevel set `{z : |f(z)| ≤ 1}` (cf. Erdos1043, inlined). -/
def levelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

/-- The strict sublevel set `{z : |f(z)| < 1}`. -/
def openLevelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < 1}

/-- The historical large-diameter component claim (disproved). -/
def conjecture : Prop :=
  ∀ (r : ℝ) (f : ℂ[X]), 0 < r → r < 2 → f.Monic → f.degree ≥ 1 →
    (∀ z ∈ f.roots, ‖z‖ ≤ r) →
    ∃ z ∈ openLevelSet f, ENNReal.ofReal (2 - r) <
      Metric.ediam (connectedComponentIn (openLevelSet f) z)

/-- Its disproof (companion). -/
def disprovedConjecture : Prop := ¬ conjecture

/-- `X ^ n - r ^ n` has `n` components (established). -/
def componentCount : Prop :=
  ∀ (r : ℝ) (_hr : 1 < r) (n : ℕ) (_hn : 1 ≤ n)
    (f : ℂ[X]) (_hf : f = (X : ℂ[X]) ^ n - C ((r : ℂ) ^ n)),
    {C : Set ℂ | ∃ z ∈ levelSet f, C = connectedComponentIn (levelSet f) z}.ncard = n

/-- Their diameters tend to `0` (established). -/
def smallDiameter : Prop :=
  ∀ (r : ℝ) (_hr : 1 < r) (ε : ℝ) (_hε : 0 < ε),
    ∀ᶠ n : ℕ in atTop, ∀ f : ℂ[X], f = (X : ℂ[X]) ^ n - C ((r : ℂ) ^ n) →
      ∀ z ∈ levelSet f,
        Metric.ediam (connectedComponentIn (levelSet f) z) < ENNReal.ofReal ε

/-- The positive `2 - r` bound for `r ≤ 1` (established). -/
def positiveLeOne : Prop :=
  ∀ (r : ℝ) (_hr₀ : 0 < r) (_hr₁ : r ≤ 1) (f : ℂ[X])
    (_hmonic : f.Monic) (_hdeg : f.degree ≥ 1) (_hroots : ∀ z ∈ f.roots, ‖z‖ ≤ r),
    ∃ z ∈ openLevelSet f, ENNReal.ofReal (2 - r) <
      Metric.ediam (connectedComponentIn (openLevelSet f) z)

/-- The diameter-`2` bound at `0` for `r ≤ 1 / 2` (established). -/
def positiveLeHalf : Prop :=
  ∀ (r : ℝ) (_hr₀ : 0 ≤ r) (_hr₁ : r ≤ 1 / 2) (f : ℂ[X])
    (_hmonic : f.Monic) (_hdeg : f.degree ≥ 1) (_hroots : ∀ z ∈ f.roots, ‖z‖ ≤ r),
    2 ≤ Metric.ediam (connectedComponentIn (levelSet f) 0)

/-- `X ^ n` shows the diameter-`2` bound is best possible (established). -/
def monomialDiameter : Prop :=
  ∀ (n : ℕ) (_hn : 1 ≤ n),
    Metric.ediam (connectedComponentIn (levelSet ((X : ℂ[X]) ^ n)) 0) = 2

/-- The `1 / r` bound in the middle range (established). -/
def positiveMidLower : Prop :=
  ∀ (r : ℝ) (_hr₀ : 1 / 2 < r)
    (_hr₁ : r ≤ (Real.sqrt 5 - 1) / 2) (f : ℂ[X]) (_hmonic : f.Monic)
    (_hdeg : f.degree ≥ 1) (_hroots : ∀ z ∈ f.roots, ‖z‖ ≤ r),
    ENNReal.ofReal (1 / r) < Metric.ediam (connectedComponentIn (levelSet f) 0)

/-- The `2 - r ^ 2` bound in the upper range (established). -/
def positiveMidUpper : Prop :=
  ∀ (r : ℝ) (_hr₀ : (Real.sqrt 5 - 1) / 2 ≤ r)
    (_hr₁ : r ≤ 1) (f : ℂ[X]) (_hmonic : f.Monic) (_hdeg : f.degree ≥ 1)
    (_hroots : ∀ z ∈ f.roots, ‖z‖ ≤ r),
    ENNReal.ofReal (2 - r ^ 2) < Metric.ediam (connectedComponentIn (levelSet f) 0)

/--
Resolved false: Answered negatively per erdosproblems.com/1048 (DISPROVED (LEAN)): Pommerenke
[Po61] proved the answer is no for r > 1 (for f(z) = z^n - r^n, {z : |f(z)| ≤ 1} has n
components, all of diameter tending to 0) and yes for 0 < r ≤ 1, with lower bounds 2, 1/r and 2
− r^2 on the diameter of the component containing 0 for r ≤ 1/2, 1/2 < r ≤ (√5 − 1)/2 and (√5 −
1)/2 ≤ r ≤ 1. The registered conjecture is refuted; the seven companion targets hold. This
target is refuted: For r > 1, Pommerenke's z^n - r^n ([Po61], recorded on
erdosproblems.com/1048): every component of {|f| ≤ 1}, hence of {|f| < 1}, has diameter tending
to 0, below 2 - r for large n; formal-conjectures erdos_1048 states this negation (category
research solved), proved in Lean in plby/lean-proofs (ErdosProblems/Erdos1048.lean). Source:
Pommerenke [Po61], per erdosproblems.com/1048, https://www.erdosproblems.com/1048. Moved from
`OpenConjectures/Analysis/ErdosProblem1048`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

/--
Resolved false: Answered negatively per erdosproblems.com/1048 (DISPROVED (LEAN)): Pommerenke
[Po61] proved the answer is no for r > 1 (for f(z) = z^n - r^n, {z : |f(z)| ≤ 1} has n
components, all of diameter tending to 0) and yes for 0 < r ≤ 1, with lower bounds 2, 1/r and 2
− r^2 on the diameter of the component containing 0 for r ≤ 1/2, 1/2 < r ≤ (√5 − 1)/2 and (√5 −
1)/2 ≤ r ≤ 1. The registered conjecture is refuted; the seven companion targets hold. This
target holds: Pommerenke ([Po61], recorded on erdosproblems.com/1048): for r > 1, {z : |z^n -
r^n| ≤ 1} has n connected components; formal-conjectures
erdos_1048.variants.pommerenke_ncard_components (category research solved). Source: Pommerenke
[Po61], per erdosproblems.com/1048, https://www.erdosproblems.com/1048. Moved from
`OpenConjectures/Analysis/ErdosProblem1048`.
-/
public theorem_wanted componentCount_holds : componentCount

/--
Resolved false: Answered negatively per erdosproblems.com/1048 (DISPROVED (LEAN)): Pommerenke
[Po61] proved the answer is no for r > 1 (for f(z) = z^n - r^n, {z : |f(z)| ≤ 1} has n
components, all of diameter tending to 0) and yes for 0 < r ≤ 1, with lower bounds 2, 1/r and 2
− r^2 on the diameter of the component containing 0 for r ≤ 1/2, 1/2 < r ≤ (√5 − 1)/2 and (√5 −
1)/2 ≤ r ≤ 1. The registered conjecture is refuted; the seven companion targets hold. This
target holds: Pommerenke ([Po61], recorded on erdosproblems.com/1048): for r > 1 the n
components of {z : |z^n - r^n| ≤ 1} all have diameter tending to 0 as n → ∞; formal-conjectures
erdos_1048.variants.pommerenke_diam_tendsto_zero (category research solved). Source: Pommerenke
[Po61], per erdosproblems.com/1048, https://www.erdosproblems.com/1048. Moved from
`OpenConjectures/Analysis/ErdosProblem1048`.
-/
public theorem_wanted smallDiameter_holds : smallDiameter

/--
Resolved false: Answered negatively per erdosproblems.com/1048 (DISPROVED (LEAN)): Pommerenke
[Po61] proved the answer is no for r > 1 (for f(z) = z^n - r^n, {z : |f(z)| ≤ 1} has n
components, all of diameter tending to 0) and yes for 0 < r ≤ 1, with lower bounds 2, 1/r and 2
− r^2 on the diameter of the component containing 0 for r ≤ 1/2, 1/2 < r ≤ (√5 − 1)/2 and (√5 −
1)/2 ≤ r ≤ 1. The registered conjecture is refuted; the seven companion targets hold. This
target holds: erdosproblems.com/1048: 'if 0<r≤1, then the answer is yes, as also shown by
Pommerenke [Po61]', i.e. some component of {|f| < 1} has diameter > 2 - r; formal-conjectures
erdos_1048.variants.r_le_one (category research solved). Source: Pommerenke [Po61], per
erdosproblems.com/1048, https://www.erdosproblems.com/1048. Moved from
`OpenConjectures/Analysis/ErdosProblem1048`.
-/
public theorem_wanted positiveLeOne_holds : positiveLeOne

/--
Resolved false: Answered negatively per erdosproblems.com/1048 (DISPROVED (LEAN)): Pommerenke
[Po61] proved the answer is no for r > 1 (for f(z) = z^n - r^n, {z : |f(z)| ≤ 1} has n
components, all of diameter tending to 0) and yes for 0 < r ≤ 1, with lower bounds 2, 1/r and 2
− r^2 on the diameter of the component containing 0 for r ≤ 1/2, 1/2 < r ≤ (√5 − 1)/2 and (√5 −
1)/2 ≤ r ≤ 1. The registered conjecture is refuted; the seven companion targets hold. This
target holds: Pommerenke ([Po61], recorded on erdosproblems.com/1048): if 0 ≤ r ≤ 1/2 the
component containing 0 has diameter ≥ 2; formal-conjectures erdos_1048.variants.diam_ge_two
(category research solved). Source: Pommerenke [Po61], per erdosproblems.com/1048,
https://www.erdosproblems.com/1048. Moved from `OpenConjectures/Analysis/ErdosProblem1048`.
-/
public theorem_wanted positiveLeHalf_holds : positiveLeHalf

/--
Resolved false: Answered negatively per erdosproblems.com/1048 (DISPROVED (LEAN)): Pommerenke
[Po61] proved the answer is no for r > 1 (for f(z) = z^n - r^n, {z : |f(z)| ≤ 1} has n
components, all of diameter tending to 0) and yes for 0 < r ≤ 1, with lower bounds 2, 1/r and 2
− r^2 on the diameter of the component containing 0 for r ≤ 1/2, 1/2 < r ≤ (√5 − 1)/2 and (√5 −
1)/2 ≤ r ≤ 1. The registered conjecture is refuted; the seven companion targets hold. This
target holds: erdosproblems.com/1048: the bound 2 is best possible, as f(z) = z^n shows; for z^n
the component of {|f| ≤ 1} containing 0 is the closed unit disc, of diameter 2;
formal-conjectures erdos_1048.variants.diam_ge_two_is_best (category research solved). Source:
Pommerenke [Po61], per erdosproblems.com/1048, https://www.erdosproblems.com/1048. Moved from
`OpenConjectures/Analysis/ErdosProblem1048`.
-/
public theorem_wanted monomialDiameter_holds : monomialDiameter

/--
Resolved false: Answered negatively per erdosproblems.com/1048 (DISPROVED (LEAN)): Pommerenke
[Po61] proved the answer is no for r > 1 (for f(z) = z^n - r^n, {z : |f(z)| ≤ 1} has n
components, all of diameter tending to 0) and yes for 0 < r ≤ 1, with lower bounds 2, 1/r and 2
− r^2 on the diameter of the component containing 0 for r ≤ 1/2, 1/2 < r ≤ (√5 − 1)/2 and (√5 −
1)/2 ≤ r ≤ 1. The registered conjecture is refuted; the seven companion targets hold. This
target holds: Pommerenke ([Po61], recorded on erdosproblems.com/1048): if 1/2 < r ≤ (√5-1)/2 the
component containing 0 has diameter > 1/r; formal-conjectures erdos_1048.variants.diam_gt_inv_r
(category research solved). Source: Pommerenke [Po61], per erdosproblems.com/1048,
https://www.erdosproblems.com/1048. Moved from `OpenConjectures/Analysis/ErdosProblem1048`.
-/
public theorem_wanted positiveMidLower_holds : positiveMidLower

/--
Resolved false: Answered negatively per erdosproblems.com/1048 (DISPROVED (LEAN)): Pommerenke
[Po61] proved the answer is no for r > 1 (for f(z) = z^n - r^n, {z : |f(z)| ≤ 1} has n
components, all of diameter tending to 0) and yes for 0 < r ≤ 1, with lower bounds 2, 1/r and 2
− r^2 on the diameter of the component containing 0 for r ≤ 1/2, 1/2 < r ≤ (√5 − 1)/2 and (√5 −
1)/2 ≤ r ≤ 1. The registered conjecture is refuted; the seven companion targets hold. This
target holds: Pommerenke ([Po61], recorded on erdosproblems.com/1048): if (√5-1)/2 ≤ r ≤ 1 the
component containing 0 has diameter > 2 - r^2; formal-conjectures
erdos_1048.variants.diam_gt_two_sub_sq (category research solved). Source: Pommerenke [Po61],
per erdosproblems.com/1048, https://www.erdosproblems.com/1048. Moved from
`OpenConjectures/Analysis/ErdosProblem1048`.
-/
public theorem_wanted positiveMidUpper_holds : positiveMidUpper

end MathlibExt.Analysis.ErdosProblem1048Wanted
