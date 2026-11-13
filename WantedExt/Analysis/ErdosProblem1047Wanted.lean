/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1047
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Connected.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

open Filter Polynomial

namespace MathlibExt.Analysis.ErdosProblem1047Wanted

/-! Source record `FC-ErdosProblem1047`, ported from FormalConjectures
`ErdosProblems/1047.lean` (`def sublevelSet`, `def strictSublevelSet`,
`def componentsIn`, `theorem erdos_1047`, `pommerenke`, `goodman`,
`goodman_simple_roots`, `referee`) and checked against
erdosproblems.com/1047. The vacuous `max_non_convex_components` claim
(unknown function as a term) is skipped. Status: resolved false (Pommerenke,
Goodman). The historical positive convexity claim is preserved as
`conjecture` (disproved); its negation is the unregistered companion
`disprovedConjecture`. The four counterexamples are the established
targets `pommerenke`, `goodman`, `goodmanSimpleRoots`, and `referee`. -/

/-- The sublevel set `{ z: |f(z)| ≤ c }` of a polynomial `f ∈ ℂ[x]`. -/
def sublevelSet (f : ℂ[X]) (c : ℝ) : Set ℂ := {z : ℂ | ‖f.eval z‖ ≤ c}

/-- The strict sublevel set `{ z: |f(z)| < c }` of a polynomial `f ∈ ℂ[x]`. -/
def strictSublevelSet (f : ℂ[X]) (c : ℝ) : Set ℂ := {z : ℂ | ‖f.eval z‖ < c}

/-- The connected components of a set `s ⊆ ℂ`, viewed as subsets of `ℂ`. -/
def componentsIn (s : Set ℂ) : Set (Set ℂ) :=
  {t : Set ℂ | ∃ z ∈ s, t = connectedComponentIn s z}

/-- The historical claim that maximal-component sublevel sets are convex
(disproved). -/
def conjecture : Prop :=
  ∀ (f : ℂ[X]) (m : ℕ) (c : ℝ), f.Monic → (f.rootSet ℂ).ncard = m →
    0 < c → (componentsIn (sublevelSet f c)).ncard = m →
      ∀ t ∈ componentsIn (sublevelSet f c), Convex ℝ t

/-- Its disproof (companion). -/
def disprovedConjecture : Prop := ¬ conjecture

/-- Pommerenke's asymptotic non-convex family (established). -/
def pommerenke : Prop :=
  ∀ᶠ k : ℕ in Filter.atTop, ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ,
    (1 + 1 / (k : ℝ)) * (k : ℝ) ^ ((1 : ℝ) / ((k : ℝ) + 1)) < a →
      a < (1 + 1 / (k : ℝ)) * (k : ℝ) ^ ((1 : ℝ) / ((k : ℝ) + 1)) + δ →
        (componentsIn (sublevelSet (X ^ k * (X - C (a : ℂ))) 1)).ncard = 2 ∧
        ¬ Convex ℝ
          (connectedComponentIn (sublevelSet (X ^ k * (X - C (a : ℂ))) 1) 0)

/-- Goodman's explicit non-convex example (established). -/
def goodman : Prop :=
  (componentsIn (strictSublevelSet ((X ^ 2 + 1) * (X - C 2) ^ 2)
      ((5 : ℝ) ^ ((3 : ℝ) / 2) / 4))).ncard = 3 ∧
    ∃ t ∈ componentsIn (strictSublevelSet ((X ^ 2 + 1) * (X - C 2) ^ 2)
      ((5 : ℝ) ^ ((3 : ℝ) / 2) / 4)), ¬ Convex ℝ t

/-- Goodman's non-convex example with simple roots (established). -/
def goodmanSimpleRoots : Prop :=
  ∃ (f : ℂ[X]) (c : ℝ), f.Monic ∧ f.natDegree = 4 ∧
    (f.rootSet ℂ).ncard = 4 ∧ 0 < c ∧
    (componentsIn (sublevelSet f c)).ncard = 4 ∧
    ∃ t ∈ componentsIn (sublevelSet f c), ¬ Convex ℝ t

/-- The referee's non-convex example (established). -/
def referee : Prop :=
  (componentsIn (strictSublevelSet (X * (X ^ 5 - 1))
      (5 * (6 : ℝ) ^ (-(6 : ℝ) / 5)))).ncard = 6 ∧
    ∃ t ∈ componentsIn (strictSublevelSet (X * (X ^ 5 - 1))
      (5 * (6 : ℝ) ^ (-(6 : ℝ) / 5))), ¬ Convex ℝ t

/--
Resolved false: Answered negatively per erdosproblems.com/1047 (DISPROVED (LEAN)): Pommerenke
[Po61] showed that for large k and a sufficiently close to (1 + 1/k) k^(1/(k+1)), {z : |z^k (z -
a)| ≤ 1} has two components and the one containing 0 is not convex; Goodman [Go66] and the
referee of [Go66] gave further non-convex examples. The registered conjecture is refuted; the
companion targets pommerenke, goodman, goodmanSimpleRoots and referee hold. This target is
refuted: Pommerenke's family ([Po61], recorded on erdosproblems.com/1047): z^k(z-a) is monic
with two distinct roots, and for c = 1 its sublevel set has two components, the one containing 0
not convex; formal-conjectures erdos_1047 states this negation (category research solved),
proved in Lean in plby/lean-proofs (ErdosProblems/Erdos1047.lean). Source: Pommerenke [Po61],
per erdosproblems.com/1047, https://www.erdosproblems.com/1047; Goodman [Go66], per
erdosproblems.com/1047, https://www.erdosproblems.com/1047. Moved from
`OpenConjectures/Analysis/ErdosProblem1047`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

/--
Resolved false: Answered negatively per erdosproblems.com/1047 (DISPROVED (LEAN)): Pommerenke
[Po61] showed that for large k and a sufficiently close to (1 + 1/k) k^(1/(k+1)), {z : |z^k (z -
a)| ≤ 1} has two components and the one containing 0 is not convex; Goodman [Go66] and the
referee of [Go66] gave further non-convex examples. The registered conjecture is refuted; the
companion targets pommerenke, goodman, goodmanSimpleRoots and referee hold. This target holds:
Pommerenke's theorem as recorded on erdosproblems.com/1047; the two-component case is a slightly
above (1+1/k)k^{1/(k+1)}, the value of a at which the critical value of z^k(z-a) has modulus 1,
which is how formal-conjectures erdos_1047.variants.pommerenke (category research solved) states
it. Source: Pommerenke [Po61], per erdosproblems.com/1047, https://www.erdosproblems.com/1047;
Goodman [Go66], per erdosproblems.com/1047, https://www.erdosproblems.com/1047. Moved from
`OpenConjectures/Analysis/ErdosProblem1047`.
-/
public theorem_wanted pommerenke_holds : pommerenke

/--
Resolved false: Answered negatively per erdosproblems.com/1047 (DISPROVED (LEAN)): Pommerenke
[Po61] showed that for large k and a sufficiently close to (1 + 1/k) k^(1/(k+1)), {z : |z^k (z -
a)| ≤ 1} has two components and the one containing 0 is not convex; Goodman [Go66] and the
referee of [Go66] gave further non-convex examples. The registered conjecture is refuted; the
companion targets pommerenke, goodman, goodmanSimpleRoots and referee hold. This target holds:
Goodman's example ([Go66], recorded on erdosproblems.com/1047): one of the three components of
{z : |(z^2+1)(z-2)^2| < 5^{3/2}/4} is not convex; formal-conjectures erdos_1047.variants.goodman
(category research solved). Source: Pommerenke [Po61], per erdosproblems.com/1047,
https://www.erdosproblems.com/1047; Goodman [Go66], per erdosproblems.com/1047,
https://www.erdosproblems.com/1047. Moved from `OpenConjectures/Analysis/ErdosProblem1047`.
-/
public theorem_wanted goodman_holds : goodman

/--
Resolved false: Answered negatively per erdosproblems.com/1047 (DISPROVED (LEAN)): Pommerenke
[Po61] showed that for large k and a sufficiently close to (1 + 1/k) k^(1/(k+1)), {z : |z^k (z -
a)| ≤ 1} has two components and the one containing 0 is not convex; Goodman [Go66] and the
referee of [Go66] gave further non-convex examples. The registered conjecture is refuted; the
companion targets pommerenke, goodman, goodmanSimpleRoots and referee hold. This target holds:
Goodman ([Go66], recorded on erdosproblems.com/1047) constructed a non-convex example with
simple roots, of degree 4, in the setting of the problem (one component per root);
formal-conjectures erdos_1047.variants.goodman_simple_roots (category research solved). Source:
Pommerenke [Po61], per erdosproblems.com/1047, https://www.erdosproblems.com/1047; Goodman
[Go66], per erdosproblems.com/1047, https://www.erdosproblems.com/1047. Moved from
`OpenConjectures/Analysis/ErdosProblem1047`.
-/
public theorem_wanted goodmanSimpleRoots_holds : goodmanSimpleRoots

/--
Resolved false: Answered negatively per erdosproblems.com/1047 (DISPROVED (LEAN)): Pommerenke
[Po61] showed that for large k and a sufficiently close to (1 + 1/k) k^(1/(k+1)), {z : |z^k (z -
a)| ≤ 1} has two components and the one containing 0 is not convex; Goodman [Go66] and the
referee of [Go66] gave further non-convex examples. The registered conjecture is refuted; the
companion targets pommerenke, goodman, goodmanSimpleRoots and referee hold. This target holds:
The referee's example in [Go66] (recorded on erdosproblems.com/1047): {z : |z(z^5-1)| <
5·6^{-6/5}} has a non-convex component; 5·6^{-6/5} is the common critical value of z^6 - z, so
the set has one component for each of the six roots; formal-conjectures
erdos_1047.variants.referee (category research solved). Source: Pommerenke [Po61], per
erdosproblems.com/1047, https://www.erdosproblems.com/1047; Goodman [Go66], per
erdosproblems.com/1047, https://www.erdosproblems.com/1047. Moved from
`OpenConjectures/Analysis/ErdosProblem1047`.
-/
public theorem_wanted referee_holds : referee

end MathlibExt.Analysis.ErdosProblem1047Wanted
