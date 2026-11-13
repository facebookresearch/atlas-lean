/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Connected lemniscates lie in a disc of radius two (Erdős Problem 1046)

Erdős Problem 1046 (Erdős, Herzog and Piranian): let `f ∈ ℂ[x]` be monic and `E = {z : |f(z)| < 1}`.
If `E` is connected, is `E` contained in a disc of radius `2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace MathlibExt.Analysis.ConnectedLemniscateRadiusTwoErdosProblem1046Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1046, https://www.erdosproblems.com/1046 (status
field DISPROVED, contradicted by the page text). UnsolvedMath record UM-30007145 (`EP-1046`),
dataset ulamai/UnsolvedMath v1.8.0.

The disc is open; since `E` is open and bounded this is the same as a closed disc. The site's status
field, and the UnsolvedMath record copied from it, say disproved, but the page text says "The answer
is yes ... as shown by Pommerenke", with the centre at the mean of the zeros of `f`; the page also
records that a separate guess of Erdős, Herzog and Piranian (width at most `2`) is false. The target
follows Pommerenke's theorem. Compared with the formal-conjectures statement
`ErdosProblems/1046.lean` (equivalent, also stated as true; no code imported).
-/

/-- The open lemniscate `E = {z : |f(z)| < 1}` of a complex polynomial. -/
def lemniscate (f : Polynomial ℂ) : Set ℂ :=
  {z | ‖f.eval z‖ < 1}

/-- Erdős Problem 1046: if `f ∈ ℂ[x]` is monic and `E = {z : |f(z)| < 1}` is connected, then `E`
lies in a disc of radius `2`. -/
def connectedLemniscateInDiscRadiusTwo : Prop :=
  ∀ f : Polynomial ℂ, f.Monic → IsConnected (lemniscate f) →
    ∃ c : ℂ, lemniscate f ⊆ Metric.ball c 2

/--
Resolved true: Pommerenke proved that a connected lemniscate `{z : |f(z)| < 1}` of a monic
polynomial lies in the disc of radius `2` centred at the mean of the zeros of `f`;
erdosproblems.com/1046 states that the answer is yes (its status field says disproved, against its
own text), and plby/lean-proofs (`Erdos1046.lean`) has a formal proof of the formal-conjectures
statement. Source: T. F. Bloom, Erdős Problems, Problem #1046, https://www.erdosproblems.com/1046
(status field DISPROVED, contradicted by the page text); resolution: Ch. Pommerenke, On some
problems by Erdős, Herzog and Piranian, Michigan Math. J. 6 (1959), 221-225, the answer is yes, with
the centre at the centroid of the zeros of f (erdosproblems.com/1046),
https://doi.org/10.1307/mmj/1028998227.
-/
public theorem_wanted connectedLemniscateInDiscRadiusTwo_holds : connectedLemniscateInDiscRadiusTwo

end MathlibExt.Analysis.ConnectedLemniscateRadiusTwoErdosProblem1046Wanted
