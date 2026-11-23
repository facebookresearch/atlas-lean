/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook65Wanted

/-- **Mazur's symmetric hull claim (Scottish Book Problem 65).** The claim that for every real
Banach space $E$ and every convex set $W \subseteq E$ with $0 \in W$, if the closure of $W$ has
empty interior (that is, $W$ is nowhere dense), then the closure of the convex hull of
$W \cup (-W)$ also has empty interior. The convex hull of $W \cup (-W)$ is the smallest convex
set containing $W$ that is symmetric about the origin.

The typescript's parenthetical identifies this set with the difference set $W - W$, which is
larger in general; the smallest-set reading is adopted here. For the Ad 65 counterexample $W$
(non-decreasing functions, a cone) the two constructions coincide, so the counterexample still
applies. -/
def ScottishBookProblem65Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (W : Set E),
    Convex ℝ W → 0 ∈ W → interior (closure W) = ∅ →
    interior (closure (convexHull ℝ
      (W ∪ {z | ∃ w ∈ W, z = -w}))) = ∅

/--
**Mazur's Problem 65 has a negative answer.** The symmetric hull claim of Scottish Book
Problem 65 is false: there are a real Banach space $E$ and a convex set $W \subseteq E$ with
$0 \in W$ whose closure has empty interior, such that the closure of the convex hull of
$W \cup (-W)$ has nonempty interior.

Source: S. Mazur, Problem 65 of the
Scottish Book; typescript Ad 65 records the negative answer, with the
counterexample of the set `W` of non-decreasing functions in the space
`(C)` of continuous functions: `W` is convex, nowhere dense, and
contains `0`, while the symmetric convex set containing `W` contains
all functions of bounded variation and is not nowhere dense (indeed,
it is dense, since it contains the polynomials). For this `W` (a cone)
the `W ∪ -W` hull and the difference-set construction coincide, so the
counterexample refutes the corrected claim too.
-/
theorem_wanted mazur65_refuted : ¬ ScottishBookProblem65Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook65Wanted
