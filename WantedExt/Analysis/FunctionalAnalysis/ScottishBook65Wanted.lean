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

/-- Mazur's Problem 65 from the Scottish Book: in a Banach space, if a
convex set `W` containing the origin is nowhere dense, is the smallest
convex set containing `W` that is symmetric about the origin — the
convex hull of `W ∪ -W` — also nowhere dense? Here
nowhere dense means the interior of the closure is empty. Note: the
typescript's parenthetical identifies this set with the difference set
`W - W`, which is larger in general; the smallest-set reading is adopted
here. For the Ad 65 counterexample `W` (non-decreasing functions, a cone)
the two constructions coincide, so the counterexample still applies. -/
def ScottishBookProblem65Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (W : Set E),
    Convex ℝ W → 0 ∈ W → interior (closure W) = ∅ →
    interior (closure (convexHull ℝ
      (W ∪ {z | ∃ w ∈ W, z = -w}))) = ∅

/--
Mazur's Problem 65 is false. Source: S. Mazur, Problem 65 of the
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
