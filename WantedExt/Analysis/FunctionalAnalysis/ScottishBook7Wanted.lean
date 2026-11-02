/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook7Wanted

/-- **Scottish Book Problem 7 (Mazur–Banach).** The claim that in every real Banach space $E$,
any two closed convex subsets $A, B \subseteq E$ whose linear spans are infinite-dimensional are
homeomorphic, with the subspace topologies. -/
def ScottishBookProblem7Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A B : Set E), IsClosed A → Convex ℝ A →
    ¬ Module.Finite ℝ ↥(Submodule.span ℝ A) → IsClosed B → Convex ℝ B →
    ¬ Module.Finite ℝ ↥(Submodule.span ℝ B) → Nonempty (↥A ≃ₜ ↥B)

/--
**Scottish Book Problem 7 fails: closed convex sets need not be homeomorphic.** The Scottish Book
Problem 7 claim is false: there are a real Banach space $E$ and closed convex subsets
$A, B \subseteq E$, each with infinite-dimensional linear span, that are not homeomorphic.

For example, a compact infinite-dimensional closed convex set, such as the Hilbert cube, is not
homeomorphic to a noncompact one, such as the whole space, since compactness is a topological
invariant.

Source:
S. Mazur and S. Banach, Problem 7 of the Scottish Book; T. Banakh's
observation as reported in the 2026 survey "90+ years of the Scottish Book"
(arXiv:2603.27867). The modified classification problem was solved for
Frechet spaces by Banakh-Cauty, Studia Mathematica 205 (2011) 1-11.
-/
theorem_wanted closedConvexSetsHomeomorphic_refuted : ¬ ScottishBookProblem7Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook7Wanted
