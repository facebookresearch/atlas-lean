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

/-- Mazur and Banach's Problem 7 from the Scottish Book: are any two closed,
infinite-dimensional convex subsets of a Banach space always homeomorphic? -/
def ScottishBookProblem7Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A B : Set E), IsClosed A → Convex ℝ A →
    ¬ Module.Finite ℝ ↥(Submodule.span ℝ A) → IsClosed B → Convex ℝ B →
    ¬ Module.Finite ℝ ↥(Submodule.span ℝ B) → Nonempty (↥A ≃ₜ ↥B)

/--
Problem 7 is false as stated: a compact infinite-dimensional closed convex
set, such as the Hilbert cube, is not homeomorphic to a noncompact one, such
as the whole space, since compactness is a topological invariant. Source:
S. Mazur and S. Banach, Problem 7 of the Scottish Book; T. Banakh's
observation as reported in the 2026 survey "90+ years of the Scottish Book"
(arXiv:2603.27867). The modified classification problem was solved for
Frechet spaces by Banakh-Cauty, Studia Mathematica 205 (2011) 1-11.
-/
theorem_wanted closedConvexSetsHomeomorphic_refuted : ¬ ScottishBookProblem7Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook7Wanted
