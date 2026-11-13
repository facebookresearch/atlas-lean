/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Epsilon-light vertex subsets
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace MathlibExt.Combinatorics.EpsilonLightSubsetWanted

open SimpleGraph

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `S` is `ε`-light if `εL - L_S` is positive semidefinite. -/
def IsEpsilonLight (G : SimpleGraph V) (ε : ℝ) (S : Finset V) : Prop :=
  open Classical in
  letI G_S := G.induce S |>.spanningCoe
  letI L := lapMatrix ℝ G
  letI L_S := lapMatrix ℝ (G_S)
  PosSemidef (ε • L - L_S)

/-- Large `ε`-light subsets exist uniformly. -/
def epsilonLightSubsetExists : Prop :=
  ∃ (c : ℝ), c > 0 ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ε : ℝ),
  0 < ε → ε < 1 →
  ∃ (S : Finset (Fin n)), IsEpsilonLight G ε S ∧ (S.card : ℝ) ≥ c * ε * n

/--
Resolved true: Question 6 of arXiv:2602.05192 is proved: v2 (16 Mar 2026), Appendix B.6 proves
Lemma B.1 (an epsilon-light subset of size at least eps*n/42 exists in every weighted graph).
Source: First Proof authors, arXiv:2602.05192v2, Appendix B.6 (Lemma B.1),
https://arxiv.org/html/2602.05192v2. Moved from
`OpenConjectures/Combinatorics/EpsilonLightSubset`.
-/
public theorem_wanted epsilonLightSubsetExists_holds : epsilonLightSubsetExists

end MathlibExt.Combinatorics.EpsilonLightSubsetWanted
