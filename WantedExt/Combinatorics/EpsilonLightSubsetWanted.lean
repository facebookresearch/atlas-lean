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
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace MathlibExt.Combinatorics.EpsilonLightSubsetWanted

open SimpleGraph

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **ε-light vertex sets.** Let $G$ be a simple graph on a finite vertex set $V$, let
$\varepsilon$ be a real number and let $S \subseteq V$. Let $L$ be the real Laplacian matrix of
$G$ and $L_S$ the real Laplacian matrix of the graph on $V$ whose edges are the edges of $G$ with
both endpoints in $S$. The set $S$ is $\varepsilon$-light in $G$ if $\varepsilon L - L_S$ is
positive semidefinite. -/
def IsEpsilonLight (G : SimpleGraph V) (ε : ℝ) (S : Finset V) : Prop :=
  open Classical in
  letI G_S := G.induce S |>.spanningCoe
  letI L := lapMatrix ℝ G
  letI L_S := lapMatrix ℝ (G_S)
  PosSemidef (ε • L - L_S)

/-- **The large ε-light subset property.** The statement that there is a real constant $c > 0$
such that for every natural number $n$, every simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ and every real number $\varepsilon$ with $0 < \varepsilon < 1$, some set $S$
of vertices that is $\varepsilon$-light in $G$ has at least $c \varepsilon n$ elements. -/
def epsilonLightSubsetExists : Prop :=
  ∃ (c : ℝ), c > 0 ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ε : ℝ),
  0 < ε → ε < 1 →
  ∃ (S : Finset (Fin n)), IsEpsilonLight G ε S ∧ (S.card : ℝ) ≥ c * ε * n

/--
**Every graph has a large ε-light vertex set.** There is a real constant $c > 0$ such that for
every natural number $n$, every simple graph $G$ on the vertex set $\{0, \dots, n-1\}$ and every
real number $\varepsilon$ with $0 < \varepsilon < 1$, there is a set $S$ of vertices with at least
$c \varepsilon n$ elements that is $\varepsilon$-light in $G$: the matrix $\varepsilon L - L_S$ is
positive semidefinite, where $L$ is the real Laplacian matrix of $G$ and $L_S$ is the real
Laplacian matrix of the graph on all $n$ vertices whose edges are the edges of $G$ with both
endpoints in $S$.

Appendix B.6 of the source proves this, with $c = 1/42$, as Lemma B.1 (stated for weighted graphs).

Source: First Proof authors, arXiv:2602.05192v2, Appendix B.6 (Lemma B.1),
https://arxiv.org/html/2602.05192v2. Moved from
`OpenConjectures/Combinatorics/EpsilonLightSubset`.
-/
public theorem_wanted epsilonLightSubsetExists_holds : epsilonLightSubsetExists

end MathlibExt.Combinatorics.EpsilonLightSubsetWanted
