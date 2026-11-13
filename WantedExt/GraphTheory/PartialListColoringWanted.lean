/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Partial List Coloring
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Rat.Cast.Order
public import MathlibExt.Combinatorics.SimpleGraph.ListColoring

@[expose] public section

namespace MathlibExt.GraphTheory.PartialListColoringWanted

/-! Source record `OPG-788`. Iradmusa's partial list coloring monotonicity conjecture
from the Open Problem Garden (posted May 12th, 2008): the ratio `λ_t / t` is
nonincreasing in `t` up to the list chromatic number. -/

/-- **Proper list colouring of a vertex subset.** Let $G$ be a graph on a finite vertex set $V$,
let $L$ assign to each vertex $v$ a finite list $L(v)$ of colours (natural numbers), and let
$S \subseteq V$. A map $f : V \to \mathbb{N}$ is a proper $L$-colouring of $S$ when
$f(v) \in L(v)$ for every $v \in S$ and $f(v) \ne f(w)$ for all adjacent $v, w \in S$. -/
def IsListColoring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset ℕ) (f : V → ℕ) (S : Finset V) : Prop :=
  (∀ v ∈ S, f v ∈ L v) ∧ ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → f v ≠ f w

/-- **Maximum number of list-colourable vertices.** For a graph $G$ on a finite vertex set and an
assignment $L$ of a finite list $L(v)$ of natural-number colours to each vertex $v$, $\lambda_L$
is the largest $k$ such that some set of $k$ vertices of $G$ has a proper $L$-colouring. -/
noncomputable def lambdaMax {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset V, ∃ f : V → ℕ, S.card = k ∧ IsListColoring G L f S}

/-- **The partial list colouring number $\lambda_t$.** For a graph $G$ on a finite vertex set and
a natural number $t$, $\lambda_t$ is the minimum of $\lambda_L$ over all assignments $L$ of a
list $L(v)$ of exactly $t$ natural-number colours to each vertex $v$, where $\lambda_L$ is the
largest $k$ such that some set of $k$ vertices of $G$ has a proper $L$-colouring. -/
noncomputable def lambdaMin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ L : V → Finset ℕ, (∀ v, (L v).card = t) ∧ lambdaMax G L = k}

/-- **Iradmusa's partial list colouring conjecture.** For every finite graph $G$ with choice
number $\chi_\ell$ and all natural numbers $r$, $s$ with $1 \le r \le s \le \chi_\ell$, one has
$\lambda_r / r \ge \lambda_s / s$, where $\lambda_t$ is the minimum, over all assignments of
lists of exactly $t$ colours to the vertices, of the largest number of vertices of $G$ that can
be properly coloured from their lists. -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (χ_ℓ r s : ℕ),
    G.IsChoiceNumber χ_ℓ →
    1 ≤ r → r ≤ s → s ≤ χ_ℓ →
    (lambdaMin G r : ℚ) / (r : ℚ) ≥ (lambdaMin G s : ℚ) / (s : ℚ)

/--
**The partial list colouring conjecture is false.** There exist a finite graph $G$ with choice
number $\chi_\ell$ and natural numbers $r$, $s$ with $1 \le r \le s \le \chi_\ell$ such that
$\lambda_r / r < \lambda_s / s$, where $\lambda_t$ is the minimum, over all assignments of lists
of exactly $t$ colours to the vertices, of the largest number of vertices of $G$ that can be
properly coloured from their lists. So Iradmusa's partial list colouring conjecture fails.

Noel's counterexample (Theorem 1.1) is a 14-vertex graph (four triangles plus two terminals)
with choice number 3 and a 2-list assignment colouring at most 9 vertices, so
$\lambda_2 / 2 \le 9/2 < 14/3 = \lambda_3 / 3$.

Source: Jonathan A. Noel, The Partial List Colouring Conjecture is False, arXiv preprint
(2026), arXiv:2609.23291, https://arxiv.org/abs/2609.23291. Moved from
`OpenConjectures/GraphTheory/PartialListColoring`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GraphTheory.PartialListColoringWanted
