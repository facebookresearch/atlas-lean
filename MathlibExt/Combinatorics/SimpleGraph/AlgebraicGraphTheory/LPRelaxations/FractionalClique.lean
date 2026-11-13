/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.NormNum.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 436

/-!
# FractionalClique

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 436

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 7.2 Fractional Cliques, page 136. (for
  `SimpleGraph.fracCliqueNumber`)
-/

namespace MetaMathlibExt

-- Combinatorics 436: Fractional clique/fractional clique number

structure FracClique {V : Type*} [Fintype V] (G : SimpleGraph V) where
  w : V → ℝ
  nonneg : ∀ v, 0 ≤ w v
  indep_le : ∀ s : Finset V, G.IsIndepSet s → ∑ v ∈ s, w v ≤ 1

def FracClique.weight {V : Type*} [Fintype V] {G : SimpleGraph V}
    (c : FracClique G) : ℝ :=
  ∑ v ∈ Finset.univ, c.w v

/-- **Fractional clique number.** Let $X$ be a graph with finite vertex set $V(X)$. A
*fractional clique* of $X$ is a function $f \colon V(X) \to \mathbb{R}$ with $f(v) \ge 0$ for
every vertex $v$, such that $\sum_{v \in S} f(v) \le 1$ for every independent set $S$ of $X$. The
*weight* of $f$ is $\sum_{v \in V(X)} f(v)$. The *fractional clique number* $\omega^*(X)$ of $X$
is the supremum of the weights of all fractional cliques of $X$.
-/
noncomputable def _root_.SimpleGraph.fracCliqueNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℝ :=
  sSup {q : ℝ | ∃ c : FracClique G, c.weight = q}

end MetaMathlibExt

end
