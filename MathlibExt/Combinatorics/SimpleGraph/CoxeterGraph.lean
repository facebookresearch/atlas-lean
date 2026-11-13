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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 18

/-!
# CoxeterGraph

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 18

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 4.6 The Coxeter Graph, page 69. (for
  `coxeterGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 18: Coxeter graph

def fin4ToZMod7 : Fin 4 → ZMod 7
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- **Coxeter graph.** The Coxeter graph is the simple graph whose $28$ vertices are the pairs
$(i, j)$ with $i \in \{0, 1, 2, 3\}$ and $j \in \mathbb{Z}/7\mathbb{Z}$, and whose edges are the
following: for each $i \in \{1, 2, 3\}$, the vertices $(i, j)$ and $(i, j')$ are adjacent when
$j - j' = i$ or $j' - j = i$ in $\mathbb{Z}/7\mathbb{Z}$, and for each $j$ the vertex $(0, j)$ is
adjacent to $(1, j)$, $(2, j)$ and $(3, j)$. There are no other edges.
-/
def coxeterGraph : SimpleGraph (Fin 4 × ZMod 7) :=
  SimpleGraph.fromRel fun a b =>
    (a.1 = b.1 ∧ a.1 ≠ 0 ∧ a.2 - b.2 = fin4ToZMod7 a.1)
    ∨
    (a.1 = 0 ∧ b.1 ≠ 0 ∧ a.2 = b.2)

end MetaMathlibExt

end
