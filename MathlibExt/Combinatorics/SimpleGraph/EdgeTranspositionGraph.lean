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

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 432

/-!
# EdgeTranspositionGraph

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 432

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 3.10, page 52. (for
  `edgeTranspositionGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 432: Edge-transposition graph

/-- **Edge-transposition graph.** Let $n$ be a natural number and let $T$ be a set of permutations
of $\{0, 1, \dots, n - 1\}$, typically a set of transpositions in the symmetric group $S_n$. The
edge-transposition graph of $T$ is the simple graph with vertex set $\{0, 1, \dots, n - 1\}$ in
which two distinct vertices $i$ and $j$ are adjacent if and only if the transposition swapping $i$
and $j$ belongs to $T$.
-/
def edgeTranspositionGraph {n : ℕ} (T : Set (Equiv.Perm (Fin n))) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => Equiv.swap i j ∈ T)

end MetaMathlibExt

end
