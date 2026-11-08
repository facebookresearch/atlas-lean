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

/-- Given a set of transpositions T of the symmetric group Sₙ, the *edge-transposition graph* is the
graph X whose vertex set is {1,…,n}, and for which (i,j) ∈ E(X) if and only if (ij) ∈ T.
-/
def edgeTranspositionGraph {n : ℕ} (T : Set (Equiv.Perm (Fin n))) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => Equiv.swap i j ∈ T)

end MetaMathlibExt

end
