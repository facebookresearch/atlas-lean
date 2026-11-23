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

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 1

open SimpleGraph Finset

/-!
# GeneralizedJohnson

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 1

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 1.6, page 9. (for `johnsonGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 1: Generalized Johnson graph

/-- **Generalized Johnson graph.** For natural numbers $v$, $k$ and $i$, the generalized Johnson
graph $J(v,k,i)$ is the graph whose vertices are the $k$-element subsets of $\{0, 1, \dots, v-1\}$,
in which two distinct vertices are adjacent if and only if their intersection has exactly $i$
elements.

The usual setting is $v \ge k \ge i$; the definition does not require it.
-/
def johnsonGraph (v k i : ℕ) :
    SimpleGraph {S : Finset (Fin v) // S.card = k} where
  Adj A B := A ≠ B ∧ (A.val ∩ B.val).card = i
  symm := ⟨fun {A B} ⟨hne, hcard⟩ => ⟨hne.symm, by rw [inter_comm]; exact hcard⟩⟩
  loopless := ⟨fun {A} ⟨hne, _⟩ => hne rfl⟩

end MetaMathlibExt

end
