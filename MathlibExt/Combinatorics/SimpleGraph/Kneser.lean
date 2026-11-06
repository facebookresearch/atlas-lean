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
public import MathlibExt.Combinatorics.SimpleGraph.GeneralizedJohnson

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 439

/-!
# Kneser

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 439

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 1.6 Johnson graphs, page 9. (for
  `kneserGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 439: Kneser graph

/-- **Kneser graph.** For natural numbers $v$ and $k$, the Kneser graph $K_{v:k}$ has as vertices
the $k$-element subsets of the $v$-element set $\{0, 1, \dots, v-1\}$, with two distinct vertices
adjacent when they are disjoint.

By definition, $K_{v:k}$ is the generalized Johnson graph $J(v, k, 0)$.
-/
def kneserGraph (v k : ℕ) :
    SimpleGraph {S : Finset (Fin v) // S.card = k} :=
  johnsonGraph v k 0

end MetaMathlibExt

end
