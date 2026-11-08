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
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 428

/-!
# LineGraph

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 428

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 1.7 Line graphs, page 10. (for
  `SimpleGraph.IsLineGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 428: Is line graph

/-- The *line graph* of a finite graph X is the finite graph L(X) with the edges of X as its
vertices, and where two edges of X are adjacent in L(X) if and only if they are incident in X.
-/
def SimpleGraph.IsLineGraph {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (H : SimpleGraph (Fin k)),
    Nonempty (G ≃g H.lineGraph)

end MetaMathlibExt

end
