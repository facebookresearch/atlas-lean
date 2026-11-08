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

-- Source: Lean Definition Library (Airtable) records: Combinatorics 10

/-!
# Petersen

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 10

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 1.6 Johnson Graphs, page 9. (for
  `petersenGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 10: Petersen graph

/-- The Petersen graph is the generalized Johnson graph J(5,2,0). -/
def petersenGraph : SimpleGraph {S : Finset (Fin 5) // S.card = 2} :=
  johnsonGraph 5 2 0

end MetaMathlibExt

end
