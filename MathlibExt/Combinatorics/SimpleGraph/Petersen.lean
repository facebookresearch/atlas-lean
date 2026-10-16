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
/-!
# Petersen

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 10
-/

@[expose] public section

open SimpleGraph Finset

-- Combinatorics 10: Petersen graph
def petersenGraph : SimpleGraph {S : Finset (Fin 5) // S.card = 2} :=
  johnsonGraph 5 2 0


instance : DecidableRel petersenGraph.Adj := fun A B => by
  unfold petersenGraph johnsonGraph SimpleGraph.Adj
  infer_instance

-- Sanity check: The Petersen graph has 15 edges
example : petersenGraph.edgeFinset.card = 15 := by
    decide

end
