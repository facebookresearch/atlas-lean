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

public import MathlibExt.Combinatorics.SimpleGraph.GraphProducts.LexProduct
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.FinCases

@[expose] public section

open SimpleGraph

namespace MathlibExtTest.Combinatorics.SimpleGraph.GraphProducts.LexProduct

open MetaMathlibExt

-- Combinatorics 3: Lexicographic product

/-- Sanity check: the lex product of the graph $K_2$ with vertices $0,1$ with the
disconnected graph on the same vertex set is equal to the graph on 4 vertices with
2 parallel edges -/

abbrev D2 : SimpleGraph (Fin 2) := ⊥

abbrev K2 : SimpleGraph (Fin 2) := ⊤

abbrev twoK2 : SimpleGraph (Fin 2 × Fin 2) :=
  fromEdgeSet {s((0, 0), (0, 1)), s((1, 0), (1, 1))}

instance : DecidableRel (D2.lexProduct K2).Adj := fun p q => by
  unfold SimpleGraph.lexProduct
  infer_instance

example : D2.lexProduct K2 = twoK2 := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;> decide

end MathlibExtTest.Combinatorics.SimpleGraph.GraphProducts.LexProduct

end
