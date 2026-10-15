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
public import Mathlib.Tactic.FinCases
/-!
# LexProduct

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 3
-/

@[expose] public section

open SimpleGraph

-- Combinatorics 3: Lexicographic product
def SimpleGraph.lexProduct {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V × W) :=
  SimpleGraph.fromRel fun (p q : V × W) => G.Adj p.1 q.1 ∨ p.1 = q.1 ∧ H.Adj p.2 q.2


/-- Sanity check: the lex product of the graph $K_2$ with vertices $0,1$ with the 
disconnected graph on the same vertex set is equal to the graph on 4 vertices with 
2 parallel edges -/
abbrev D2 : SimpleGraph (Fin 2) := ⊥

abbrev K2lex : SimpleGraph (Fin 2) := ⊤

abbrev twoK2 : SimpleGraph (Fin 2 × Fin 2) :=
  fromEdgeSet {s((0, 0), (0, 1)), s((1, 0), (1, 1))}


instance : DecidableRel (D2.lexProduct K2lex).Adj := fun p q => by
  unfold SimpleGraph.lexProduct
  infer_instance

example : D2.lexProduct K2lex = twoK2 := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;> decide

end
