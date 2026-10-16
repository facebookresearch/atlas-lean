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
# Kneser

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 439
-/

@[expose] public section

open SimpleGraph

-- Combinatorics 439: Kneser graph
def kneserGraph (v k : ℕ) :
    SimpleGraph {S : Finset (Fin v) // S.card = k} :=
  johnsonGraph v k 0


/-- Adjacency in a Kneser graph is decidable. -/
instance (v k : ℕ) : DecidableRel (kneserGraph v k).Adj :=
  fun A B => inferInstanceAs (Decidable (A ≠ B ∧ (A.val ∩ B.val).card = 0))


/-- Adjacency in a complete graph is decidable. -/
instance : DecidableRel (⊤ : SimpleGraph {S : Finset (Fin 2) // S.card = 1}).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b))


abbrev kneser := kneserGraph 2 1


/-- `K(2,1)` is complete. -/
theorem kneser21_eq_top : kneser = ⊤ := by
  ext a b
  revert a b
  decide

end
