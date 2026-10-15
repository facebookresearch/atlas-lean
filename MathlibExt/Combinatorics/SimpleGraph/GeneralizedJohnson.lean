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
/-!
# GeneralizedJohnson

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 1
-/

@[expose] public section

open SimpleGraph Finset

-- Combinatorics 1: Generalized Johnson graph

def johnsonGraph (v k i : ℕ) :
    SimpleGraph {S : Finset (Fin v) // S.card = k} where
  Adj A B := A ≠ B ∧ (A.val ∩ B.val).card = i
  symm := ⟨fun {A B} ⟨hne, hcard⟩ => ⟨hne.symm, by rw [inter_comm]; exact hcard⟩⟩
  loopless := ⟨fun {A} ⟨hne, _⟩ => hne rfl⟩

end
