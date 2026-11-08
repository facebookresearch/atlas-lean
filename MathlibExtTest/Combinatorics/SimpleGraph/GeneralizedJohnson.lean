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

public import MathlibExt.Combinatorics.SimpleGraph.GeneralizedJohnson
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

open SimpleGraph Finset

namespace MathlibExtTest.Combinatorics.SimpleGraph.GeneralizedJohnson

open MetaMathlibExt

-- Combinatorics 1: Generalized Johnson graph

-- Sanity check: J(2,1,1) is the graph with 2 vertices and 0 edges.

example : johnsonGraph 2 1 1 ≃g (⊥ : SimpleGraph (Fin 2)) :=
  { toEquiv :=
      { toFun := fun S => if S.val = {0} then 0 else 1
        invFun := fun i => if i = 0 then ⟨{0}, by decide⟩ else ⟨{1}, by decide⟩
        left_inv := by decide
        right_inv := by decide }
    map_rel_iff' := by
      intro a b
      rw [bot_adj]
      constructor
      · exact False.elim
      · intro h
        obtain ⟨hne, hcard⟩ := h
        have hsub : a.val ∩ b.val ⊆ a.val := Finset.inter_subset_left
        have heq : a.val ∩ b.val = a.val :=
          Finset.eq_of_subset_of_card_le hsub (by rw [a.property, hcard])
        have hAB : a.val ⊆ b.val := by rw [← heq]; exact Finset.inter_subset_right
        have hval : a.val = b.val :=
          Finset.eq_of_subset_of_card_le hAB (by rw [b.property, a.property])
        exact absurd (Subtype.ext hval) hne }

end MathlibExtTest.Combinatorics.SimpleGraph.GeneralizedJohnson

end
