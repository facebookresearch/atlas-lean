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

public import MathlibExt.Combinatorics.Digraph.DirectedCayley
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace MathlibExtTest.Combinatorics.Digraph.DirectedCayley

open MetaMathlibExt

-- Combinatorics 58: Cayley arc/Cayley digraph

abbrev U5 := Units (ZMod 5)

-- U(5) = {1,2,3,4} with explicit inverses (2⁻¹=3, 3⁻¹=2, 4⁻¹=4 mod 5)

def u1 : U5 := ⟨1, 1, by decide, by decide⟩

def u2 : U5 := ⟨2, 3, by decide, by decide⟩

def u3 : U5 := ⟨3, 2, by decide, by decide⟩

def u4 : U5 := ⟨4, 4, by decide, by decide⟩

-- the digraph X(U(5), {2})

abbrev D5 : Digraph U5 := directedCayleyGraph ({u2} : Set U5)

-- arcs are 1→2, 2→4, 3→1, 4→3

theorem u5_arcs : ∀ x y : U5, D5.Adj x y ↔
    (x = u1 ∧ y = u2) ∨ (x = u2 ∧ y = u4) ∨
      (x = u3 ∧ y = u1) ∨ (x = u4 ∧ y = u3) := by
  simp only [D5, directedCayleyGraph, cayleyArc, Set.mem_singleton_iff, exists_eq_left]
  decide

-- arc-set form: the set of arcs equals {(1,2),(2,4),(3,1),(4,3)}

example : {(x, y) : U5 × U5 | D5.Adj x y}
    = {(u1, u2), (u2, u4), (u3, u1), (u4, u3)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  exact u5_arcs x y

end MathlibExtTest.Combinatorics.Digraph.DirectedCayley

end
