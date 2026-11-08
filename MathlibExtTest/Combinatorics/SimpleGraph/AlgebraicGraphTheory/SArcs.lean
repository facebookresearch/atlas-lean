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

public import MathlibExt.Combinatorics.SimpleGraph.AlgebraicGraphTheory.SArcs
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.AlgebraicGraphTheory.SArcs

open MetaMathlibExt

-- Combinatorics 14: $X^{(s)}$

deriving instance DecidableEq for SimpleGraph.SArc

abbrev K₃ : SimpleGraph (Fin 3) := SimpleGraph.completeGraph (Fin 3)

abbrev a012 : K₃.SArc 2 := ⟨![0, 1, 2], by decide, by decide⟩

abbrev a01 : K₃.SArc 1 := ⟨![0, 1], by decide, by decide⟩

abbrev a12 : K₃.SArc 1 := ⟨![1, 2], by decide, by decide⟩

@[ext] theorem _root_.SimpleGraph.SArc.ext {V : Type*} [Fintype V] {G : SimpleGraph V} {s : ℕ}
    {a b : G.SArc s} (h : a.vertices = b.vertices) : a = b := by
  cases a; cases b; simp_all

example : (K₃.arcDigraph 1).Adj a01 a12 :=
  ⟨a012, by apply SimpleGraph.SArc.ext; decide,
          by apply SimpleGraph.SArc.ext; decide⟩

end MathlibExtTest.Combinatorics.SimpleGraph.AlgebraicGraphTheory.SArcs

end
