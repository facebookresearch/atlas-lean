/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.Degeneracy
import MathlibExt.Combinatorics.SimpleGraph.DegeneracyColoring

@[expose] public section

namespace SimpleGraph

example {V : Type*} [Finite V] (U : Set V) : (⊥ : SimpleGraph V).IsDegenerateOn U 0 := by
  intro W hWne _
  obtain ⟨v, hvW⟩ := hWne
  refine ⟨v, hvW, ?_⟩
  simp

example {V : Type*} [Finite V] {G : SimpleGraph V} {U : Set V} {k l : ℕ}
    (h : G.IsDegenerateOn U k) (hkl : k ≤ l) : G.IsDegenerateOn U l :=
  h.mono hkl

example {V : Type*} [Finite V] {G : SimpleGraph V} {U : Set V} {k : ℕ}
    (h : G.IsDegenerate k) : G.IsDegenerateOn U k :=
  h.isDegenerateOn U

-- DegeneracyColoring API: edgeless-graph and `k = 0` boundaries.

example {V : Type*} [Finite V] (k : ℕ) : (⊥ : SimpleGraph V).IsDegenerate k :=
  isDegenerate_bot k

example {V : Type*} [Finite V] (k : ℕ) :
    (⊥ : SimpleGraph V).Colorable (k + 1) :=
  (isDegenerate_bot k).colorable

example {V : Type*} [Finite V] : (⊥ : SimpleGraph V).Colorable 1 := by
  have h := (isDegenerate_bot (V := V) 0).colorable
  simpa using h

example {V : Type*} [Finite V] (k : ℕ) :
    (⊥ : SimpleGraph V).chromaticNumber ≤ k + 1 := by
  have := Fintype.ofFinite V
  exact (isDegenerate_bot k).chromaticNumber_le

example {V : Type*} [Finite V] {G : SimpleGraph V} {k : ℕ} (s : Finset V)
    (h : G.IsDegenerateOn (↑s : Set V) k) (hs : s.Nonempty) :
    ∃ v ∈ s, (G.neighborSet v ∩ ↑s).ncard ≤ k :=
  h.exists_small_vertex s hs

example {V : Type*} [Finite V] {G : SimpleGraph V} {k : ℕ}
    (h : G.IsDegenerateOn (↑(∅ : Finset V) : Set V) k) : True := by
  obtain ⟨e, hinj, hbound⟩ := h.exists_injOn_ordering ∅
  obtain ⟨f, hf⟩ := h.exists_coloringFun ∅
  trivial

example {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (h : ∀ v, G.degree v ≤ k) : G.IsDegenerate k :=
  IsDegenerate.of_forall_degree_le h

end SimpleGraph

end
