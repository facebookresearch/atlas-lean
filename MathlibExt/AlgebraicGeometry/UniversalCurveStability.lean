/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The finite marked-graph interface adapts the mathematical definitions in
`TauCeti/AlgebraicGeometry/Curves/DualGraph/Basic.lean`,
`TauCeti/AlgebraicGeometry/Curves/DualGraph/Iso.lean`, and
`TauCeti/AlgebraicGeometry/Curves/DualGraph/Smoothing.lean`
at TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9:
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Licensed under Apache 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Tau Ceti contributors.
Modification notice: use finite ordinal vertex/edge labels, retain
branch permutations, and expose contraction genus equations directly.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation

@[expose] public noncomputable section

/-!
# Contraction-compatible numerical universal stability

Graphs have actual finite vertices, edges with two branches, markings and
genus. A contraction retains exactly the uncontracted edges, has connected
contracted fibers and preserves the genus with the selected-edge Betti
contribution. Universal stability is precisely the finite sum, isomorphism
and contraction equations. No values outside the prescribed genus/marking
graph domain are present.

Source: Kass--Pagani, The stability space of compactified universal
Jacobians, Definitions 3.1--3.2 and Corollary 3.6.
-/

namespace MathlibExt.AlgebraicGeometry.UniversalCurveStability

open Finset
open scoped BigOperators

/-- Valence counts actual branches, including two branches of each loop. -/
def valence {v e : ℕ} (endpoint : Fin e → Fin 2 → Fin v) (w : Fin v) : ℕ :=
  (Finset.univ.filter fun h : Fin e × Fin 2 ↦ endpoint h.1 h.2 = w).card

/-- Number of actual labeled markings on a vertex. -/
def markingCount {v n : ℕ} (mark : Fin n → Fin v) (w : Fin v) : ℕ :=
  (Finset.univ.filter fun i ↦ mark i = w).card

/-- A connected stable marked graph of the stated arithmetic genus. -/
structure StableGraph (g n : ℕ) where
  vertices : ℕ
  nonempty : 0 < vertices
  edges : ℕ
  endpoint : Fin edges → Fin 2 → Fin vertices
  genus : Fin vertices → ℕ
  marking : Fin n → Fin vertices
  connected : ∀ v w, Relation.ReflTransGen
    (fun v w ↦ ∃ e, (endpoint e 0 = v ∧ endpoint e 1 = w) ∨
      (endpoint e 0 = w ∧ endpoint e 1 = v)) v w
  totalGenus : g + vertices = (∑ v, genus v) + edges + 1
  stable : ∀ v, 0 < 2 * (genus v : ℤ) - 2 +
    valence endpoint v + markingCount marking v

/-- Graph isomorphisms include branch orientation permutations. -/
structure GraphIso {g n : ℕ} (G H : StableGraph g n) where
  vertex : Fin G.vertices ≃ Fin H.vertices
  edge : Fin G.edges ≃ Fin H.edges
  branch : Fin G.edges → (Fin 2 ≃ Fin 2)
  endpoint : ∀ e h, H.endpoint (edge e) (branch e h) = vertex (G.endpoint e h)
  genus : ∀ v, H.genus (vertex v) = G.genus v
  marking : ∀ i, H.marking i = vertex (G.marking i)

/-- A genuine contraction of selected edges, with connected fibers and genus update. -/
structure GraphContraction {g n : ℕ} (G H : StableGraph g n) where
  selected : Finset (Fin G.edges)
  vertex : Fin G.vertices → Fin H.vertices
  onto : Function.Surjective vertex
  edge : {e : Fin G.edges // e ∉ selected} ≃ Fin H.edges
  branch : {e : Fin G.edges // e ∉ selected} → (Fin 2 ≃ Fin 2)
  surviving : ∀ e h, H.endpoint (edge e) (branch e h) = vertex (G.endpoint e.val h)
  contracted : ∀ e ∈ selected, vertex (G.endpoint e 0) = vertex (G.endpoint e 1)
  fiberConnected : ∀ v w, vertex v = vertex w → Relation.ReflTransGen
    (fun v w ↦ ∃ e ∈ selected,
      (G.endpoint e 0 = v ∧ G.endpoint e 1 = w) ∨
      (G.endpoint e 0 = w ∧ G.endpoint e 1 = v)) v w
  marking : ∀ i, H.marking i = vertex (G.marking i)
  genus : ∀ w,
    H.genus w + (Finset.univ.filter fun v ↦ vertex v = w).card =
      (∑ v, if vertex v = w then G.genus v else 0) +
        (selected.filter fun e ↦ vertex (G.endpoint e 0) = w).card + 1

/-- Universal stability, on the exact stable-graph domain. -/
structure UniversalStability (g n : ℕ) (d : ℚ) where
  weight : ∀ G : StableGraph g n, Fin G.vertices → ℚ
  total : ∀ G, (∑ v, weight G v) = d
  isomorphism : ∀ G H (e : GraphIso G H) v, weight H (e.vertex v) = weight G v
  contraction : ∀ G H (c : GraphContraction G H) w,
    weight H w = ∑ v, if c.vertex v = w then weight G v else 0

/-- Degree zero provides an explicit consistent witness for the interface. -/
def zeroStability (g n : ℕ) : UniversalStability g n 0 where
  weight _ _ := 0
  total _ := by simp
  isomorphism _ _ _ _ := rfl
  contraction _ _ _ _ := by simp

/-- The two-vertex test graphs in Kass--Pagani Corollary 3.6. -/
def IsDeterminingGraph {g n : ℕ} (G : StableGraph g n) : Prop :=
  G.vertices = 2 ∧ (∀ e, G.endpoint e 0 ≠ G.endpoint e 1) ∧
    (G.edges = 1 ∨
      (G.edges = 2 ∧ ∃ v : Fin G.vertices,
        G.genus v = 0 ∧ markingCount G.marking v = 1))

end MathlibExt.AlgebraicGeometry.UniversalCurveStability
