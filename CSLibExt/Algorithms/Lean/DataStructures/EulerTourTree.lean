/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# Euler tours of rooted trees

This file defines rooted ordered trees and their Euler tours. The `tour` of a tree
is the vertex sequence of a depth-first walk that returns to the parent after each
child subtree, so every tree edge is traversed twice, once in each direction. The
`arcTour` is the sequence of consecutively traversed arcs; a tree with `n` vertices
has tour length `2 * n - 1` and exactly `2 * (n - 1)` arcs.

Vertices need not be distinct in a raw `Tree`; the dynamic-forest reading
(placing vertices of one tree in another) requires the `Tree.Valid`
invariant (`vertices` duplicate-free) plus disjoint vertex sets for `link`,
recorded in `Tree.valid_link`. Without those hypotheses `link`/`tour` are
still total list operations on labelled trees, but they do not describe a
forest link.

Link and cut are recorded at the level of tours. `link t₁ t₂` attaches `t₂` as the
last child of the root of `t₁`, and its tour is the list splice
`tour t₁ ++ tour t₂ ++ [t₁.root]`: the tour of `t₁` is a prefix and the tour of `t₂`
occurs as a contiguous block. `cutLast` removes the last child subtree of the root
and inverts `link`. These are the sequence operations underlying Euler-tour trees
for dynamic forests.

Out of scope: balance and complexity (tours are plain lists here, so splicing is
linear in this representation, not the logarithmic bound of a balanced sequence),
subtree aggregate queries over tours, and the link-cut tree proper. The splay-based
link-cut tree is deferred until a splay tree module is present in this library; this
file provides the Euler-tour representation and its splice specification only.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

namespace EulerTourTree

/-- A rooted ordered tree: a root vertex with an ordered list of child subtrees. -/
inductive Tree (V : Type u) where
  | node (root : V) (children : List (Tree V)) : Tree V
deriving Repr

namespace Tree

variable {V : Type u}

/-- Induction on a tree from the statement for every child subtree. The built-in
`induction` tactic does not support the nested recursion through `List`, so this
principle is derived from `Tree.rec` and used with `induction … using`. -/
theorem children_ind {motive : Tree V → Prop}
    (node : ∀ (r : V) (cs : List (Tree V)), (∀ c ∈ cs, motive c) →
      motive (.node r cs))
    (t : Tree V) : motive t :=
  Tree.rec (motive_1 := motive) (motive_2 := fun cs => ∀ c ∈ cs, motive c)
    (fun r cs ih => node r cs ih)
    (fun c hc => (List.not_mem_nil hc).elim)
    (fun c cs ihc ihcs x hx => by
      rcases List.mem_cons.mp hx with rfl | h
      · exact ihc
      · exact ihcs x h)
    t

/-- The root vertex of a tree. -/
def root : Tree V → V
  | .node r _ => r

/-- The child subtrees of the root, in order. -/
def children : Tree V → List (Tree V)
  | .node _ cs => cs

@[simp] theorem root_node (r : V) (cs : List (Tree V)) : root (.node r cs) = r :=
  rfl

@[simp] theorem children_node (r : V) (cs : List (Tree V)) :
    children (.node r cs) = cs :=
  rfl

/-- The number of vertices of a tree. -/
def size : Tree V → Nat
  | .node _ cs => 1 + (cs.map size).sum

theorem size_pos (t : Tree V) : 0 < size t := by
  cases t with
  | node r cs => simp only [size]; omega

/-- Accumulator preorder traversal: `verticesAux t acc = vertices t ++ acc`
(see `verticesAux_eq`), so `vertices` is linear rather than repeatedly
appending child lists. -/
def verticesAux : Tree V → List V → List V
  | .node r cs, acc => r :: cs.foldr (fun c acc => verticesAux c acc) acc

/-- The vertices of a tree in preorder. -/
def vertices (t : Tree V) : List V :=
  verticesAux t []

/-- The accumulator traversal appends the preorder list onto its accumulator. -/
theorem verticesAux_eq (t : Tree V) (acc : List V) :
    verticesAux t acc = vertices t ++ acc := by
  induction t using Tree.children_ind generalizing acc with
  | node r cs ih =>
      have hfold : ∀ (cs : List (Tree V)) (acc : List V),
          (∀ c ∈ cs, ∀ acc, verticesAux c acc = vertices c ++ acc) →
          cs.foldr (fun c acc => verticesAux c acc) acc =
            cs.flatMap vertices ++ acc := by
        intro cs
        induction cs with
        | nil => intro acc _; rfl
        | cons c cs ihl =>
            intro acc h
            simp only [List.foldr_cons, List.flatMap_cons, List.append_assoc]
            rw [ihl acc (fun x hx => h x (List.mem_cons_of_mem c hx)),
              h c (by simp)]
      have hnode : vertices (.node r cs) = r :: cs.flatMap vertices := by
        rw [vertices, verticesAux, hfold cs [] ih]
        simp
      rw [verticesAux, hfold cs acc ih, hnode]
      simp

/-- Characteristic node equation for `vertices` (the former definition). -/
theorem vertices_node (r : V) (cs : List (Tree V)) :
    vertices (.node r cs) = r :: cs.flatMap vertices := by
  have hfold : ∀ (cs : List (Tree V)),
      cs.foldr (fun c acc => verticesAux c acc) [] = cs.flatMap vertices := by
    intro cs
    induction cs with
    | nil => rfl
    | cons c cs ihl =>
        simp only [List.foldr_cons, List.flatMap_cons]
        rw [verticesAux_eq, ihl]
  rw [vertices, verticesAux, hfold]

theorem vertices_length (t : Tree V) : (vertices t).length = size t := by
  induction t using Tree.children_ind with
  | node r cs ih =>
      have hsum : ∀ cs : List (Tree V),
          (∀ c ∈ cs, (vertices c).length = size c) →
          (cs.flatMap vertices).length = (cs.map size).sum := by
        intro cs
        induction cs with
        | nil => intro _; rfl
        | cons c cs ihl =>
            intro h
            rw [List.flatMap_cons, List.length_append, h c (by simp),
              List.map_cons, List.sum_cons,
              ihl (fun x hx => h x (List.mem_cons_of_mem c hx))]
      simp only [vertices_node, size, List.length_cons]
      rw [hsum cs ih]
      omega

/-- Accumulator Euler tour: `tourAux t acc = tour t ++ acc` (see
`tourAux_eq`), so `tour` is linear rather than repeatedly appending child
tours. -/
def tourAux : Tree V → List V → List V
  | .node r cs, acc =>
      r :: cs.foldr (fun c acc => tourAux c (r :: acc)) acc

/-- The Euler tour of a tree: the vertex sequence of the depth-first walk that
returns to the parent vertex after each child subtree. -/
def tour (t : Tree V) : List V :=
  tourAux t []

/-- The accumulator tour appends the tour onto its accumulator. -/
theorem tourAux_eq (t : Tree V) (acc : List V) :
    tourAux t acc = tour t ++ acc := by
  induction t using Tree.children_ind generalizing acc with
  | node r cs ih =>
      have hfold : ∀ (cs : List (Tree V)) (acc : List V),
          (∀ c ∈ cs, ∀ acc, tourAux c acc = tour c ++ acc) →
          cs.foldr (fun c acc => tourAux c (r :: acc)) acc =
            cs.flatMap (fun c => tour c ++ [r]) ++ acc := by
        intro cs
        induction cs with
        | nil => intro acc _; rfl
        | cons c cs ihl =>
            intro acc h
            have hrest := ihl acc (fun x hx => h x (List.mem_cons_of_mem c hx))
            simp only [List.foldr_cons, List.flatMap_cons]
            rw [h c (by simp) (r :: cs.foldr (fun c acc => tourAux c (r :: acc)) acc),
              hrest]
            simp [List.append_assoc]
      have hnode : tour (.node r cs) =
          r :: cs.flatMap (fun c => tour c ++ [r]) := by
        rw [tour, tourAux, hfold cs [] ih]
        simp
      rw [tourAux, hfold cs acc ih, hnode]
      simp

/-- Characteristic node equation for `tour` (the former definition). -/
theorem tour_node (r : V) (cs : List (Tree V)) :
    tour (.node r cs) = r :: cs.flatMap (fun c => tour c ++ [r]) := by
  have hfold : ∀ (cs : List (Tree V)),
      cs.foldr (fun c acc => tourAux c (r :: acc)) [] =
        cs.flatMap (fun c => tour c ++ [r]) := by
    intro cs
    induction cs with
    | nil => rfl
    | cons c cs ihl =>
        simp only [List.foldr_cons, List.flatMap_cons]
        rw [tourAux_eq, ihl]
        simp [List.append_assoc]
  rw [tour, tourAux, hfold]

theorem tour_length (t : Tree V) : (tour t).length = 2 * size t - 1 := by
  induction t using Tree.children_ind with
  | node r cs ih =>
      have hsum : ∀ cs : List (Tree V),
          (∀ c ∈ cs, (tour c).length = 2 * size c - 1) →
          (cs.flatMap (fun c => tour c ++ [r])).length = 2 * (cs.map size).sum := by
        intro cs
        induction cs with
        | nil => intro _; rfl
        | cons c cs ihl =>
            intro h
            have hc := h c (by simp)
            have hp := size_pos c
            rw [List.flatMap_cons, List.length_append,
              ihl (fun x hx => h x (List.mem_cons_of_mem c hx)),
              List.map_cons, List.sum_cons]
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
      simp only [tour_node, size, List.length_cons]
      rw [hsum cs ih]
      omega

/-- The arc sequence of the Euler tour: consecutive vertex pairs. Each tree edge
occurs once in each direction. -/
def arcTour (t : Tree V) : List (V × V) :=
  let tourList := tour t
  tourList.zip tourList.tail

/-- `arcTour` computed from the single shared tour list. -/
theorem arcTour_eq_zip (t : Tree V) :
    arcTour t = (tour t).zip (tour t).tail :=
  rfl

theorem arcTour_length (t : Tree V) : (arcTour t).length = 2 * (size t - 1) := by
  have h := tour_length t
  have hp := size_pos t
  rw [arcTour_eq_zip, List.length_zip, List.length_tail, h]
  omega

theorem exists_cons_tour (t : Tree V) : ∃ l, tour t = t.root :: l := by
  cases t with
  | node r cs => exact ⟨cs.flatMap (fun c => tour c ++ [r]), by rw [tour_node]; rfl⟩

theorem root_mem_tour (t : Tree V) : t.root ∈ tour t := by
  obtain ⟨l, hl⟩ := exists_cons_tour t
  rw [hl]
  exact List.mem_cons_self

/-- A vertex occurs in the Euler tour exactly when it is a vertex of the tree. -/
theorem mem_tour_iff (t : Tree V) (v : V) : v ∈ tour t ↔ v ∈ vertices t := by
  induction t using Tree.children_ind with
  | node r cs ih =>
      simp only [tour_node, vertices_node, List.mem_cons, List.mem_flatMap, List.mem_append]
      constructor
      · rintro (rfl | ⟨c, hc, hv | hv⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨c, hc, (ih c hc).mp hv⟩
        · cases hv with
          | inl h => exact Or.inl h
          | inr h => exact (List.not_mem_nil h).elim
      · rintro (rfl | ⟨c, hc, hv⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨c, hc, Or.inl ((ih c hc).mpr hv)⟩

/-- Forest validity: every vertex occurs at most once in the tree. Raw
`Tree`s may repeat vertex labels; the dynamic-forest interpretation of
`link` requires `Valid` inputs with disjoint vertex sets. -/
def Valid (t : Tree V) : Prop :=
  (vertices t).Nodup

/-- Validity is exactly duplicate-freeness of the preorder vertex list. -/
theorem valid_iff (t : Tree V) : Valid t ↔ (vertices t).Nodup :=
  Iff.rfl

/-- A single-vertex tree is valid. -/
theorem valid_singleton (r : V) : Valid (.node r []) := by
  rw [Valid, vertices_node]
  simp

/-- Records `t₂` as a new last child subtree of the root of `t₁`. -/
def link : Tree V → Tree V → Tree V
  | .node r cs, t₂ => .node r (cs ++ [t₂])

@[simp] theorem root_link (t₁ t₂ : Tree V) : (link t₁ t₂).root = t₁.root := by
  cases t₁ with
  | node r cs => rfl

theorem size_link (t₁ t₂ : Tree V) : size (link t₁ t₂) = size t₁ + size t₂ := by
  cases t₁ with
  | node r cs =>
      simp only [link, size, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega

theorem vertices_link (t₁ t₂ : Tree V) :
    vertices (link t₁ t₂) = vertices t₁ ++ vertices t₂ := by
  cases t₁ with
  | node r cs => simp [link, vertices_node, List.flatMap_append]

/-- Linking two valid trees with disjoint vertex sets stays valid: the
forest precondition for reading `link` as a dynamic-forest link. -/
theorem valid_link {t₁ t₂ : Tree V} (h₁ : Valid t₁) (h₂ : Valid t₂)
    (hd : List.Disjoint (vertices t₁) (vertices t₂)) :
    Valid (link t₁ t₂) := by
  rw [Valid, vertices_link] at *
  exact List.nodup_append.mpr ⟨h₁, h₂, by
    intro a ha b hb hab
    subst hab
    exact hd ha hb⟩

/-- Without disjointness, `link` need not be valid: linking two singleton
trees with the same root duplicates that vertex. -/
theorem not_valid_link_same_root (r : V) :
    ¬ Valid (link (.node r []) (.node r [])) := by
  rw [Valid, vertices_link, vertices_node]
  simp

/-- The splice of two tours at the root `r` of the first tree: walk the first tour,
then the second tree's tour, then return to `r`. -/
def spliceLink (tour₁ tour₂ : List V) (r : V) : List V :=
  tour₁ ++ tour₂ ++ [r]

/-- The tour of a linked tree is the splice of the two tours: the first tour is a
prefix, and the second tour is inserted whole before the final return to the root. -/
theorem tour_link (t₁ t₂ : Tree V) :
    tour (link t₁ t₂) = tour t₁ ++ (tour t₂ ++ [t₁.root]) := by
  cases t₁ with
  | node r cs => simp [link, tour_node, root, List.flatMap_append]

theorem tour_link_splice (t₁ t₂ : Tree V) :
    tour (link t₁ t₂) = spliceLink (tour t₁) (tour t₂) t₁.root := by
  rw [spliceLink, List.append_assoc]
  exact tour_link t₁ t₂

theorem tour_prefix_link (t₁ t₂ : Tree V) :
    ∃ rest, tour (link t₁ t₂) = tour t₁ ++ rest :=
  ⟨tour t₂ ++ [t₁.root], tour_link t₁ t₂⟩

theorem tour_infix_link (t₁ t₂ : Tree V) :
    ∃ pre post, tour (link t₁ t₂) = pre ++ tour t₂ ++ post :=
  ⟨tour t₁, [t₁.root], by rw [tour_link, ← List.append_assoc]⟩

/-- Removes the last child subtree of the root, returning the remaining tree and the
removed subtree, or `none` when the root has no children. -/
def cutLast : Tree V → Option (Tree V × Tree V)
  | .node r cs => cs.getLast?.map (fun last => (.node r cs.dropLast, last))

theorem cutLast_link (t₁ t₂ : Tree V) : cutLast (link t₁ t₂) = some (t₁, t₂) := by
  cases t₁ with
  | node r cs => simp [link, cutLast]

end Tree

end EulerTourTree

end Cslib.Algorithms.Lean
