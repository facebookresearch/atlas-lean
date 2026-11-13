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

/-- **Rooted ordered tree.** A rooted ordered tree with vertices in a type $V$ consists of a root
vertex in $V$ together with an ordered list of child subtrees, each a rooted ordered tree with
vertices in $V$.

Vertex labels need not be distinct. -/
inductive Tree (V : Type u) where
  | node (root : V) (children : List (Tree V)) : Tree V
deriving Repr

namespace Tree

variable {V : Type u}

/-- **Induction principle for rooted trees.** Let $P$ be a property of trees. Suppose that for
every vertex $r$ and all trees $c_1, \dots, c_k$ (with $k \ge 0$), if $P$ holds for each $c_i$, then
$P$ holds for the tree with root $r$ and child subtrees $c_1, \dots, c_k$. Then $P$ holds for every
tree. -/
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

/-- **Root of a rooted tree.** The root of the tree with root vertex $r$ and child subtrees
$c_1, \dots, c_k$ is the vertex $r$. -/
def root : Tree V → V
  | .node r _ => r

/-- **Children of a rooted tree.** The children of a tree are the child subtrees of its root, as a
list in their given order. -/
def children : Tree V → List (Tree V)
  | .node _ cs => cs

@[simp] theorem root_node (r : V) (cs : List (Tree V)) : root (.node r cs) = r :=
  rfl

@[simp] theorem children_node (r : V) (cs : List (Tree V)) :
    children (.node r cs) = cs :=
  rfl

/-- **Size of a rooted tree.** The size of a tree is its number of nodes, counting repeated vertex
labels with multiplicity: the tree with root $r$ and child subtrees $c_1, \dots, c_k$ has size
$1 + \sum_{i=1}^{k} \operatorname{size}(c_i)$. -/
def size : Tree V → Nat
  | .node _ cs => 1 + (cs.map size).sum

theorem size_pos (t : Tree V) : 0 < size t := by
  cases t with
  | node r cs => simp only [size]; omega

/-- **Accumulator preorder traversal.** For a rooted ordered tree $t$ with root $r$ and child
subtrees $c_1, \dots, c_k$ (in order) and a list $a$, the accumulator traversal $T(t, a)$ is
the list whose first entry is $r$ and whose remaining entries are
$T(c_1, T(c_2, \dots, T(c_k, a) \dots))$; when $k = 0$ the remaining entries are $a$.

The list $T(t, a)$ equals the preorder vertex list of $t$ followed by $a$, so the preorder list
is computed in linear time rather than by repeatedly appending child lists. -/
def verticesAux : Tree V → List V → List V
  | .node r cs, acc => r :: cs.foldr (fun c acc => verticesAux c acc) acc

/-- **Preorder vertex list of a rooted tree.** The preorder vertex list of a rooted ordered tree
$t$ is the accumulator preorder traversal of $t$ started from the empty list.

Equivalently, it is the root of $t$ followed by the preorder vertex lists of its child subtrees
in order; repeated vertex labels appear with multiplicity. -/
def vertices (t : Tree V) : List V :=
  verticesAux t []

/-- **Accumulator preorder traversal is append.** For every rooted ordered tree $t$ and every
list $a$, the accumulator preorder traversal of $t$ started from $a$ equals the preorder vertex
list of $t$ followed by $a$. -/
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

/-- **Preorder vertex list of a node.** For a vertex $r$ and rooted ordered trees
$c_1, \dots, c_k$, the preorder vertex list of the tree with root $r$ and child subtrees
$c_1, \dots, c_k$ (in order) is $r$ followed by the concatenation of the preorder vertex lists
of $c_1, \dots, c_k$, in this order. -/
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

/-- **Euler tour with an accumulator.** Let $t$ be a tree with root $r$ and child subtrees
$c_1, \dots, c_k$ in order, and let $a$ be a list of vertices. For a list $L$ of vertices, write
$r \cdot L$ for the list $L$ with $r$ put in front. The Euler tour of $t$ with accumulator $a$,
written $T(t, a)$, is $r \cdot L_1$, where $L_{k+1} = a$ and $L_i = T(c_i, r \cdot L_{i+1})$ for
$i = k, \dots, 1$.

It equals the Euler tour of $t$ followed by $a$, and computes the Euler tour without repeatedly
concatenating the tours of the child subtrees. -/
def tourAux : Tree V → List V → List V
  | .node r cs, acc =>
      r :: cs.foldr (fun c acc => tourAux c (r :: acc)) acc

/-- **Euler tour.** The Euler tour of a tree $t$ with root $r$ and child subtrees
$c_1, \dots, c_k$ in order is the list of vertices consisting of $r$, followed, for each
$i = 1, \dots, k$ in turn, by the Euler tour of $c_i$ and then $r$. It is the vertex sequence of
the depth-first walk that returns to the parent vertex after each child subtree. -/
def tour (t : Tree V) : List V :=
  tourAux t []

/-- **Accumulator lemma for the Euler tour.** For every tree $t$ and every list $a$ of vertices,
the Euler tour of $t$ with accumulator $a$ equals the Euler tour of $t$ followed by $a$. -/
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

/-- **Recursive formula for the Euler tour.** For a vertex $r$ and a list of trees
$c_1, \dots, c_k$, the Euler tour of the tree with root $r$ and child subtrees $c_1, \dots, c_k$
in order is $r$, followed, for each $i = 1, \dots, k$ in turn, by the Euler tour of $c_i$ and
then $r$. -/
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

/-- **Arc sequence of the Euler tour.** The arc sequence of a tree $t$ is the list of consecutive
pairs of its Euler tour: if the Euler tour of $t$ is $v_0, v_1, \dots, v_k$, then the arc sequence
of $t$ is $(v_0, v_1), (v_1, v_2), \dots, (v_{k-1}, v_k)$.

Each tree edge occurs once in each direction. -/
def arcTour (t : Tree V) : List (V × V) :=
  let tourList := tour t
  tourList.zip tourList.tail

/-- **Arc sequence as the zipped Euler tour.** For every tree $t$, the arc sequence of $t$ is
the Euler tour of $t$ zipped with its own tail: if the Euler tour of $t$ is $v_0, v_1, \dots, v_k$,
then the arc sequence of $t$ is $(v_0, v_1), (v_1, v_2), \dots, (v_{k-1}, v_k)$. -/
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

/-- **The Euler tour visits exactly the vertices of the tree.** For every tree $t$ and every $v$,
$v$ occurs in the Euler tour of $t$ if and only if $v$ is a vertex of $t$. -/
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

/-- **Valid Euler-tour tree.** A rooted ordered tree is valid when its list of vertices in
preorder has no duplicates, that is, every vertex label occurs at most once in the tree.

Raw trees may repeat vertex labels; reading the linking of two trees as a link in a dynamic
forest requires valid trees with disjoint vertex sets. -/
def Valid (t : Tree V) : Prop :=
  (vertices t).Nodup

/-- **Valid trees have distinct vertices.** A tree $t$ is valid if and only if its list of
vertices in preorder has no repeated entries. -/
theorem valid_iff (t : Tree V) : Valid t ↔ (vertices t).Nodup :=
  Iff.rfl

/-- **A single-vertex tree is valid.** For every vertex $r$, the tree with root $r$ and no child
subtrees is valid. -/
theorem valid_singleton (r : V) : Valid (.node r []) := by
  rw [Valid, vertices_node]
  simp

/-- **Linking two rooted trees.** Let $t_1$ be a tree with root $r$ and child subtrees
$c_1, \dots, c_k$, and let $t_2$ be a tree. The link of $t_1$ and $t_2$ is the tree with root $r$
and child subtrees $c_1, \dots, c_k, t_2$, so $t_2$ becomes the new last child subtree of the root
of $t_1$. -/
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

/-- **Linking valid trees with disjoint vertices gives a valid tree.** Let $t_1$ and $t_2$ be
valid trees such that no vertex of $t_1$ is a vertex of $t_2$. Then the link of $t_1$ and $t_2$,
that is, $t_1$ with $t_2$ added as the last child subtree of its root, is valid.

This is the forest precondition for reading the link as a link of two trees in a dynamic
forest. -/
theorem valid_link {t₁ t₂ : Tree V} (h₁ : Valid t₁) (h₂ : Valid t₂)
    (hd : List.Disjoint (vertices t₁) (vertices t₂)) :
    Valid (link t₁ t₂) := by
  rw [Valid, vertices_link] at *
  exact List.nodup_append.mpr ⟨h₁, h₂, by
    intro a ha b hb hab
    subst hab
    exact hd ha hb⟩

/-- **Linking two copies of a single vertex is not valid.** For every vertex $r$, the link of the
single-vertex tree with root $r$ and another single-vertex tree with root $r$ is not valid, since
the vertex $r$ occurs twice in it. Hence the link of two valid trees need not be valid when their
vertex sets are not disjoint. -/
theorem not_valid_link_same_root (r : V) :
    ¬ Valid (link (.node r []) (.node r [])) := by
  rw [Valid, vertices_link, vertices_node]
  simp

/-- **Splicing two Euler tours.** For lists $\tau_1$ and $\tau_2$ of vertices and a vertex $r$,
the splice of $\tau_1$ and $\tau_2$ at $r$ is the list consisting of the entries of $\tau_1$,
followed by the entries of $\tau_2$, followed by $r$.

It is used with $\tau_1$ and $\tau_2$ the Euler tours of two trees and $r$ the root of the first
tree: walk the first tour, then the second tour, then return to $r$. -/
def spliceLink (tour₁ tour₂ : List V) (r : V) : List V :=
  tour₁ ++ tour₂ ++ [r]

/-- **Euler tour of a linked tree.** For trees $t_1$ and $t_2$, let $t$ be the link of $t_1$ and
$t_2$, that is, $t_1$ with $t_2$ added as the last child subtree of its root. The Euler tour of
$t$ is the Euler tour of $t_1$, followed by the Euler tour of $t_2$, followed by the root of
$t_1$. -/
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

/-- **Cutting the last child subtree.** Let $t$ be a tree with root $r$ and child subtrees
$c_1, \dots, c_k$. Cutting the last child subtree of $t$ gives no result when $k = 0$; when
$k \ge 1$ it gives the pair consisting of the tree with root $r$ and child subtrees
$c_1, \dots, c_{k-1}$, together with the removed subtree $c_k$. -/
def cutLast : Tree V → Option (Tree V × Tree V)
  | .node r cs => cs.getLast?.map (fun last => (.node r cs.dropLast, last))

theorem cutLast_link (t₁ t₂ : Tree V) : cutLast (link t₁ t₂) = some (t₁, t₂) := by
  cases t₁ with
  | node r cs => simp [link, cutLast]

end Tree

end EulerTourTree

end Cslib.Algorithms.Lean
