/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Book numbers of finite graphs

The book number of a graph is the maximum, over adjacent vertex pairs, of the
number of common neighbors (triangles sharing that edge). This is the
canonical invariant consumed by the book-triangle and Erdős Problem 80
entries.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Book number.** Let $G$ be a finite simple graph. The book number of $G$ is the maximum,
over ordered pairs $(u, v)$ of adjacent vertices, of the number of common neighbors of $u$ and
$v$ (the number of triangles containing the edge $uv$); it is $0$ if $G$ has no edges. -/
noncomputable def bookNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.sup Finset.univ fun p : V × V =>
    if G.Adj p.1 p.2 then
      (Finset.univ.filter fun w => G.Adj p.1 w ∧ G.Adj p.2 w).card
    else 0

/-- **Common neighbors of an edge are bounded by the book number.** Let $G$ be a finite simple
graph. If $u$ and $v$ are adjacent vertices of $G$, then the number of common neighbors of $u$
and $v$ is at most the book number of $G$. -/
theorem le_bookNumber {u v : V} (h : G.Adj u v) :
    (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card ≤ G.bookNumber := by
  unfold bookNumber
  have hle := Finset.le_sup (s := (Finset.univ : Finset (V × V)))
    (f := fun p : V × V =>
      if G.Adj p.1 p.2 then
        (Finset.univ.filter fun w => G.Adj p.1 w ∧ G.Adj p.2 w).card
      else 0)
    (Finset.mem_univ (u, v))
  simpa [h] using hle

/-- **Bounding the book number.** Let $G$ be a finite simple graph and $b$ a natural number. If
every pair of adjacent vertices $u$, $v$ of $G$ has at most $b$ common neighbors, then the book
number of $G$ is at most $b$. -/
theorem bookNumber_le (b : ℕ)
    (h : ∀ u v : V, G.Adj u v →
      (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card ≤ b) :
    G.bookNumber ≤ b := by
  unfold bookNumber
  apply Finset.sup_le
  rintro ⟨u, v⟩ -
  by_cases hadj : G.Adj u v
  · simpa [hadj] using h u v hadj
  · simp [hadj]

end SimpleGraph

end
