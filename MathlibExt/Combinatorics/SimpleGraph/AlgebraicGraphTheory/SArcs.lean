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

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 11, Combinatorics 12, Combinatorics 13, Combinatorics 14

/-!
# SArcs

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 11, Combinatorics 12, Combinatorics 13, Combinatorics 14

## References

* AGT Section 4.1 (for `SimpleGraph.SArc`, `SimpleGraph.IsSArcTransitive`,
  `SimpleGraph.IsSArcRegular`)
* Algebraic Graph Theory, Godsil & Royle (2001), Section 4.2 Arc Graphs, page 61. (for
  `SimpleGraph.arcDigraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 11: $s$-arc

/-- **$s$-arc.** Let $X$ be a finite graph and $s$ a natural number. An *$s$-arc* in $X$ is a
sequence $(v_0, \dots, v_s)$ of vertices of $X$ such that $v_{i-1}$ and $v_i$ are adjacent for
$1 \le i \le s$, and $v_{i-1} \ne v_{i+1}$ for $0 < i < s$.
-/
structure _root_.SimpleGraph.SArc {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ) where
  vertices : Fin (s + 1) → V
  adj : ∀ i : Fin s, G.Adj (vertices i.castSucc) (vertices i.succ)
  no_backtrack : ∀ (i : Fin (s + 1)) (h : (i : ℕ) + 2 ≤ s),
    vertices i ≠ vertices ⟨(i : ℕ) + 2, by omega⟩

-- Combinatorics 12: $s$-arc transitive

/-- **$s$-arc transitive graph.** A finite graph $G$ is $s$-arc transitive if its automorphism
group acts transitively on its $s$-arcs: for any two $s$-arcs $(u_0, \dots, u_s)$ and
$(v_0, \dots, v_s)$ of $G$ there is an automorphism $\varphi$ of $G$ with $\varphi(u_i) = v_i$
for every $i \le s$. -/
def SimpleGraph.IsSArcTransitive {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∀ p q : G.SArc s, ∃ φ : G ≃g G, ∀ i, φ (p.vertices i) = q.vertices i

-- Combinatorics 13: $s$-arc regular

/-- **$s$-arc regular graph.** A finite graph $G$ is $s$-arc regular if it has at least one
$s$-arc and, for any two $s$-arcs $(u_0, \dots, u_s)$ and $(v_0, \dots, v_s)$ of $G$, there is
exactly one automorphism $\varphi$ of $G$ with $\varphi(u_i) = v_i$ for every $i \le s$.
-/
def SimpleGraph.IsSArcRegular {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ) : Prop :=
  Nonempty (G.SArc s) ∧
  ∀ p q : G.SArc s, ∃! φ : G ≃g G, ∀ i : Fin (s + 1), φ (p.vertices i) = q.vertices i

-- Combinatorics 14: $X^{(s)}$

def _root_.SimpleGraph.SArc.tail {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (a : G.SArc (s + 1)) : G.SArc s where
  vertices i := a.vertices ⟨i.val, Nat.lt_of_lt_of_le i.is_lt (Nat.le_succ _)⟩
  adj i := a.adj ⟨i.val, by omega⟩
  no_backtrack i hi := a.no_backtrack ⟨i.val, Nat.lt_of_lt_of_le i.is_lt (Nat.le_succ _)⟩
    (Nat.le_succ_of_le hi)

def _root_.SimpleGraph.SArc.head {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (a : G.SArc (s + 1)) : G.SArc s where
  vertices i := a.vertices ⟨i.val + 1, Nat.succ_lt_succ i.is_lt⟩
  adj i := a.adj ⟨i.val + 1, by omega⟩
  no_backtrack i hi := a.no_backtrack ⟨i.val + 1, Nat.succ_lt_succ i.is_lt⟩
    (Nat.succ_le_succ hi)

def _root_.SimpleGraph.SArc.follows {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (a b : G.SArc s) : Prop :=
  ∃ c : G.SArc (s + 1), c.head = a ∧ c.tail = b

/-- **$s$-arc digraph.** Let $X$ be a finite graph and $s$ a natural number. For an
$(s+1)$-arc $\gamma = (x_0, \dots, x_{s+1})$ of $X$, its *head* is the $s$-arc
$(x_1, \dots, x_{s+1})$ and its *tail* is the $s$-arc $(x_0, \dots, x_s)$. If $\alpha$ and
$\beta$ are $s$-arcs of $X$, then $\beta$ *follows* $\alpha$ if there is an $(s+1)$-arc of $X$
whose tail is $\alpha$ and whose head is $\beta$. The *$s$-arc digraph* $X^{(s)}$ is the directed
graph whose vertices are the $s$-arcs of $X$, with an arc from $\alpha$ to $\beta$ if and only if
$\beta$ follows $\alpha$.
-/
def _root_.SimpleGraph.arcDigraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : ℕ) : Digraph (G.SArc s) where
  Adj a b := b.follows a

end MetaMathlibExt

end
