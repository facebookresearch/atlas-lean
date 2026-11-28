/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dichromatic number

Orientation and dichromatic-colouring infrastructure for simple graphs.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Fin.Basic

@[expose] public section


namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- **Orientations of a graph.** Let $G$ be a simple graph on a vertex set $V$. A binary relation
$D$ on $V$ is an orientation of $G$ if $D(u, v)$ holds only when $u$ and $v$ are adjacent in $G$,
and for every pair of adjacent vertices $u$ and $v$ exactly one of $D(u, v)$ and $D(v, u)$
holds. -/
def IsOrientation (D : V → V → Prop) : Prop :=
  (∀ u v, D u v → G.Adj u v) ∧
  ∀ u v, G.Adj u v → (D u v ∧ ¬ D v u) ∨ (D v u ∧ ¬ D u v)

/-- **Closed directed walks.** Let $D$ be a binary relation on a set $V$, viewed as a digraph,
let $n$ be a natural number, and let $f_0, f_1, \dots, f_{n+1}$ be elements of $V$. The sequence
$(f_0, \dots, f_{n+1})$ is a closed directed walk of length $n + 1$ in $D$ if $f_0 = f_{n+1}$ and
$D(f_i, f_{i+1})$ holds for every $i$ with $0 \le i \le n$.

Vertices may repeat, so this is a closed walk of positive length rather than a directed cycle in
the strict sense. -/
def IsDirectedCycle (D : V → V → Prop) (n : ℕ)
    (f : Fin (n + 2) → V) : Prop :=
  f 0 = f (Fin.last (n + 1)) ∧ ∀ i : Fin (n + 1), D (f i.castSucc) (f i.succ)

/-- **Dichromatically $k$-colourable graphs.** Let $G$ be a simple graph on a vertex set $V$ and
let $k$ be a natural number. Then $G$ is dichromatically $k$-colourable if for every orientation
$D$ of $G$ there is a map $c \colon V \to \{0, \dots, k - 1\}$, not required to be a proper
colouring, such that no closed directed walk of positive length in $D$ has all of its vertices of
the same colour under $c$.

Since every closed directed walk of positive length contains a directed cycle, this is the same as
asking for a colouring with no monochromatic directed cycle. -/
def DichromaticColorable (k : ℕ) : Prop :=
  ∀ D : V → V → Prop, G.IsOrientation D →
    ∃ c : V → Fin k, ∀ (n : ℕ) (f : Fin (n + 2) → V),
      IsDirectedCycle D n f → ¬ ∃ col, ∀ i, c (f i) = col

/-- **Dichromatic number.** The dichromatic number of a simple graph $G$ is the least natural
number $k$ such that $G$ is dichromatically $k$-colourable, taken in $\mathbb{N} \cup \{\infty\}$;
it is $\infty$ if $G$ is dichromatically $k$-colourable for no natural number $k$. -/
noncomputable def dichromaticNumber : ℕ∞ :=
  ⨅ n ∈ Set.ofPred (G.DichromaticColorable), (n : ℕ∞)

/-- **The dichromatic number as a least natural number.** Let $G$ be a simple graph. If $G$ is
dichromatically $n$-colourable for some natural number $n$, then the dichromatic number of $G$
equals the least natural number $k$ such that $G$ is dichromatically $k$-colourable. -/
theorem DichromaticColorable.dichromaticNumber_eq_sInf {n : ℕ}
    (h : G.DichromaticColorable n) :
    G.dichromaticNumber = sInf {n' : ℕ | G.DichromaticColorable n'} := by
  rw [ENat.natCast_sInf, dichromaticNumber]
  exact ⟨_, h⟩

/-- **The empty orientation of an edgeless graph.** If a simple graph $G$ has no edges, then the
empty relation on its vertex set, the digraph with no arcs, is an orientation of $G$. -/
theorem IsOrientation.of_edgeless (hempty : ∀ u v, ¬ G.Adj u v) :
    G.IsOrientation (fun _ _ => False) := by
  refine ⟨fun u v h => absurd h (by simp), fun u v hadj => ?_⟩
  exact absurd hadj (hempty u v)

/-- **Edgeless graphs are dichromatically $1$-colourable.** If a simple graph $G$ has no edges,
then $G$ is dichromatically $1$-colourable.

No orientation of $G$ has an arc, so there is no closed directed walk of positive length. -/
theorem DichromaticColorable.of_edgeless (hempty : ∀ u v, ¬ G.Adj u v) :
    G.DichromaticColorable 1 := by
  intro D hD
  refine ⟨fun _ => 0, fun n f hdir => ?_⟩
  have i0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  have e : D (f i0.castSucc) (f i0.succ) := hdir.2 i0
  exact absurd (hD.1 _ _ e) (hempty _ _)

end SimpleGraph
