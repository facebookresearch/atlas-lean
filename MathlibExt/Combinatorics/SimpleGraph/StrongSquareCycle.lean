/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Square

/-!
# Rooted Hamiltonian cycles in graph squares
-/

@[expose] public section

namespace SimpleGraph

/-- **Strong square cycle at a vertex.** Let $G$ be a graph on a finite vertex set $V$ and let
$x \in V$. Then $G$ has a strong square cycle at $x$ if the square $G^2$ of $G$ has a Hamiltonian
cycle that starts and ends at $x$ and whose two edges at $x$, its first and its last edge, are
edges of $G$. -/
public def HasStrongSquareCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) : Prop :=
  ∃ p : G.square.Walk x x, p.IsHamiltonianCycle ∧
    G.Adj x p.snd ∧ G.Adj p.penultimate x

/-- **Characterization of strong square cycles.** Let $G$ be a graph on a finite vertex set $V$
and let $x \in V$. Then $G$ has a strong square cycle at $x$ if and only if the square $G^2$ of
$G$ has a Hamiltonian cycle $p$ that starts and ends at $x$ such that $x$ is adjacent in $G$ to
the second vertex of $p$ and the second-to-last vertex of $p$ is adjacent in $G$ to $x$. -/
public theorem hasStrongSquareCycle_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) :
    G.HasStrongSquareCycle x ↔
      ∃ p : G.square.Walk x x, p.IsHamiltonianCycle ∧
        G.Adj x p.snd ∧ G.Adj p.penultimate x :=
  Iff.rfl

end SimpleGraph
