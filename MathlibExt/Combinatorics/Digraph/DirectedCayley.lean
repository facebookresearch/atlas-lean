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

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 58

/-!
# DirectedCayley

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 58

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 3.4 Vertex Connectivity, page 34. (for
  `directedCayleyGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 58: Cayley arc/Cayley digraph

def cayleyArc {G : Type*} [Mul G] (C : Set G) (x y : G) : Prop :=
  ∃ c ∈ C, x * c = y

/-- **Cayley digraph.** Let $G$ be a set with a binary operation written as multiplication,
and let $C \subseteq G$. The *Cayley digraph* $X(G, C)$ is the directed graph whose vertices
are the elements of $G$, with an arc $u \to v$ exactly when $v = uc$ for some $c \in C$.

Usually $G$ is a group and $C$ does not contain the identity, so that $X(G, C)$ has no loops;
neither condition is imposed here.
-/
def directedCayleyGraph {G : Type*} [Mul G] (S : Set G) : Digraph G where
  Adj := cayleyArc S

end MetaMathlibExt

end
