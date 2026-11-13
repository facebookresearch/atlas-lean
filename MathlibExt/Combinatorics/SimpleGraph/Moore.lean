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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 19

/-!
# Moore

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 19

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 5 Generalized Polygons and Moore Graphs,
  page 77. (for `IsMooreGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 19: Is Moore graph

/-- **Moore graph.** Let $G$ be a simple graph on a finite vertex set and let $d$ be a natural
number. Then $G$ is a Moore graph of diameter $d$ when $G$ has diameter $d$ and girth $2d + 1$. -/
def IsMooreGraph {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  G.diam = d ∧ G.girth = 2 * d + 1

end MetaMathlibExt

end
