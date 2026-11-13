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
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 26

/-!
# Andrasfai

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 26

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 6.10 The Andrásfai Graphs, page 118. (for
  `andrasfaiGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 26: Andrásfai graph

def andrasfaiConnectionSet (k : ℕ) : Finset (ZMod (3 * k + 2)) :=
  {x | x.val % 3 = 1}

/-- **Andrásfai graph.** For a natural number $k$, the Andrásfai graph is the Cayley graph of
the cyclic group $\mathbb{Z}/(3k+2)\mathbb{Z}$ whose connection set $C$ consists of the residues
whose representative in $\{0, 1, \dots, 3k+1\}$ is congruent to $1$ modulo $3$: two distinct
residues $x$ and $y$ are adjacent when $y - x \in C$ or $x - y \in C$.
-/
def andrasfaiGraph (k : ℕ) : SimpleGraph (ZMod (3 * k + 2)) :=
  SimpleGraph.addCayley (andrasfaiConnectionSet k)

end MetaMathlibExt

end
