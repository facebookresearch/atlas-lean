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

/-- The Andrásfai graph is the Cayley graph X(G,C) where G = ℤ₃ₖ₊₂ for some non-negative integer k
and C is the subset of G consisting of the elements congruent to 1  (mod 3).
-/
def andrasfaiGraph (k : ℕ) : SimpleGraph (ZMod (3 * k + 2)) :=
  SimpleGraph.addCayley (andrasfaiConnectionSet k)

end MetaMathlibExt

end
