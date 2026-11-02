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
public import Mathlib.Tactic.FinCases

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 3

/-!
# LexProduct

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 3

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 1.8 Notes, page 17 (Exercise 26). (for
  `SimpleGraph.lexProduct`)
-/

namespace MetaMathlibExt

-- Combinatorics 3: Lexicographic product

/-- **Lexicographic product of graphs.** Given simple graphs $X$ and $Y$, the *lexicographic
product* $X[Y]$ of $X$ and $Y$ is the simple graph with vertex set $V(X) \times V(Y)$ in which
two vertices $(x_1, y_1)$ and $(x_2, y_2)$ are adjacent exactly when $x_1$ and $x_2$ are
adjacent in $X$, or $x_1 = x_2$ and $y_1$ and $y_2$ are adjacent in $Y$.
-/
def _root_.SimpleGraph.lexProduct {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V × W) :=
  SimpleGraph.fromRel fun (p q : V × W) => G.Adj p.1 q.1 ∨ p.1 = q.1 ∧ H.Adj p.2 q.2

end MetaMathlibExt

end
