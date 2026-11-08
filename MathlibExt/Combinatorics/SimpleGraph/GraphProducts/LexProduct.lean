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

/-- Given graphs $X,Y$, the \emph{lexicographic product} $X[Y] of $X$ and $Y$ has as its vertices
the set $V(X) \times V(Y)$ and an edge exists between $(x_1,y_1),(x_2,y_2) \in V(X) \times V(Y)$
whenever $x_1 \sim_X x_2$ or $x_1 = x_2$ and $y_1 \sim_Y y_2$. (here $u \sim_G v$ indicates that $u$
and $v$ are adjacent in $G$).
-/
def _root_.SimpleGraph.lexProduct {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V × W) :=
  SimpleGraph.fromRel fun (p q : V × W) => G.Adj p.1 q.1 ∨ p.1 = q.1 ∧ H.Adj p.2 q.2

end MetaMathlibExt

end
