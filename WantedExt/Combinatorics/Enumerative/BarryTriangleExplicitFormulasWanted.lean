/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Matrix.Mul
public import MathlibExt.Combinatorics.Enumerative.BarryTriangleExplicitFormulas

/-!
# Matrix formula for Barry's triangle

Khaidarov gives a matrix power formula for the Stirling-like triangle OEIS A080416.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Matrix power formula for Barry's triangle.** Let $s$ be Barry's triangle recurrence and let
$2 \le a \le n$. Let $M$ be the $(a - 1) \times (a - 1)$ lower bidiagonal matrix of natural
numbers with diagonal entries $M_{i,i} = i(a - i)$ for $i = 1, \dots, a - 1$, entries
$M_{i+1,i} = 1$ just below the diagonal, and all other entries $0$. Then $s(0, n, a)$ is the
bottom-left entry $(M^{n-2})_{a-1,1}$ of the power $M^{n-2}$.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, main result announced in the abstract, equation (7)
(`jis-2026-26.2.8-abstract-main`). -/
public theorem_wanted barryTriangleAux_eq_matrix_pow (n a : ℕ) (ha : 2 ≤ a) (han : a ≤ n) :
    barryTriangleAux 0 n a =
      ((Matrix.of fun i j : Fin (a - 1) =>
          if i = j then ((i : ℕ) + 1) * (a - ((i : ℕ) + 1))
          else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) ^ (n - 2))
        ⟨a - 2, by omega⟩ ⟨0, by omega⟩

end

end MetaMathlibExt
