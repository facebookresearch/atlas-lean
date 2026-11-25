/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.NumberTheory.Farey

namespace MetaMathlibExt

open scoped BigOperators Asymptotics

@[expose] public section

/-- **Franel–Landau theorem.** For a natural number $N$, let
$F_N(0) < F_N(1) < \dots < F_N(L_N - 1)$ be the terms of the Farey sequence of order $N$, and for
$k < L_N$ let $\delta_{N,k} = F_N(k) - k/(L_N - 1)$. The Riemann hypothesis holds if and only if
for every real $\varepsilon > 0$,
$\sum_{k=0}^{L_N - 1} \delta_{N,k}^2 = O(N^{-1+\varepsilon})$ as $N \to \infty$.

Source: https://en.wikipedia.org/wiki/Farey_sequence. -/
theorem_wanted franel_landau :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ => ∑ k : Fin (Farey.fareySeq N).length,
          ((((Farey.fareySeq N).get k : ℚ) : ℝ) -
            ((k : ℕ) : ℝ) / (((Farey.fareySeq N).length - 1 : ℕ) : ℝ)) ^ 2)
            =O[Filter.atTop]
        (fun N : ℕ => (N : ℝ) ^ (-1 + ε))

end

end MetaMathlibExt
