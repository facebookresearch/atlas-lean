/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Additive.ApproximateSubgroup
public import Mathlib.GroupTheory.Nilpotent

namespace MetaMathlibExt

@[expose] public section

open scoped Pointwise

/-- **Breuillard–Green–Tao structure theorem for approximate subgroups.** For every real number
$K$ there is a natural number $C \ge 1$ with the following property. Let $G$ be a group and let
$A \subseteq G$ be a $K$-approximate subgroup, that is, $1 \in A$, $A^{-1} = A$, and $A^2$ is
covered by at most $K$ left translates of $A$. Then there are a subgroup $H$ of $G$, a normal
subgroup $N$ of $H$, a finite set $F \subseteq G$ and a finite set $S \subseteq H/N$ such that
$H/N$ is nilpotent of class at most $C$ (the $C$-th term of its upper central series is all of
$H/N$), $S$ has at most $C$ elements and generates $H/N$, $N$ is contained in the $C$-fold
product set $(AA^{-1})^C$, $F$ has at most $C$ elements, and $A \subseteq FH$.

Sources: S. Machado, *Topics in Geometric Group Theory* lecture notes,
<https://sites.google.com/view/simonmachado/teaching>, Theorem 4.4;
original B. Breuillard, B. Green, T. Tao, *The structure of approximate
groups*, Publ. Math. IHÉS 116 (2012). -/
theorem_wanted breuillard_green_tao_approximate_subgroup {K : ℝ} :
    ∃ C : ℕ, 0 < C ∧
      ∀ {G : Type*} [Group G] [DecidableEq G] (A : Set G)
        (_hA : IsApproximateSubgroup K A),
        ∃ (H : Subgroup G) (N : Subgroup H) (_hD : N.Normal) (F : Finset G)
          (S : Finset (H ⧸ N)),
        Subgroup.upperCentralSeries (H⧸ N) C = ⊤ ∧
          S.card ≤ C ∧
          Subgroup.closure (↑S : Set (H ⧸ N)) = ⊤ ∧
          ((↑) '' (N : Set H) : Set G) ⊆ ((A / A) ^ C) ∧
          F.card ≤ C ∧
          A ⊆ (F : Set G) * (H : Set G)

end

end MetaMathlibExt
