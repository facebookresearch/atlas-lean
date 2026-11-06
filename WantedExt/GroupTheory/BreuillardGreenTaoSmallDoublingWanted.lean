/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Additive.DoublingConst
public import Mathlib.Data.Real.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.SetTheory.Cardinal.Finite

namespace MetaMathlibExt

@[expose] public section

open scoped Combinatorics.Additive Pointwise

/-- **Breuillard–Green–Tao theorem (small doubling form).** For every real number $K$ there is a
natural number $C > 0$ with the following property. Let $G$ be a group and let $A$ be a nonempty
finite subset of $G$ such that the product set $A A = \{ab : a, b \in A\}$ satisfies
$|A A| \le K |A|$. Then there are a subgroup $N$ of $G$, a normal subgroup $D$ of $N$ and a finite
subset $S$ of $N / D$ with at most $C$ elements such that $N / D$ is nilpotent of class at most
$C$ (its upper central series reaches $N / D$ at step $C$), $S$ generates $N / D$, every element
of $D$ is a product of four elements of $A A^{-1} = \{ab^{-1} : a, b \in A\}$, and there are
$a_1, \dots, a_C \in G$ such that $A$ is contained in the union of the left cosets
$a_1 N, \dots, a_C N$ of $N$.

Sources: S. Machado, *Topics in Geometric Group Theory* lecture notes,
<https://sites.google.com/view/simonmachado/teaching>, Theorem 1.8;
original B. Breuillard, B. Green, T. Tao, *The structure of approximate
groups*, Publ. Math. IHÉS 116 (2012). -/
theorem_wanted breuillard_green_tao_small_doubling {K : ℝ} :
    ∃ C : ℕ, 0 < C ∧
      ∀ {G : Type*} [Group G] [DecidableEq G] (A : Finset G)
        (_hA_nonempty : A.Nonempty) (_hA : ((σₘ[A] : ℚ≥0) : ℝ) ≤ K),
        ∃ (N : Subgroup G) (D : Subgroup N) (_hD : D.Normal)
          (S : Finset (N ⧸ D)),
          Subgroup.upperCentralSeries (N⧸ D) C = ⊤ ∧
            S.card ≤ C ∧
            Subgroup.closure (↑S : Set (N ⧸ D)) = ⊤ ∧
            ((↑) '' (D : Set N) : Set G) ⊆ ((A / A) ^ 4 : Set G) ∧
            ∃ a : Fin C → G, (A : Set G) ⊆ ⋃ i, a i • (N : Set G)

end

end MetaMathlibExt
