/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
OPG-655 (Snevily's conjecture): let `G` be an abelian group of odd order
and `A B ⊆ G` with `|A| = |B| = k`. Then `A` and `B` can be ordered so
that the `k` sums `aᵢ + bᵢ` are pairwise distinct.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace MathlibExt.Combinatorics.SnevilyTransversalWanted

/-! Source record `OPG-655`. -/

/-- **Snevily's conjecture.** The statement that for every finite abelian group $G$ of odd order,
written additively, and all subsets $A, B \subseteq G$ with $|A| = |B|$, there is a bijection
$f \colon A \to B$ such that the sums $a + f(a)$, for $a \in A$, are pairwise distinct.

Equivalently, $A$ and $B$ can be enumerated as $a_1, \dots, a_k$ and $b_1, \dots, b_k$ so that
the sums $a_i + b_i$ are pairwise distinct: given such enumerations, send $a_i$ to $b_i$;
conversely, enumerate $A$ and transport the enumeration along $f$.

Source: OPG-655. -/
def conjecture : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G],
    Odd (Fintype.card G) →
      ∀ A B : Finset G, A.card = B.card →
        ∃ f : ↥A → ↥B, Function.Bijective f ∧
          ∀ a₁ a₂ : ↥A,
            (a₁ : G) + (f a₁ : G) = (a₂ : G) + (f a₂ : G) → a₁ = a₂

/--
**Snevily's conjecture is true.** Let $G$ be a finite abelian group of odd order, written
additively, and let $A, B \subseteq G$ be subsets with $|A| = |B|$. Then there is a bijection
$f \colon A \to B$ such that the sums $a + f(a)$, for $a \in A$, are pairwise distinct.

Source:
Boris Arsovski, A proof of Snevily's conjecture, Israel J. Math. 182 (2011), 505-508. Moved from
`OpenConjectures/Combinatorics/SnevilyTransversal`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.SnevilyTransversalWanted
