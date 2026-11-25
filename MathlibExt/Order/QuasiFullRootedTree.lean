/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Arity of quasi-full rooted trees

A finite partial order $P$ that is a rooted tree is quasi-full $t$-ary when every $x \in P$ is
covered by exactly $\min(|U_x| - 1, t)$ elements, where $U_x = \{y \in P : x \le y\}$. The main
result, `MetaMathlibExt.quasiFullTree_arity`, concerns such a tree with $n \ge 3$ elements: if it
is quasi-full $(n - 1)$-ary, it is quasi-full $t$-ary for every $t \ge n$, and if it is
quasi-full $t$-ary for some $t \le n - 2$, it is quasi-full $t'$-ary for no $t' \ge n$.

Both parts follow from two counts: every up-set $U_x$ has at most $n$ elements, so
$\min(|U_x| - 1, t) = |U_x| - 1$ once $t \ge n - 1$, and the up-set of the root is all of $P$.
The hypothesis that the elements below each $x$ form a chain is kept for fidelity with the source
but is not needed.
-/

namespace MetaMathlibExt

-- The chain hypothesis `hchain` is part of the source's notion of a rooted tree; the proof does
-- not need it.
set_option linter.unusedVariables false in
/-- **Arity of quasi-full rooted trees.** Let $P$ be a finite partial order with $n \ge 3$
elements that is a rooted tree: $P$ has a least element and, for every $x \in P$, the elements
below $x$ form a chain. For a natural number $t$, call $P$ quasi-full $t$-ary when every $x \in P$
is covered by exactly $\min(|U_x| - 1, t)$ elements of $P$, where $U_x = \{y \in P : x \le y\}$.
Then (i) if $P$ is quasi-full $(n - 1)$-ary, it is quasi-full $t$-ary for every $t \ge n$; and
(ii) if $P$ is quasi-full $t$-ary for some $t \le n - 2$, it is not quasi-full $t'$-ary for any
$t' \ge n$.

The source states this for poset matrices representing quasi-full $t$-ary rooted trees; both
parts depend only on the represented poset.

Source: Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and
Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025),
Article 25.6.3, Theorem 10 (`jis-2025-25.6.3-thm-10`). -/
public theorem quasiFullTree_arity {P : Type*} [PartialOrder P] [Fintype P]
    (hn : 3 ≤ Fintype.card P) (hroot : ∃ ρ : P, ∀ x, ρ ≤ x)
    (hchain : ∀ x : P, IsChain (· ≤ ·) (Set.Iic x)) :
    ((∀ x : P, Nat.card {y : P // x ⋖ y} =
        min (Nat.card (Set.Ici x) - 1) (Fintype.card P - 1)) →
      ∀ t, Fintype.card P ≤ t →
        ∀ x : P, Nat.card {y : P // x ⋖ y} = min (Nat.card (Set.Ici x) - 1) t) ∧
    (∀ t, t ≤ Fintype.card P - 2 →
      (∀ x : P, Nat.card {y : P // x ⋖ y} = min (Nat.card (Set.Ici x) - 1) t) →
        ∀ t', Fintype.card P ≤ t' →
          ¬ ∀ x : P, Nat.card {y : P // x ⋖ y} = min (Nat.card (Set.Ici x) - 1) t') := by
  -- Every up-set has at most `n` elements, and the up-set of the root has exactly `n`.
  have hle (x : P) : Nat.card (Set.Ici x) ≤ Fintype.card P := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  refine ⟨fun h t ht x => ?_, fun t ht h t' ht' h' => ?_⟩
  · have := hle x
    rw [h x, min_eq_left (by omega), min_eq_left (by omega)]
  · obtain ⟨ρ, hρ⟩ := hroot
    have hU : Nat.card (Set.Ici ρ) = Fintype.card P := by
      rw [Set.eq_univ_of_forall (s := Set.Ici ρ) hρ, Nat.card_univ, Nat.card_eq_fintype_card]
    have h₁ := h ρ
    have h₂ := h' ρ
    rw [hU] at h₁ h₂
    omega

end MetaMathlibExt
