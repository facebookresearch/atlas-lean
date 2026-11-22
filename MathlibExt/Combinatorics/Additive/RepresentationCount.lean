/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Ordered additive representation counts

This file provides the shared ordered representation count used by several
Erdős-problem statements: the number of ordered pairs `(a, b) ∈ A × A` with
`a + b = n`, counted over the finite antidiagonal.

## Main definitions

* `AdditiveCombinatorics.orderedRepresentationCount`: ordered representation count.

## Main statements

* `AdditiveCombinatorics.orderedRepresentationCount_pos_iff`: positivity holds
  iff an ordered representation exists.
-/

@[expose] public section

namespace AdditiveCombinatorics

/-- **Ordered representation count.** For a set $A$ of natural numbers and a natural number $n$,
the ordered representation count of $n$ by $A$ is the number of ordered pairs
$(a, b) \in A \times A$ with $a + b = n$. Pairs are not identified under swapping: when $a \ne b$,
the pairs $(a, b)$ and $(b, a)$ are counted separately. -/
public noncomputable def orderedRepresentationCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter
    (fun ab => ab.1 ∈ A ∧ ab.2 ∈ A)).card

/-- **Positivity of the ordered representation count.** For a set $A$ of natural numbers and a
natural number $n$, the number of ordered pairs $(a, b) \in A \times A$ with $a + b = n$ is
positive if and only if $n = a + b$ for some $a \in A$ and $b \in A$. -/
public theorem orderedRepresentationCount_pos_iff {A : Set ℕ} {n : ℕ} :
    0 < orderedRepresentationCount A n ↔
      ∃ a ∈ A, ∃ b ∈ A, a + b = n := by
  classical
  unfold orderedRepresentationCount
  rw [Finset.card_pos]
  constructor
  · rintro ⟨⟨a, b⟩, hmem⟩
    have h := Finset.mem_filter.mp hmem
    have hanti := h.1
    have ha := h.2.1
    have hb := h.2.2
    have hsum := Finset.mem_antidiagonal.mp hanti
    exact ⟨a, ha, b, hb, hsum⟩
  · rintro ⟨a, ha, b, hb, hsum⟩
    exact ⟨(a, b), Finset.mem_filter.mpr
      ⟨Finset.mem_antidiagonal.mpr hsum, ha, hb⟩⟩

end AdditiveCombinatorics
