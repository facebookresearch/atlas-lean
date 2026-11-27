/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SlowANim

/-!
# P-positions after adding moves

This module proves `isPPositionSet_extend`, which gives a set of P-positions after
adding moves to a move relation.

Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite
Families of Slow`A`-Nim*, INTEGERS 26 (2026), Article G3 (arXiv:2404.06608v3),
Proposition 7.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **P-positions after adding moves.** Let $M$ and $E$ be move relations on a type of positions,
let $P$ be a set of P-positions for $M$, and let $Q \subseteq P$. Suppose that (1) no element of
$P \setminus Q$ has an $E$-move to an element of $P \setminus Q$, (2) every position outside $P$
that has an $M$-move into $Q$ has an $M$-move or an $E$-move into $P \setminus Q$, and (3) every
position of $Q$ has an $E$-move into $P \setminus Q$. Then $P \setminus Q$ is a set of
P-positions for the move relation "$M$ or $E$".

The relations $M$ and $E$ need not be disjoint.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Proposition 7. -/
public theorem isPPositionSet_extend {α : Type*} (M E : α → α → Prop) (P Q : Set α)
    (hP : IsPPositionSet M P) (hQP : Q ⊆ P)
    (h1 : ∀ x y, x ∈ P \ Q → y ∈ P \ Q → ¬ E x y)
    (h2 : ∀ x, x ∉ P → (∃ y ∈ Q, M x y) → ∃ y ∈ P \ Q, M x y ∨ E x y)
    (h3 : ∀ x ∈ Q, ∃ y ∈ P \ Q, E x y) :
    IsPPositionSet (fun x y => M x y ∨ E x y) (P \ Q) := by
  classical
  constructor
  · intro x y hx hxy hy
    rcases hxy with hM | hE
    · exact hP.1 x y hx.1 hM hy.1
    · exact h1 x y hx hy hE
  · intro x hx
    by_cases hxQ : x ∈ Q ∧ x ∈ P
    · obtain ⟨y, hy, hE⟩ := h3 x hxQ.1
      exact ⟨y, Or.inr hE, hy⟩
    · have hxNotQ : x ∉ Q := fun h => hxQ ⟨h, hQP h⟩
      have hxP : x ∉ P := fun hxP => hx ⟨hxP, hxNotQ⟩
      obtain ⟨y, hM, hyP⟩ := hP.2 x hxP
      by_cases hyQ : y ∈ Q
      · obtain ⟨z, hz, hzM⟩ := h2 x hxP ⟨y, hyQ, hM⟩
        exact ⟨z, hzM, hz⟩
      · exact ⟨y, Or.inl hM, hyP, hyQ⟩

end

end MetaMathlibExt
