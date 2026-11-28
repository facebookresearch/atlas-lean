/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.HammingBall

@[expose] public section

namespace Hamming

/-!
# Generic Hamming expansion and ball predicates

ATLAS item N134 (ProbabilisticMethodsInCombinatorics:134). Reusable generic
support extracted while reformalizing that item. Source:
`Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/HarperIsoperimetric.lean`
(lines 17--39) at commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`:
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/HarperIsoperimetric.lean#L17-L39>

Source-to-API map: ATLAS's duplicate Hamming distance and ball map to
existing `hammingDist` and `Hamming.ball`, while ATLAS's expansion operator and ball
predicate map to `Hamming.expansion` and `Hamming.IsBall`.

This module is a supporting step, not the full N134 target; the Wanted module
states the full ball-comparison target. The Harper theorem itself is not
proved here.
-/

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]

/-- **Hamming expansion.** Let $\iota$ and $F$ be finite, and view functions $\iota \to F$ as
words with the Hamming distance. For a finite set $A$ of words and $t \in \mathbb{N}$, the
$t$-expansion of $A$ is the set of words at Hamming distance at most $t$ from some element of
$A$, that is, the union over $a \in A$ of the closed Hamming balls of radius $t$ about $a$. -/
def expansion (A : Finset (ι → F)) (t : ℕ) : Finset (ι → F) :=
  A.biUnion fun a => ball a t

@[simp]
theorem mem_expansion {A : Finset (ι → F)} {x : ι → F} {t : ℕ} :
    x ∈ expansion A t ↔ ∃ a ∈ A, hammingDist x a ≤ t := by
  simp only [expansion, Finset.mem_biUnion, mem_ball, hammingDist_comm]

theorem mem_expansion_of_mem {A : Finset (ι → F)} {x a : ι → F} {t : ℕ}
    (ha : a ∈ A) (h : hammingDist x a ≤ t) : x ∈ expansion A t :=
  mem_expansion.mpr ⟨a, ha, h⟩

@[simp]
theorem expansion_empty (t : ℕ) : expansion (∅ : Finset (ι → F)) t = ∅ := by
  simp [expansion]

@[simp]
theorem expansion_singleton (a : ι → F) (t : ℕ) :
    expansion {a} t = ball a t := by
  simp [expansion]

theorem subset_expansion_self (A : Finset (ι → F)) (t : ℕ) :
    A ⊆ expansion A t := by
  intro x hx
  rw [mem_expansion]
  exact ⟨x, hx, by simp [hammingDist_self]⟩

theorem expansion_mono {A B : Finset (ι → F)} {t : ℕ} (h : A ⊆ B) :
    expansion A t ⊆ expansion B t := by
  intro x hx
  rw [mem_expansion] at hx ⊢
  obtain ⟨a, ha, hdist⟩ := hx
  exact ⟨a, h ha, hdist⟩

/-- **Hamming ball predicate.** Let $\iota$ and $F$ be finite, and view functions $\iota \to F$
as words with the Hamming distance. A set $B$ of words is a Hamming ball if there are a word
$c$ and a radius $e \in \mathbb{N}$ such that $B$ is the closed Hamming ball of radius $e$
about $c$. -/
def IsBall (B : Finset (ι → F)) : Prop :=
  ∃ c : ι → F, ∃ e : ℕ, B = ball c e

theorem isBall_ball (c : ι → F) (e : ℕ) : IsBall (ball c e : Finset (ι → F)) :=
  ⟨c, e, rfl⟩

end Hamming
