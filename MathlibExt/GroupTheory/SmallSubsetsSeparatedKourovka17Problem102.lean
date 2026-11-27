/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Order
import Mathlib.GroupTheory.Perm.Support
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Small disjoint subsets of an infinite group need not be separated

We refute the separation assertion in Kourovka Notebook Problem 17.102. Following Wan, we split
the transpositions of the natural numbers according to a rigid graph. Here the graph is the
one-way infinite path, whose edges join consecutive natural numbers.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.102 (I. V. Protasov). UnsolvedMath
record UM-00701404 (`KOU-17.102`), dataset ulamai/UnsolvedMath v1.8.0.

`XAX` is the pointwise product of sets and cardinalities are `Cardinal.mk`; groups are taken in
`Type`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SmallSubsetsSeparatedKourovka17Problem102Wanted

open scoped Pointwise

/-- **Separated subsets of a group.** Two subsets $A$ and $B$ of a group $G$ are separated, in the
sense of I. V. Protasov, when there is an infinite subset $X \subseteq G$ with $1 \in X$,
$X^{-1} = X$ and $XAX \cap B = \emptyset$, where $XAX = \{x a y : x, y \in X,\ a \in A\}$. -/
def AreSeparated {G : Type*} [Group G] (A B : Set G) : Prop :=
  ∃ X : Set G, X.Infinite ∧ (1 : G) ∈ X ∧ X⁻¹ = X ∧ Disjoint (X * A * X) B

/-- **Separation of small disjoint subsets of infinite groups (Kourovka 17.102).** The statement,
posed by I. V. Protasov, that for every infinite group $G$ and all disjoint subsets
$A, B \subseteq G$ with $|A| < |G|$ and $|B| < |G|$, the sets $A$ and $B$ are separated. -/
def smallDisjointSubsetsSeparated : Prop :=
  ∀ (G : Type) [Group G] [Infinite G] (A B : Set G), Disjoint A B →
    Cardinal.mk A < Cardinal.mk G → Cardinal.mk B < Cardinal.mk G → AreSeparated A B

/-- A permutation carrying consecutive pairs to consecutive pairs fixes the entire ray. -/
private theorem eq_one_of_preserves_adjacency (g : Equiv.Perm ℕ)
    (h : ∀ n, g (n + 1) = g n + 1 ∨ g n = g (n + 1) + 1) : g = 1 := by
  -- An interior vertex has two distinct neighbors, so it cannot map to zero.
  have h₀ : g 0 = 0 := by
    obtain ⟨n, hn⟩ := g.surjective 0
    cases n with
    | zero => exact hn
    | succ n =>
      have hleft := h n
      have hright := h (n + 1)
      have hne := g.injective.ne (show n ≠ n + 1 + 1 by omega)
      omega
  -- Once two successive vertices are fixed, injectivity rules out turning back.
  suffices hfix : ∀ n, g n = n ∧ g (n + 1) = n + 1 from Equiv.ext fun n ↦ (hfix n).1
  intro n
  induction n with
  | zero =>
    have := h 0
    exact ⟨h₀, by omega⟩
  | succ n ih =>
    have := h (n + 1)
    have hne := g.injective.ne (show n ≠ n + 1 + 1 by omega)
    exact ⟨ih.2, by omega⟩

private theorem adjacent_of_swap_eq {a b n : ℕ} (hab : a ≠ b)
    (he : Equiv.swap n (n + 1) = Equiv.swap a b) : b = a + 1 ∨ a = b + 1 := by
  have ha : Equiv.swap n (n + 1) a ≠ a := by simpa [he] using hab.symm
  have hb : Equiv.swap n (n + 1) b ≠ b := by simpa [he] using hab
  have ha' := (Equiv.swap_apply_ne_self_iff.mp ha).2
  have hb' := (Equiv.swap_apply_ne_self_iff.mp hb).2
  omega

/--
**Small disjoint subsets of an infinite group need not be separated.** There exist an infinite
group $G$ and disjoint subsets $A, B \subseteq G$ with $|A| < |G|$ and $|B| < |G|$ such that $A$
and $B$ are not separated. That is, the statement of Kourovka Problem 17.102 is false.

Resolved false: Wan (Theorem 1.1) takes $G = \mathrm{Sym}(\mathbb{N})$ and splits the set of
transpositions into $A$ and $B$ using a graph on $\mathbb{N}$ with trivial automorphism group, so
that $|A| = |B| = \aleph_0 < 2^{\aleph_0}$. The Kourovka Notebook (21st issue) answers 17.102
"No, not always".

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 17.102 (I. V. Protasov); resolution: S. Wan, Counterexamples to Problem 17.102 of
The Kourovka Notebook, preprint, arXiv:2608.00504 (2026), Theorem 1.1 (an infinite group G with
disjoint A, B, |A|, |B| < |G|, not separated; in the proof G = Sym(N) and A, B split the
transpositions by a rigid graph on N); the Kourovka Notebook (21st issue) marks 17.102 solved (No,
not always), https://arxiv.org/abs/2608.00504.
-/
theorem smallDisjointSubsetsSeparated_refuted : ¬ smallDisjointSubsetsSeparated := by
  intro hsep
  let A := Set.range fun n : ℕ ↦ Equiv.swap n (n + 1)
  let B := {g : Equiv.Perm ℕ | g.IsSwap} \ A
  have hsmall (S : Set (Equiv.Perm ℕ)) (hS : S.Countable) :
      Cardinal.mk S < Cardinal.mk (Equiv.Perm ℕ) := by
    rw [Cardinal.mk_perm_eq_two_power, Cardinal.mk_nat]
    exact (Cardinal.le_aleph0_iff_set_countable.mpr hS).trans_lt (Cardinal.cantor _)
  have hB : B.Countable := by
    apply (Set.countable_range fun p : ℕ × ℕ ↦ Equiv.swap p.1 p.2).mono
    rintro g ⟨⟨i, j, _, rfl⟩, _⟩
    exact ⟨(i, j), rfl⟩
  obtain ⟨X, hinf, _, hsym, hdisj⟩ :=
    hsep _ A B Set.disjoint_sdiff_right (hsmall A (Set.countable_range _)) (hsmall B hB)
  obtain ⟨g, hg, hne⟩ := hinf.nontrivial.exists_ne 1
  apply hne
  apply eq_one_of_preserves_adjacency
  intro n
  have hinv : g⁻¹ ∈ X := Set.mem_inv.mp (by rwa [hsym])
  have hconj : Equiv.swap (g n) (g (n + 1)) ∈ X * A * X := by
    rw [Equiv.swap_apply_apply]
    exact Set.mul_mem_mul (Set.mul_mem_mul hg (Set.mem_range_self n)) hinv
  have hdistinct := g.injective.ne (Nat.ne_of_lt (Nat.lt_succ_self n))
  have hedge : Equiv.swap (g n) (g (n + 1)) ∈ A := by
    by_contra h
    exact Set.disjoint_left.mp hdisj hconj ⟨⟨_, _, hdistinct, rfl⟩, h⟩
  obtain ⟨k, hk⟩ := hedge
  exact adjacent_of_swap_eq hdistinct hk

end MathlibExt.GroupTheory.SmallSubsetsSeparatedKourovka17Problem102Wanted
