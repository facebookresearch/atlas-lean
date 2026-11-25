/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Index

open scoped Pointwise

@[expose] public section

/-! # G-harmonic tuples

Source: Murali Menon, "Two Questions on G-Harmonic Tuples"
(https://arxiv.org/abs/2608.15873v1, Definition span lines 33--37 of `main.tex`).
For a group `G`, a tuple `a : Fin n → ℕ` of positive integers is `G`-harmonic when
subgroups `U i` of exact index `a i` have left cosets `g i • (U i : Set G)` that
are pairwise disjoint. Since `Subgroup.index` is `0` for infinite index,
positivity plus exact index equality rules out infinite index. -/

/-- **G-harmonic tuples.** Let $G$ be a group and $a = (a_1, \dots, a_n)$ a tuple of natural
numbers. The tuple $a$ is $G$-harmonic if every $a_i$ is positive and there exist subgroups
$U_1, \dots, U_n$ of $G$ and elements $g_1, \dots, g_n \in G$ such that $U_i$ has index $a_i$ in
$G$ for every $i$ and the left cosets $g_1 U_1, \dots, g_n U_n$ are pairwise disjoint. -/
def IsGHarmonic (G : Type*) [Group G] {n : ℕ} (a : Fin n → ℕ) : Prop :=
  (∀ i, 0 < a i) ∧
    ∃ (U : Fin n → Subgroup G) (g : Fin n → G),
      (∀ i, (U i).index = a i) ∧
        Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G))

/-- **Constructing a G-harmonic tuple.** Let $G$ be a group and $a = (a_1, \dots, a_n)$ a tuple
of natural numbers with every $a_i$ positive. If $U_1, \dots, U_n$ are subgroups of $G$ such that
$U_i$ has index $a_i$ in $G$ for every $i$, and $g_1, \dots, g_n \in G$ are elements such that the
left cosets $g_1 U_1, \dots, g_n U_n$ are pairwise disjoint, then $a$ is $G$-harmonic. -/
theorem IsGHarmonic.intro {G : Type*} [Group G] {n : ℕ} {a : Fin n → ℕ}
    (hpos : ∀ i, 0 < a i) (U : Fin n → Subgroup G) (g : Fin n → G)
    (hidx : ∀ i, (U i).index = a i)
    (hdisj : Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G))) :
    IsGHarmonic G a :=
  ⟨hpos, U, g, hidx, hdisj⟩

/-- **Entries of a G-harmonic tuple are positive.** Let $G$ be a group. If a tuple
$a = (a_1, \dots, a_n)$ of natural numbers is $G$-harmonic, then $a_i > 0$ for every $i$. -/
theorem IsGHarmonic.pos {G : Type*} [Group G] {n : ℕ} {a : Fin n → ℕ}
    (h : IsGHarmonic G a) (i : Fin n) : 0 < a i :=
  h.1 i

/-- **Witnesses for a G-harmonic tuple.** Let $G$ be a group. If a tuple $a = (a_1, \dots, a_n)$
of natural numbers is $G$-harmonic, then there exist subgroups $U_1, \dots, U_n$ of $G$ and
elements $g_1, \dots, g_n \in G$ such that $U_i$ has index $a_i$ in $G$ for every $i$ and the
left cosets $g_1 U_1, \dots, g_n U_n$ are pairwise disjoint. -/
theorem IsGHarmonic.witnesses {G : Type*} [Group G] {n : ℕ} {a : Fin n → ℕ}
    (h : IsGHarmonic G a) :
    ∃ (U : Fin n → Subgroup G) (g : Fin n → G),
      (∀ i, (U i).index = a i) ∧
        Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G)) :=
  h.2

/-- **Characterization of G-harmonic tuples.** Let $G$ be a group and $a = (a_1, \dots, a_n)$ a
tuple of natural numbers. Then $a$ is $G$-harmonic if and only if every $a_i$ is positive and
there are subgroups $U_1, \dots, U_n$ of $G$ and elements $g_1, \dots, g_n \in G$ such that $U_i$
has index $a_i$ in $G$ for every $i$ and the left cosets $g_1 U_1, \dots, g_n U_n$ are pairwise
disjoint. -/
theorem isGHarmonic_iff {G : Type*} [Group G] {n : ℕ} (a : Fin n → ℕ) :
    IsGHarmonic G a ↔
      (∀ i, 0 < a i) ∧
        ∃ (U : Fin n → Subgroup G) (g : Fin n → G),
          (∀ i, (U i).index = a i) ∧
            Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G)) :=
  Iff.rfl

/-- **The empty tuple is G-harmonic.** For every group $G$, the empty tuple of natural numbers is
(vacuously) $G$-harmonic. -/
theorem isGHarmonic_empty {G : Type*} [Group G] :
    IsGHarmonic G (n := 0) Fin.elim0 := by
  refine ⟨fun i => Fin.elim0 i, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, ?_⟩
  intro i _ j _ hij
  exact (hij (Subsingleton.elim i j)).elim

/-- **The tuple (1) is G-harmonic.** For every group $G$, the one-entry tuple $(1)$ is
$G$-harmonic; the subgroup $G$ itself, of index $1$, with coset representative $1$ witnesses
this. -/
theorem isGHarmonic_singleton_one {G : Type*} [Group G] :
    IsGHarmonic G (n := 1) (fun _ => 1) := by
  refine ⟨fun _ => Nat.zero_lt_one, fun _ => ⊤, fun _ => 1, fun i => ?_, ?_⟩
  · exact Subgroup.index_top
  · intro i _ j _ hij
    exact (hij (Subsingleton.elim i j)).elim

/-- **Tuples with a zero entry are not G-harmonic.** Let $G$ be a group. If a tuple
$a = (a_1, \dots, a_n)$ of natural numbers has $a_i = 0$ for some $i$, then $a$ is not
$G$-harmonic. -/
theorem not_isGHarmonic_of_zero {G : Type*} [Group G] {n : ℕ} {a : Fin n → ℕ}
    (i : Fin n) (h0 : a i = 0) : ¬ IsGHarmonic G a := by
  intro h
  have hp := h.pos i
  rw [h0] at hp
  exact Nat.lt_irrefl 0 hp

end
