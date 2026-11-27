/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
import Mathlib.Tactic

@[expose] public section

/-! # Arithmetic progressions -/

variable {α : Type*} [AddCommMonoid α]

/-- **Set arithmetic progressions with given first term and difference.** Let $M$ be an
additive commutative monoid, $l \in \mathbb{N} \cup \{\infty\}$ and $a, d \in M$. A set
$s \subseteq M$ is an arithmetic progression of length $l$ with first term $a$ and difference
$d$ if $s = \{a + n d : n \in \mathbb{N},\ n < l\}$ and $s$ has exactly $l$ elements, counting
the size of an infinite set as $\infty$; here $n d$ is the sum of $n$ copies of $d$. -/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- **Sets that are arithmetic progressions.** Let $\alpha$ be an additive commutative monoid
and $l \in \mathbb{N} \cup \{\infty\}$. A set $s \subseteq \alpha$ is an arithmetic progression
of length $l$ if there are $a, d \in \alpha$ such that
$s = \{a + nd : n \in \mathbb{N},\ n < l\}$ and $s$ has exactly $l$ elements (infinitely many
when $l = \infty$). Here $nd$ denotes the sum of $n$ copies of $d$. -/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

namespace Set.IsAPOfLength

variable {s : Set α} {l : ℕ∞}

/-- **Cardinality of a set arithmetic progression.** Let $M$ be an additive commutative monoid
and $l \in \mathbb{N} \cup \{\infty\}$. If a set $s \subseteq M$ is an arithmetic progression of
length $l$, then $s$ has exactly $l$ elements, counting the size of an infinite set as $\infty$. -/
theorem card (h : s.IsAPOfLength l) : ENat.card s = l :=
  h.choose_spec.choose_spec.1

/-- **First term and difference of a set arithmetic progression.** Let $M$ be an additive
commutative monoid and $l \in \mathbb{N} \cup \{\infty\}$. If a set $s \subseteq M$ is an
arithmetic progression of length $l$, then there are $a, d \in M$ with
$s = \{a + n d : n \in \mathbb{N},\ n < l\}$, where $n d$ is the sum of $n$ copies of $d$. -/
theorem eq (h : s.IsAPOfLength l) :
    ∃ a d : α, s = {a + n • d | (n : ℕ) (_ : n < l)} :=
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2⟩

end Set.IsAPOfLength

/-- **List arithmetic progressions with given start and difference.** Let $M$ be an additive
commutative monoid, $l \in \mathbb{N}$ and $a, d \in M$. A list $s$ of elements of $M$ is an
arithmetic progression of length $l$ starting from $a$ with difference $d$, in either direction,
if $s = (a, a + d, \dots, a + (l - 1)d)$ or $s = (a + (l - 1)d, \dots, a + d, a)$, where $n d$ is
the sum of $n$ copies of $d$; when $l = 0$ both lists are empty. -/
def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨
    s = (List.range l).reverse.map (fun n ↦ a + n • d)

/-- **Arithmetic progressions of lists.** Let $M$ be an additive commutative monoid and
$l \in \mathbb{N}$. A list $s$ of elements of $M$ is an arithmetic progression of length $l$ if
there are $a, d \in M$ such that $s = (a, a + d, \dots, a + (l - 1)d)$ or
$s = (a + (l - 1)d, \dots, a + d, a)$, where $n d$ is the sum of $n$ copies of $d$. -/
def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

/-- **Monotone arithmetic progressions in a function.** Let $M$ be an additive commutative
monoid, $\beta$ a preordered type, $f : \beta \to M$ and $k \in \mathbb{N}$. Then $f$ contains a
monotone arithmetic progression of length $k$ if there are $x_1 < x_2 < \dots < x_k$ in $\beta$
such that the list $(f(x_1), \dots, f(x_k))$ is an arithmetic progression of length $k$: for
some $a, d \in M$ it equals $(a, a + d, \dots, a + (k - 1)d)$ or its reverse. -/
def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

/-- **Progression-free sets.** Let $M$ be an additive commutative monoid and
$l \in \mathbb{N} \cup \{\infty\}$. A set $s \subseteq M$ is free of nontrivial arithmetic
progressions of length $l$ if every subset of $s$ that is an arithmetic progression of length $l$
forces $l \le 1$; equivalently, $l \le 1$ or no subset of $s$ is an arithmetic progression of
length $l$. -/
def Set.IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, t.IsAPOfLength l → l ≤ 1

/-- **A progression of length greater than one is not progression-free.** Let $s$ be a set in an
additive commutative monoid and $l \in \mathbb{N} \cup \{\infty\}$ with $l > 1$. If $s$ is an
arithmetic progression of length $l$, then $s$ is not free of nontrivial arithmetic progressions
of length $l$. -/
theorem Set.IsAPOfLength.not_isAPOfLengthFree {s : Set α} {l : ℕ∞}
    (hs : s.IsAPOfLength l) (hl : 1 < l) : ¬ s.IsAPOfLengthFree l := by
  simpa [Set.IsAPOfLengthFree] using ⟨s, le_rfl, ⟨hs, hl⟩⟩

/-- **Progression-free finite sets.** Let $M$ be an additive commutative monoid and
$l \in \mathbb{N} \cup \{\infty\}$. A finite set $s \subseteq M$ is free of nontrivial arithmetic
progressions of length $l$ if it is so as a set: $l \le 1$, or no subset of $s$ is an
arithmetic progression of length $l$. -/
def Finset.IsAPOfLengthFree (s : Finset α) (l : ℕ∞) : Prop :=
  (s : Set α).IsAPOfLengthFree l

@[simp] theorem Finset.isAPOfLengthFree_coe (s : Finset α) (l : ℕ∞) :
    s.IsAPOfLengthFree l ↔ (s : Set α).IsAPOfLengthFree l :=
  Iff.rfl

/-- **Sets of naturals without three-term progressions.** Let $s$ be a set of natural numbers
such that $a = b$ whenever $a, b, c \in s$ satisfy $a + c = 2b$. Then $s$ is free of nontrivial
arithmetic progressions of length $3$: no subset of $s$ is an arithmetic progression of
length $3$. -/
theorem ThreeAPFree.isAPOfLengthFree_three {s : Set ℕ} (hs : ThreeAPFree s) :
    s.IsAPOfLengthFree 3 := by
  intro t hts ht
  rcases ht with ⟨a, d, hcard, rfl⟩
  have ha : a ∈ s := hts ⟨0, by norm_num, by simp⟩
  have hb : a + d ∈ s := hts ⟨1, by norm_num, by simp⟩
  have hc : a + 2 * d ∈ s := hts ⟨2, by norm_num, by simp⟩
  have had : a = a + d := hs ha hb hc (by omega)
  have hd : d = 0 := by omega
  subst d
  have hset :
      {x : ℕ | ∃ n : ℕ, ∃ (_ : (n : ℕ∞) < 3), a + n • 0 = x} = {a} := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      simp
    · rintro rfl
      exact ⟨0, by norm_num, by simp⟩
  rw [hset] at hcard
  norm_num at hcard

/-- **Largest size of a progression-free subset of $\{1, \dots, N\}$.** For natural numbers
$k$ and $N$, $r_k(N)$ is the largest cardinality of a subset $S \subseteq \{1, \dots, N\}$ that
is free of nontrivial arithmetic progressions of length $k$, meaning that if $k \ge 2$ then no
subset of $S$ is an arithmetic progression of length $k$ (for $k \le 1$ every subset
qualifies). -/
noncomputable def Set.IsAPOfLengthFree.maxCard (k N : ℕ) : ℕ :=
  by
    classical
    exact Nat.findGreatest
      (fun m ↦ ∃ S : Finset ℕ,
        S ⊆ Finset.Icc 1 N ∧ S.card = m ∧ S.IsAPOfLengthFree k)
      N

namespace Set.IsAPOfLengthFree

/-- **Trivial upper bound for the largest progression-free subset.** For all natural numbers $k$
and $N$, the largest size $r_k(N)$ of a subset of $\{1, \dots, N\}$ free of nontrivial
arithmetic progressions of length $k$ satisfies $r_k(N) \le N$. -/
theorem maxCard_le (k N : ℕ) : maxCard k N ≤ N :=
  by
    classical
    unfold maxCard
    exact Nat.findGreatest_le N

/-- **A largest progression-free subset is attained.** For all natural numbers $k$ and $N$, let
$r_k(N)$ be the largest size of a subset of $\{1, \dots, N\}$ free of nontrivial arithmetic
progressions of length $k$. Then some subset $S \subseteq \{1, \dots, N\}$ free of nontrivial
arithmetic progressions of length $k$ has exactly $r_k(N)$ elements. -/
theorem maxCard_spec (k N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧
      S.card = maxCard k N ∧ S.IsAPOfLengthFree k := by
  classical
  unfold maxCard
  refine Nat.findGreatest_spec
    (P := fun m ↦ ∃ S : Finset ℕ,
      S ⊆ Finset.Icc 1 N ∧ S.card = m ∧ S.IsAPOfLengthFree k)
    (Nat.zero_le N) ?_
  refine ⟨∅, Finset.empty_subset _, rfl, ?_⟩
  intro t ht hAP
  have ht' : t ⊆ (∅ : Set ℕ) := by simpa using ht
  have ht0 : t = ∅ := Set.subset_empty_iff.mp ht'
  subst t
  have hk : (k : ℕ∞) = 0 := by simpa using hAP.card.symm
  simp [hk]

/-- **Progression-free subsets are bounded by the extremal size.** Let $k$ and $N$ be natural
numbers, and let $S$ be a finite set of natural numbers with $S \subseteq \{1, \dots, N\}$ that
is free of nontrivial arithmetic progressions of length $k$. Then $|S| \le r_k(N)$, where
$r_k(N)$ is the largest size of a subset of $\{1, \dots, N\}$ containing no nontrivial $k$-term
arithmetic progression. -/
theorem card_le_maxCard {S : Finset ℕ} {k N : ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hfree : S.IsAPOfLengthFree k) :
    S.card ≤ maxCard k N := by
  classical
  unfold maxCard
  apply Nat.le_findGreatest
  · exact (Finset.card_le_card hS).trans_eq (Nat.card_Icc 1 N)
  · exact ⟨S, hS, rfl, hfree⟩

end Set.IsAPOfLengthFree
