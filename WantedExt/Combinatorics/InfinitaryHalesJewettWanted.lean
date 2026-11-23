/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Free
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.List.OfFn
public import MathlibExt.Combinatorics.SemigroupLargeness

/-!
# Infinitary Hales–Jewett theorems for variable words

Statements quoted in Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary
Hales–Jewett Theorem*, INTEGERS 24 (2024), Article A74. A variable word over an alphabet `A` is
a list over `Option A` in which the variable `none` occurs; `w(a)` replaces every occurrence of
the variable by the letter `a`. Theorem 1.1 (Hales–Jewett) and Theorem 1.7 (`n`-variable words)
are Mathlib's `Combinatorics.Line.exists_mono_in_high_dimension` and
`Combinatorics.Subspace.exists_mono_in_high_dimension`.

Section 3 of the paper fixes an increasing sequence of finite alphabets `A_0 ⊆ A_1 ⊆ ⋯` with
union `A`. Its statements are rendered with `A : ℕ → Finset α`, `Monotone A`, and the covering
hypothesis `∀ x, ∃ i, x ∈ A i`, so that the ambient type `α` is the alphabet `A` itself and the
semigroup `S_0` of nonempty words over `A` under concatenation is `FreeSemigroup α`. An
`n`-variable word (an element of `S_n`) is an element `w` of `FreeSemigroup (α ⊕ Fin n)` in which
every variable `Sum.inr i` occurs, and `w(a⃗)` is `FreeSemigroup.map (Sum.elim id a⃗) w`. Words
are indexed from `0` rather than `1`; since the alphabets increase, a sequence indexed from `1`
with `w_i` evaluated over `A_i` shifts to one indexed from `0` with `w_i` evaluated over `A_i`
(and conversely), so the shift does not change the statements. Products `x₀ x₁ ⋯ x_l` in a
semigroup are written as left folds `List.foldl (· * ·) x₀ [x₁, …, x_l]`. The largeness
notions (piecewise syndetic sets, `J`-sets, central sets, `C`-sets) are the reusable
definitions of `MathlibExt.Combinatorics.SemigroupLargeness`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Infinitary Hales–Jewett theorem.** Let $A$ be a finite alphabet, and color the finite words
over $A$ with finitely many colors. A variable word over $A$ is a finite word over $A \cup \{v\}$,
for a variable $v \notin A$, in which $v$ occurs, and $w(a)$ is the word obtained from $w$ by
replacing every occurrence of $v$ by the letter $a$. Then there are a sequence $w_0, w_1, \dots$ of
variable words over $A$ and a color $k$ such that the word
$w_{m_1}(a_1) w_{m_2}(a_2) \cdots w_{m_l}(a_l)$ has color $k$ for all $l \ge 1$, all
$m_1 < m_2 < \cdots < m_l$ in $\mathbb{N}$ and all $a_1, \dots, a_l \in A$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 1.2 (Bergelson, Blass and Hindman). -/
public theorem_wanted infinitary_halesJewett {A κ : Type*} [Finite A] [Finite κ]
    (c : List A → κ) :
    ∃ (w : ℕ → List (Option A)) (k : κ), (∀ n, none ∈ w n) ∧
      ∀ (l : ℕ) (m : Fin l → ℕ) (a : Fin l → A), 1 ≤ l → StrictMono m →
        c (List.ofFn fun i => (w (m i)).map fun o => o.getD (a i)).flatten = k

/-- **Karagiannis's infinitary Hales–Jewett theorem for increasing alphabets.** Let $X$ be a set,
let $A_0 \subseteq A_1 \subseteq \cdots$ be finite subsets of $X$ with union $A$, and color the
finite words over $X$ with finitely many colors. A variable word over $A$ is a finite word over
$A \cup \{v\}$, for a variable $v \notin X$, in which $v$ occurs, and $w(a)$ is the word obtained
from $w$ by replacing every occurrence of $v$ by the letter $a$. Then there are a sequence
$w_0, w_1, \dots$ of variable words over $A$ and a color $k$ such that the word
$w_{m_1}(a_1) w_{m_2}(a_2) \cdots w_{m_l}(a_l)$ has color $k$ for all $l \ge 1$, all
$m_1 < m_2 < \cdots < m_l$ in $\mathbb{N}$ and all $a_i \in A_{m_i}$, $i = 1, \dots, l$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 1.8 (Karagiannis). -/
public theorem_wanted infinitary_halesJewett_increasing_alphabets {α κ : Type*} [Finite κ]
    (A : ℕ → Finset α) (hA : Monotone A) (c : List α → κ) :
    ∃ (w : ℕ → List (Option α)) (k : κ),
      (∀ n, none ∈ w n ∧ ∀ x : α, some x ∈ w n → ∃ i, x ∈ A i) ∧
      ∀ (l : ℕ) (m : Fin l → ℕ) (a : Fin l → α), 1 ≤ l → StrictMono m →
        (∀ i, a i ∈ A (m i)) →
        c (List.ofFn fun i => (w (m i)).map fun o => o.getD (a i)).flatten = k

/-- **Piecewise syndetic sets contain Hales–Jewett configurations.** Let
$A_0 \subseteq A_1 \subseteq \cdots$ be finite sets with union $A$, and let $S_0$ be the semigroup
of nonempty finite words over $A$ under concatenation. For $n \in \mathbb{N}$, an $n$-variable
word over $A$ is a nonempty finite word over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct
variables $v_i \notin A$, in which every $v_i$ occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in
$A^n$, the word $w(\vec a) \in S_0$ is obtained from $w$ by replacing each $v_i$ by $a_i$. If
$D \subseteq S_0$ is piecewise syndetic, then for all $m, n \in \mathbb{N}$ there is an
$n$-variable word $w$ over $A$ with $w(\vec a) \in D$ for every $\vec a \in A_m^n$.

For $n = 0$ the claim is that $D$ is nonempty.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Lemma 3.3. -/
public theorem_wanted exists_variableWord_subst_mem_of_isMulPiecewiseSyndetic {α : Type*}
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (m n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsMulPiecewiseSyndetic D) :
    ∃ w : FreeSemigroup (α ⊕ Fin n), (∀ i, Sum.inr i ∈ w.head :: w.tail) ∧
      ∀ a : Fin n → α, (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) w ∈ D

/-- **J-sets contain Hales–Jewett configurations.** Let $A_0 \subseteq A_1 \subseteq \cdots$ be
finite sets whose union $A$ is nonempty, and let $S_0$ be the semigroup of nonempty finite words
over $A$ under concatenation. For $n \in \mathbb{N}$, an $n$-variable word over $A$ is a nonempty
finite word over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct variables $v_i \notin A$, in which
every $v_i$ occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in $A^n$, the word $w(\vec a) \in S_0$
is obtained from $w$ by replacing each $v_i$ by $a_i$. If $D \subseteq S_0$ is a $J$-set, then
for all $m, n \in \mathbb{N}$ there is an $n$-variable word $w$ over $A$ with $w(\vec a) \in D$
for every $\vec a \in A_m^n$.

The alphabet must be nonempty: over the empty alphabet every subset of $S_0 = \emptyset$ is
vacuously a $J$-set, and there is no $0$-variable word.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Lemma 3.4. -/
public theorem_wanted exists_variableWord_subst_mem_of_isMulJSet {α : Type*} [Nonempty α]
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (m n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsMulJSet D) :
    ∃ w : FreeSemigroup (α ⊕ Fin n), (∀ i, Sum.inr i ∈ w.head :: w.tail) ∧
      ∀ a : Fin n → α, (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) w ∈ D

/-- **Infinitary Hales–Jewett configurations in central sets.** Let
$A_0 \subseteq A_1 \subseteq \cdots$ be finite sets with union $A$, and let $S_0$ be the semigroup
of nonempty finite words over $A$ under concatenation. For $n \in \mathbb{N}$, an $n$-variable
word over $A$ is a nonempty finite word over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct
variables $v_i \notin A$, in which every $v_i$ occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in
$A^n$, the word $w(\vec a) \in S_0$ is obtained from $w$ by replacing each $v_i$ by $a_i$. If
$D \subseteq S_0$ is central, then for every $n \in \mathbb{N}$ there is a sequence
$w_0, w_1, \dots$ of $n$-variable words over $A$ such that
$w_{m_0}(\vec a_0) w_{m_1}(\vec a_1) \cdots w_{m_l}(\vec a_l) \in D$ for all $l \in \mathbb{N}$,
all $m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$ and all $\vec a_j \in A_{m_j}^n$,
$j = 0, \dots, l$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 3.5. -/
public theorem_wanted exists_variableWords_prod_mem_of_isCentralSet {α : Type*}
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsCentralSet D) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin n), (∀ k i, Sum.inr i ∈ (w k).head :: (w k).tail) ∧
      ∀ (l : ℕ) (m : Fin (l + 1) → ℕ) (a : Fin (l + 1) → Fin n → α), StrictMono m →
        (∀ j i, a j i ∈ A (m j)) →
        (List.ofFn fun j : Fin l => FreeSemigroup.map (Sum.elim id (a j.succ)) (w (m j.succ))).foldl
          (· * ·) (FreeSemigroup.map (Sum.elim id (a 0)) (w (m 0))) ∈ D

/-- **Infinitary Hales–Jewett configurations in C-sets.** Let
$A_0 \subseteq A_1 \subseteq \cdots$ be finite sets with union $A$, and let $S_0$ be the semigroup
of nonempty finite words over $A$ under concatenation. For $n \in \mathbb{N}$, an $n$-variable
word over $A$ is a nonempty finite word over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct
variables $v_i \notin A$, in which every $v_i$ occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in
$A^n$, the word $w(\vec a) \in S_0$ is obtained from $w$ by replacing each $v_i$ by $a_i$. If
$D \subseteq S_0$ is a $C$-set, then for every $n \in \mathbb{N}$ there is a sequence
$w_0, w_1, \dots$ of $n$-variable words over $A$ such that
$w_{m_0}(\vec a_0) w_{m_1}(\vec a_1) \cdots w_{m_l}(\vec a_l) \in D$ for all $l \in \mathbb{N}$,
all $m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$ and all $\vec a_j \in A_{m_j}^n$,
$j = 0, \dots, l$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Corollary 3.6. -/
public theorem_wanted exists_variableWords_prod_mem_of_isCSet {α : Type*}
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsCSet D) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin n), (∀ k i, Sum.inr i ∈ (w k).head :: (w k).tail) ∧
      ∀ (l : ℕ) (m : Fin (l + 1) → ℕ) (a : Fin (l + 1) → Fin n → α), StrictMono m →
        (∀ j i, a j i ∈ A (m j)) →
        (List.ofFn fun j : Fin l => FreeSemigroup.map (Sum.elim id (a j.succ)) (w (m j.succ))).foldl
          (· * ·) (FreeSemigroup.map (Sum.elim id (a 0)) (w (m 0))) ∈ D

/-- **Variable-count sums of variable words in J-sets.** Let $A_0 \subseteq A_1 \subseteq \cdots$
be finite sets with union $A$, and let $S_0$ be the semigroup of nonempty finite words over $A$
under concatenation. A variable word over $A$ is a nonempty finite word over $A \cup \{v\}$, for a
variable $v \notin A$, in which $v$ occurs; for $a \in A$, the word $w(a) \in S_0$ is obtained from
$w$ by replacing each occurrence of $v$ by $a$, and $|w|_v$ is the number of occurrences of $v$ in
$w$. If $D \subseteq S_0$ is a $J$-set and $x_0, x_1, \dots$ are positive integers, then there is
a sequence $w_0, w_1, \dots$ of variable words over $A$ such that $w_k(a) \in D$ for all
$k \in \mathbb{N}$ and $a \in A_k$, and such that for every nonempty finite $G \subseteq \mathbb{N}$
there is a nonempty finite $H \subseteq \mathbb{N}$ with
$\sum_{k \in G} |w_k|_v = \sum_{j \in H} x_j$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 3.7. -/
public theorem_wanted exists_variableWords_subst_mem_sum_count_mem_finiteSums_of_isMulJSet
    {α : Type*} (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i)
    {D : Set (FreeSemigroup α)} (hD : IsMulJSet D) (x : ℕ → ℕ) (hx : ∀ j, 0 < x j) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin 1), (∀ k, Sum.inr 0 ∈ (w k).head :: (w k).tail) ∧
      (∀ k a, a ∈ A k → FreeSemigroup.map (Sum.elim id fun _ => a) (w k) ∈ D) ∧
      ∀ G : Finset ℕ, G.Nonempty → ∃ H : Finset ℕ, H.Nonempty ∧
        ∑ k ∈ G, ((w k).head :: (w k).tail).countP Sum.isRight = ∑ j ∈ H, x j

/-- **Variable-count sums of variable words in C-sets.** Let $A_0 \subseteq A_1 \subseteq \cdots$
be finite sets with union $A$, and let $S_0$ be the semigroup of nonempty finite words over $A$
under concatenation. A variable word over $A$ is a nonempty finite word over $A \cup \{v\}$, for a
variable $v \notin A$, in which $v$ occurs; for $a \in A$, the word $w(a) \in S_0$ is obtained from
$w$ by replacing each occurrence of $v$ by $a$, and $|w|_v$ is the number of occurrences of $v$ in
$w$. If $D \subseteq S_0$ is a $C$-set and $x_0, x_1, \dots$ are positive integers, then there is
a sequence $w_0, w_1, \dots$ of variable words over $A$ such that
$w_{m_0}(a_0) w_{m_1}(a_1) \cdots w_{m_l}(a_l) \in D$ for all $l \in \mathbb{N}$, all
$m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$ and all $a_j \in A_{m_j}$, $j = 0, \dots, l$, and such
that for every nonempty finite $G \subseteq \mathbb{N}$ there is a nonempty finite
$H \subseteq \mathbb{N}$ with $\sum_{k \in G} |w_k|_v = \sum_{j \in H} x_j$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Corollary 3.8. -/
public theorem_wanted exists_variableWords_prod_mem_sum_count_mem_finiteSums_of_isCSet
    {α : Type*} (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i)
    {D : Set (FreeSemigroup α)} (hD : IsCSet D) (x : ℕ → ℕ) (hx : ∀ j, 0 < x j) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin 1), (∀ k, Sum.inr 0 ∈ (w k).head :: (w k).tail) ∧
      (∀ (l : ℕ) (m : Fin (l + 1) → ℕ) (a : Fin (l + 1) → α), StrictMono m →
        (∀ j, a j ∈ A (m j)) →
        (List.ofFn fun j : Fin l =>
            FreeSemigroup.map (Sum.elim id fun _ => a j.succ) (w (m j.succ))).foldl
          (· * ·) (FreeSemigroup.map (Sum.elim id fun _ => a 0) (w (m 0))) ∈ D) ∧
      ∀ G : Finset ℕ, G.Nonempty → ∃ H : Finset ℕ, H.Nonempty ∧
        ∑ k ∈ G, ((w k).head :: (w k).tail).countP Sum.isRight = ∑ j ∈ H, x j

/-- **Variable patterns of variable words in J-sets.** Let $A_0 \subseteq A_1 \subseteq \cdots$
be finite sets with union $A$, and let $S_0$ be the semigroup of nonempty finite words over $A$
under concatenation. Let $1 \le k < n$. An $n$-variable word over $A$ is a nonempty finite word
over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct variables $v_i \notin A$, in which every $v_i$
occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in $A^n$, the word $w(\vec a) \in S_0$ is obtained
from $w$ by replacing each $v_i$ by $a_i$, and $\tau(w)$ is the word over
$\{v_0, \dots, v_{k-1}\}$ obtained from $w$ by deleting the letters of $A$ and the variables $v_i$
with $i \ge k$. Let $y_0, y_1, \dots$ be finite words over $\{v_0, \dots, v_{k-1}\}$ in each of
which every $v_i$ with $i < k$ occurs. If $D \subseteq S_0$ is a $J$-set, then there is a
sequence $w_0, w_1, \dots$ of $n$-variable words over $A$ such that $w_m(\vec a) \in D$ for all
$m \in \mathbb{N}$ and $\vec a \in A_m^n$, and such that for all $l \in \mathbb{N}$ and
$m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$ there are $r \in \mathbb{N}$ and
$t_0 < t_1 < \cdots < t_r$ in $\mathbb{N}$ with
$\tau(w_{m_0}) \tau(w_{m_1}) \cdots \tau(w_{m_l}) = y_{t_0} y_{t_1} \cdots y_{t_r}$, where
juxtaposition is concatenation of words.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 3.9. -/
public theorem_wanted exists_variableWords_subst_mem_prod_pattern_mem_finiteProducts_of_isMulJSet
    {α : Type*} (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i)
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n) (y : ℕ → List (Fin k)) (hy : ∀ t i, i ∈ y t)
    {D : Set (FreeSemigroup α)} (hD : IsMulJSet D) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin n), (∀ m i, Sum.inr i ∈ (w m).head :: (w m).tail) ∧
      (∀ m (a : Fin n → α), (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) (w m) ∈ D) ∧
      ∀ (l : ℕ) (m : Fin (l + 1) → ℕ), StrictMono m →
        ∃ (r : ℕ) (t : Fin (r + 1) → ℕ), StrictMono t ∧
          (List.ofFn fun j => ((w (m j)).head :: (w (m j)).tail).filterMap
              (Sum.elim (fun _ => none) fun i : Fin n =>
                if h : (i : ℕ) < k then some ⟨i, h⟩ else none)).flatten =
            (List.ofFn fun j => y (t j)).flatten

/-- **Variable patterns of variable words in C-sets.** Let $A_0 \subseteq A_1 \subseteq \cdots$
be finite sets with union $A$, and let $S_0$ be the semigroup of nonempty finite words over $A$
under concatenation. Let $1 \le k < n$. An $n$-variable word over $A$ is a nonempty finite word
over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct variables $v_i \notin A$, in which every $v_i$
occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in $A^n$, the word $w(\vec a) \in S_0$ is obtained
from $w$ by replacing each $v_i$ by $a_i$, and $\tau(w)$ is the word over
$\{v_0, \dots, v_{k-1}\}$ obtained from $w$ by deleting the letters of $A$ and the variables $v_i$
with $i \ge k$. Let $y_0, y_1, \dots$ be finite words over $\{v_0, \dots, v_{k-1}\}$ in each of
which every $v_i$ with $i < k$ occurs. If $C \subseteq S_0$ is a $C$-set, then there is a
sequence $w_0, w_1, \dots$ of $n$-variable words over $A$ such that for all $l \in \mathbb{N}$ and
$m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$, the word
$w_{m_0}(\vec a_0) w_{m_1}(\vec a_1) \cdots w_{m_l}(\vec a_l)$ lies in $C$ for all
$\vec a_j \in A_{m_j}^n$, $j = 0, \dots, l$, and there are $r \in \mathbb{N}$ and
$t_0 < t_1 < \cdots < t_r$ in $\mathbb{N}$ with
$\tau(w_{m_0}) \tau(w_{m_1}) \cdots \tau(w_{m_l}) = y_{t_0} y_{t_1} \cdots y_{t_r}$, where
juxtaposition is concatenation of words.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Corollary 3.10. -/
public theorem_wanted exists_variableWords_prod_mem_prod_pattern_mem_finiteProducts_of_isCSet
    {α : Type*} (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i)
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n) (y : ℕ → List (Fin k)) (hy : ∀ t i, i ∈ y t)
    {C : Set (FreeSemigroup α)} (hC : IsCSet C) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin n), (∀ m i, Sum.inr i ∈ (w m).head :: (w m).tail) ∧
      ∀ (l : ℕ) (m : Fin (l + 1) → ℕ), StrictMono m →
        (∀ a : Fin (l + 1) → Fin n → α, (∀ j i, a j i ∈ A (m j)) →
          (List.ofFn fun j : Fin l =>
              FreeSemigroup.map (Sum.elim id (a j.succ)) (w (m j.succ))).foldl
            (· * ·) (FreeSemigroup.map (Sum.elim id (a 0)) (w (m 0))) ∈ C) ∧
        ∃ (r : ℕ) (t : Fin (r + 1) → ℕ), StrictMono t ∧
          (List.ofFn fun j => ((w (m j)).head :: (w (m j)).tail).filterMap
              (Sum.elim (fun _ => none) fun i : Fin n =>
                if h : (i : ℕ) < k then some ⟨i, h⟩ else none)).flatten =
            (List.ofFn fun j => y (t j)).flatten

end

end MetaMathlibExt
