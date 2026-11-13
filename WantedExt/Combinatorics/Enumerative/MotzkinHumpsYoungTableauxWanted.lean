/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
import Mathlib.Tactic

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Height change of a Motzkin step.** The three Motzkin steps are encoded as $0 = D$ (down),
$1 = F$ (flat) and $2 = U$ (up). The height change of the step encoded by $s \in \{0, 1, 2\}$
is the integer $s - 1$; thus $D$ changes the height by $-1$, $F$ by $0$ and $U$ by $+1$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def motzkinStep (s : Fin 3) : ℤ := (s.val : ℤ) - 1

/-- **Motzkin prefix.** Let $p = p_0 p_1 \cdots p_{n-1}$ be a word of length $n$ in the steps $D$,
$F$, $U$ (encoded as $0$, $1$, $2$), whose vertical displacements are $-1$, $0$ and $+1$, and let
$h \in \mathbb{Z}$. The word $p$ is a Motzkin prefix ending at height $h$ when, for every natural
number $m \le n$, the sum of the displacements of $p_0, \dots, p_{m-1}$ is nonnegative, and the
sum of the displacements of all $n$ steps is $h$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsMotzkinPrefix (n : ℕ) (h : ℤ) (p : Fin n → Fin 3) : Prop :=
  (∀ m : ℕ, m ≤ n → 0 ≤ ∑ i : Fin n, if i.val < m then motzkinStep (p i) else 0) ∧
  ∑ i : Fin n, motzkinStep (p i) = h

/-- **Motzkin hump.** Let $p = p_0 p_1 \cdots p_{n-1}$ be a word of length $n$ in the steps $D$,
$F$, $U$ (encoded as $0$, $1$, $2$), whose vertical displacements are $-1$, $0$ and $+1$. For
$k \in \mathbb{N}$ and positions $i, j \in \{0, \dots, n-1\}$, the pair $(i, j)$ is a hump of
height $k$ in $p$ when $i < j$, $p_i = U$, $p_j = D$, every $p_r$ with $i < r < j$ is $F$, and the
height after step $i$, that is, the sum of the displacements of $p_0, \dots, p_i$, equals $k$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsMotzkinHump (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  i.val < j.val ∧ motzkinStep (p i) = 1 ∧ motzkinStep (p j) = -1 ∧
  (∀ r : Fin n, i.val < r.val → r.val < j.val → motzkinStep (p r) = 0) ∧
  (∑ r : Fin n, if r.val ≤ i.val then motzkinStep (p r) else 0) = (k : ℤ)

/-- **Unfolding the Motzkin prefix condition.** Let $p = p_0 p_1 \cdots p_{n-1}$ be a word of
length $n$ in the steps $D$, $F$, $U$, whose vertical displacements are $-1$, $0$ and $+1$, and let
$h \in \mathbb{Z}$. Then $p$ is a Motzkin prefix ending at height $h$ if and only if, for every
natural number $m \le n$, the sum of the displacements of $p_0, \dots, p_{m-1}$ is nonnegative,
and the sum of the displacements of all $n$ steps is $h$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isMotzkinPrefix_iff (n : ℕ) (h : ℤ) (p : Fin n → Fin 3) :
    IsMotzkinPrefix n h p ↔
      (∀ m : ℕ, m ≤ n →
        0 ≤ ∑ i : Fin n, if i.val < m then motzkinStep (p i) else 0) ∧
      ∑ i : Fin n, motzkinStep (p i) = h := by
  rfl

/-- **Bounded Motzkin prefix condition.** Let $p = p_0 p_1 \cdots p_{n-1}$ be a word of length $n$
in the steps $D$, $F$, $U$ (encoded as $0$, $1$, $2$), whose vertical displacements are $-1$, $0$
and $+1$, and let $h \in \mathbb{Z}$. The word $p$ satisfies the bounded Motzkin prefix condition
for $h$ when, for every $m \in \{0, 1, \dots, n\}$, the sum of the displacements of
$p_0, \dots, p_{m-1}$ is nonnegative, and the sum of the displacements of all $n$ steps is $h$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsMotzkinPrefixFinite (n : ℕ) (h : ℤ) (p : Fin n → Fin 3) : Prop :=
  (∀ m : Fin (n + 1),
    0 ≤ ∑ i : Fin n, if i.val < m.val then motzkinStep (p i) else 0) ∧
  ∑ i : Fin n, motzkinStep (p i) = h

/-- **Bounded form of the Motzkin prefix condition.** Let $p$ be a word of length $n$ in the steps
$D$, $F$, $U$ and let $h \in \mathbb{Z}$. Then $p$ satisfies the bounded Motzkin prefix condition
for $h$, in which the prefix length $m$ ranges over $\{0, 1, \dots, n\}$, if and only if $p$ is
a Motzkin prefix ending at height $h$, in which $m$ ranges over all natural numbers with
$m \le n$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isMotzkinPrefixFinite_iff (n : ℕ) (h : ℤ) (p : Fin n → Fin 3) :
    IsMotzkinPrefixFinite n h p ↔ IsMotzkinPrefix n h p := by
  constructor
  · intro hp
    refine ⟨?_, hp.2⟩
    intro m hm
    exact hp.1 ⟨m, Nat.lt_succ_iff.mpr hm⟩
  · intro hp
    refine ⟨?_, hp.2⟩
    intro m
    exact hp.1 m.val (Nat.lt_succ_iff.mp m.isLt)

/-- Motzkin-prefix membership is decidable via the equivalent bounded prefix condition.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableIsMotzkinPrefix (n : ℕ) (h : ℤ) (p : Fin n → Fin 3) :
    Decidable (IsMotzkinPrefix n h p) := by
  letI : Decidable (IsMotzkinPrefixFinite n h p) := by
    unfold IsMotzkinPrefixFinite
    infer_instance
  exact decidable_of_iff (IsMotzkinPrefixFinite n h p)
    (isMotzkinPrefixFinite_iff n h p)

/-- **Characterization of Motzkin humps.** Write a path of length $n$ as a sequence of steps
$p_0, \dots, p_{n-1}$, and let $s(p_r) \in \{-1, 0, 1\}$ be the vertical displacement of the
step $p_r$ (down, flat or up). For a natural number $k$ and positions $i, j < n$, the pair
$(i, j)$ is a hump of height $k$ if and only if $i < j$, $s(p_i) = 1$, $s(p_j) = -1$,
$s(p_r) = 0$ for every $r$ with $i < r < j$, and $\sum_{r \le i} s(p_r) = k$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isMotzkinHump_iff (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) :
    IsMotzkinHump n k p i j ↔
      i.val < j.val ∧ motzkinStep (p i) = 1 ∧ motzkinStep (p j) = -1 ∧
      (∀ r : Fin n, i.val < r.val → r.val < j.val → motzkinStep (p r) = 0) ∧
      (∑ r : Fin n, if r.val ≤ i.val then motzkinStep (p r) else 0) = (k : ℤ) := by
  rfl

/-- Hump membership is decidable because all marked positions and intervening steps
range over finite types.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableIsMotzkinHump (n k : ℕ) (p : Fin n → Fin 3)
    (i j : Fin n) : Decidable (IsMotzkinHump n k p i j) := by
  unfold IsMotzkinHump
  infer_instance

/-- **Motzkin peak.** Let $p$ be a word of length $n$ in the steps $D$, $F$, $U$, let
$k \in \mathbb{N}$, and let $i, j \in \{0, \dots, n-1\}$. The pair $(i, j)$ is a peak of height
$k$ in $p$ when it is a hump of height $k$ in $p$ and $j = i + 1$, that is, when the down step
$p_j$ immediately follows the up step $p_i$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsMotzkinPeak (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  IsMotzkinHump n k p i j ∧ i.val + 1 = j.val

/-- **Peaks are humps with adjacent endpoints.** Let $p$ be a word of length $n$ in the steps $D$,
$F$, $U$, let $k \in \mathbb{N}$, and let $i, j \in \{0, \dots, n-1\}$. Then $(i, j)$ is a peak of
height $k$ in $p$ if and only if $(i, j)$ is a hump of height $k$ in $p$ and $j = i + 1$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isMotzkinPeak_iff (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) :
    IsMotzkinPeak n k p i j ↔ IsMotzkinHump n k p i j ∧ i.val + 1 = j.val := by
  rfl

/-- **Paths whose last non-flat step is up.** A word $p = p_0 p_1 \cdots p_{n-1}$ of length $n$
in the steps $U$ (up), $F$ (flat) and $D$ (down) has last non-flat step up when some position
$i$ has $p_i = U$ and every later step $p_j$ with $j > i$ is $F$. In particular, such a word
contains an up step.

Among the Motzkin prefixes of length $n$ ending at height $h$ (words that never go below height
$0$ and end at height $h$), these words form the paper's set $\mathcal{M}^{*U}_{n,h}$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def LastNonflatStepUp (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  ∃ i, p i = 2 ∧ ∀ j, i < j → p j = 1

/-- **Characterization of words whose last non-flat step is up.** Let $p = p_0 p_1 \cdots p_{n-1}$
be a word of length $n$ in the steps $D$, $F$, $U$. Then the last non-flat step of $p$ is $U$ if
and only if there is a position $i$ with $p_i = U$ such that $p_j = F$ for every position $j > i$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem lastNonflatStepUp_iff (n : ℕ) (p : Fin n → Fin 3) :
    LastNonflatStepUp n p ↔ ∃ i, p i = 2 ∧ ∀ j, i < j → p j = 1 := by
  rfl

/-- **Paths whose first non-up step is down.** Write a path of length $n$ as a sequence of steps
$p_0, \dots, p_{n-1}$, each $D$ (down), $F$ (flat) or $U$ (up), encoded as $0$, $1$, $2$. The
path has first non-up step down when there is a position $i$ with $p_i = D$ and $p_j = U$ for
every $j < i$. In particular, a path all of whose steps are up steps, including the empty path,
does not qualify.

For a Motzkin prefix ending at height $h$, this is membership in the paper's set
$\mathcal{M}^{D*}_{n,h}$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def FirstNonupStepDown (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  ∃ i, p i = 0 ∧ ∀ j, j < i → p j = 2

/-- **Characterization of paths whose first non-up step is down.** Write a path of length $n$ as
a sequence of steps $p_0, \dots, p_{n-1}$, each $D$ (down), $F$ (flat) or $U$ (up), encoded as
$0$, $1$, $2$. The path has first non-up step $D$ if and only if there is a position $i$ with
$p_i = D$ and $p_j = U$ for every $j < i$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem firstNonupStepDown_iff (n : ℕ) (p : Fin n → Fin 3) :
    FirstNonupStepDown n p ↔ ∃ i, p i = 0 ∧ ∀ j, j < i → p j = 2 := by
  rfl

/-- **Paths ending with an up step.** Write a path of length $n$ as a sequence of steps
$p_0, \dots, p_{n-1}$, each $D$ (down), $F$ (flat) or $U$ (up), encoded as $0$, $1$, $2$. The
path ends with an up step when it has a last position, that is, some $i < n$ with $i + 1 = n$,
and $p_i = U$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public def EndsWithUp (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  ∃ i, i.val + 1 = n ∧ p i = 2

/-- **Characterization of paths ending with an up step.** Write a path of length $n$ as a
sequence of steps $p_0, \dots, p_{n-1}$, each $D$ (down), $F$ (flat) or $U$ (up), encoded as
$0$, $1$, $2$. The path ends with an up step if and only if there is a position $i < n$ with
$i + 1 = n$ and $p_i = U$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public theorem endsWithUp_iff (n : ℕ) (p : Fin n → Fin 3) :
    EndsWithUp n p ↔ ∃ i, i.val + 1 = n ∧ p i = 2 := by
  rfl

/-- **Number of humps of a given height in Motzkin paths.** A Motzkin path of length $n$ is a
word of $n$ steps $U = (1,1)$, $F = (1,0)$ and $D = (1,-1)$ that ends at height $0$ and never
goes below height $0$. A hump of height $k$ in such a path is a pair consisting of an up step
and a later down step with only flat steps between them, where the up step ends at height $k$.
For natural numbers $n$ and $k$, $H_{n,k}$ is the number of pairs $(P, h)$ with $P$ a Motzkin
path of length $n$ and $h$ a hump of height $k$ in $P$, that is, the number of Motzkin paths of
length $n$ with one distinguished hump of height $k$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def motzkinHumpCount (n k : ℕ) : ℕ :=
  Fintype.card {q : (Fin n → Fin 3) × Fin n × Fin n //
    IsMotzkinPrefix n 0 q.1 ∧ IsMotzkinHump n k q.1 q.2.1 q.2.2}

/-- A computationally shallow expansion of `H_{n,k}` that enumerates the path and
the two marked positions in nested indicator sums.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def motzkinHumpCountExpanded (n k : ℕ) : ℕ :=
  ∑ p : Fin n → Fin 3, ∑ i : Fin n, ∑ j : Fin n,
    if IsMotzkinPrefix n 0 p ∧ IsMotzkinHump n k p i j then 1 else 0

/-- The nested indicator expansion computes the defining distinguished-hump cardinality.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private theorem motzkinHumpCount_eq_expanded (n k : ℕ) :
    motzkinHumpCount n k = motzkinHumpCountExpanded n k := by
  classical
  rw [motzkinHumpCount, Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  rfl

/-- **Motzkin generating function.** The Motzkin series is the formal power series
$M(x) = \sum_{n \ge 0} m_n x^n$ in $\mathbb{Z}[[x]]$, where $m_n$ is the $n$-th Motzkin number.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def motzkinSeries : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (motzkinNumber n : ℤ))

/-- **Standard Young tableau.** A standard Young tableau of order $n$ is encoded by a map $T$ that
assigns to each entry $i \in \{0, \dots, n-1\}$ a cell $T(i) = (r_i, c_i)$ with row and column
indices in $\{0, \dots, n-1\}$. The map $T$ is a standard Young tableau when it is injective
and, for every entry $i$ and every cell $(r, c)$ with $r \le r_i$ and $c \le c_i$, there is an
entry $j \le i$ with $T(j) = (r, c)$.

It follows that for every $m \le n$ the cells of the entries $0, \dots, m-1$ form a Young
diagram, and that entries increase strictly along rows and down columns.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsStandardYoungTableau (n : ℕ) (T : Fin n → Fin n × Fin n) : Prop :=
  Function.Injective T ∧
    ∀ i c, c.1 ≤ (T i).1 → c.2 ≤ (T i).2 → ∃ j, j ≤ i ∧ T j = c

/-- **Unfolding the standard Young tableau condition.** Let $T$ assign to each entry
$i \in \{0, \dots, n-1\}$ a cell $T(i) = (r_i, c_i)$ with row and column indices in
$\{0, \dots, n-1\}$. Then $T$ is a standard Young tableau of order $n$ if and only if $T$ is
injective and, for every entry $i$ and every cell $(r, c)$ with $r \le r_i$ and $c \le c_i$,
there is an entry $j \le i$ with $T(j) = (r, c)$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isStandardYoungTableau_iff (n : ℕ) (T : Fin n → Fin n × Fin n) :
    IsStandardYoungTableau n T ↔
      Function.Injective T ∧
        ∀ i c, c.1 ≤ (T i).1 → c.2 ≤ (T i).2 → ∃ j, j ≤ i ∧ T j = c := by
  rfl

/-- Membership in the finite-cell SYT encoding is decidable by finite quantification.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableIsStandardYoungTableau (n : ℕ)
    (T : Fin n → Fin n × Fin n) : Decidable (IsStandardYoungTableau n T) := by
  unfold IsStandardYoungTableau Function.Injective
  infer_instance

/-- **Tableaux in the $(2,1)$-hook.** Let $T$ assign to each entry $i < n$ a cell $(r_i, c_i)$
with zero-based row $r_i < n$ and column $c_i < n$. Then $T$ lies in the $(2,1)$-hook when no
entry occupies a cell whose row is at least $2$ and whose column is at least $1$, that is, when
no $i$ has both $r_i \ge 2$ and $c_i \ge 1$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsInTwoOneHook (n : ℕ) (T : Fin n → Fin n × Fin n) : Prop :=
  ∀ i, ¬(2 ≤ (T i).1.val ∧ 1 ≤ (T i).2.val)

/-- **Characterization of tableaux in the $(2,1)$-hook.** Let $T$ assign to each entry $i < n$ a
cell $(r_i, c_i)$ with zero-based row $r_i < n$ and column $c_i < n$. Then $T$ lies in the
$(2,1)$-hook if and only if for no entry $i$ do both $r_i \ge 2$ and $c_i \ge 1$ hold.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isInTwoOneHook_iff (n : ℕ) (T : Fin n → Fin n × Fin n) :
    IsInTwoOneHook n T ↔ ∀ i, ¬(2 ≤ (T i).1.val ∧ 1 ≤ (T i).2.val) := by
  rfl

/-- Membership in the `(2,1)`-hook is decidable by inspecting the finitely many entries.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableIsInTwoOneHook (n : ℕ) (T : Fin n → Fin n × Fin n) :
    Decidable (IsInTwoOneHook n T) := by
  unfold IsInTwoOneHook
  infer_instance

/-- **Row length of a tableau.** For a natural number $n$, let $T$ assign to each entry
$i \in \{0, \dots, n-1\}$ a cell $T(i)$, given by a zero-based row index and a zero-based column
index, both in $\{0, \dots, n-1\}$. For a natural number $r$, the length of row $r$ is the number
of entries $i$ whose cell $T(i)$ lies in row $r$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def tableauRowLength (n : ℕ) (T : Fin n → Fin n × Fin n) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (T i).1.val = r).card

/-- **First-two-row difference of a tableau.** Let $T$ assign to each entry $i < n$ a cell
$(r_i, c_i)$ with zero-based row $r_i < n$ and column $c_i < n$, and let $\lambda_1$ and
$\lambda_2$ be the numbers of entries $i$ with $r_i = 0$ and with $r_i = 1$ respectively. For a
natural number $k$, $T$ has first-two-row difference $k$ when $\lambda_1 = \lambda_2 + k$, that
is, when $\lambda_1 - \lambda_2 = k$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def HasFirstTwoRowDifference (n k : ℕ) (T : Fin n → Fin n × Fin n) : Prop :=
  tableauRowLength n T 0 = tableauRowLength n T 1 + k

/-- **Characterization of the first-two-row difference.** Let $T$ assign to each entry $i < n$ a
cell $(r_i, c_i)$ with zero-based row $r_i < n$ and column $c_i < n$, and let $\lambda_1$ and
$\lambda_2$ be the numbers of entries $i$ with $r_i = 0$ and with $r_i = 1$ respectively. For a
natural number $k$, $T$ has first-two-row difference $k$ if and only if
$\lambda_1 = \lambda_2 + k$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem hasFirstTwoRowDifference_iff (n k : ℕ) (T : Fin n → Fin n × Fin n) :
    HasFirstTwoRowDifference n k T ↔
      tableauRowLength n T 0 = tableauRowLength n T 1 + k := by
  rfl

/-- The first-two-row cardinality equation is decidable.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableHasFirstTwoRowDifference (n k : ℕ)
    (T : Fin n → Fin n × Fin n) : Decidable (HasFirstTwoRowDifference n k T) := by
  unfold HasFirstTwoRowDifference
  infer_instance

/-- **Standard Young tableaux in the $(2,1)$-hook with given row difference.** For natural numbers
$n$ and $k$, $\mathrm{SYT}_k(2,1;n)$ is the number of standard Young tableaux of order $n$ whose
shape $\lambda$ lies in the $(2,1)$-hook, that is $\lambda_3 \le 1$, and whose first two row
lengths satisfy $\lambda_1 = \lambda_2 + k$ (a missing row has length $0$).

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def sytHookCount (n k : ℕ) : ℕ :=
  Fintype.card {T : Fin n → Fin n × Fin n //
    IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧ HasFirstTwoRowDifference n k T}

/-- A cell-valued map is equivalently the pair of its row and column coordinate maps.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def tableauCoordinateEquiv (n : ℕ) :
    (Fin n → Fin n × Fin n) ≃ (Fin n → Fin n) × (Fin n → Fin n) where
  toFun T := (fun i => (T i).1, fun i => (T i).2)
  invFun rc := fun i => (rc.1 i, rc.2 i)
  left_inv T := by
    funext i
    exact Prod.eta (T i)
  right_inv rc := by
    exact Prod.ext (by rfl) (by rfl)

/-- Restricting `tableauCoordinateEquiv` gives an equivalence between valid tableaux
and pairs of coordinate maps satisfying the same tableau predicate.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def sytHookSubtypeEquiv (n k : ℕ) :
    {T : Fin n → Fin n × Fin n //
      IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧ HasFirstTwoRowDifference n k T} ≃
    {rc : (Fin n → Fin n) × (Fin n → Fin n) //
      let T := fun i => (rc.1 i, rc.2 i)
      IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧
        HasFirstTwoRowDifference n k T} where
  toFun T := ⟨tableauCoordinateEquiv n T.val, by simpa [tableauCoordinateEquiv] using T.property⟩
  invFun rc := ⟨(tableauCoordinateEquiv n).symm rc.val, by
    simpa [tableauCoordinateEquiv] using rc.property⟩
  left_inv T := by
    apply Subtype.ext
    exact (tableauCoordinateEquiv n).left_inv T.val
  right_inv rc := by
    apply Subtype.ext
    exact (tableauCoordinateEquiv n).right_inv rc.val

/-- A computationally shallow expansion of `SYT_k(2,1;n)` that independently
enumerates the row and column coordinate maps.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def sytHookCountExpanded (n k : ℕ) : ℕ :=
  ∑ rows : Fin n → Fin n, ∑ cols : Fin n → Fin n,
    let T := fun i => (rows i, cols i)
    if IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧
        HasFirstTwoRowDifference n k T then 1 else 0

/-- The nested coordinate-map expansion computes the defining SYT cardinality.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private theorem sytHookCount_eq_expanded (n k : ℕ) :
    sytHookCount n k = sytHookCountExpanded n k := by
  classical
  rw [sytHookCount, Fintype.card_congr (sytHookSubtypeEquiv n k),
    Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  rfl

/-- **Motzkin paths with a marked hump, over all heights.** For a natural number $n$, this is
the set of triples $(k, P, h)$ where $k$ is a natural number with
$1 \le k \le \lfloor n/2 \rfloor$, $P$ is a Motzkin path of length $n$ (a word of $n$ steps
$U = (1,1)$, $F = (1,0)$ and $D = (1,-1)$ that ends at height $0$ and never goes below height
$0$), and $h$ is a hump of height $k$ in $P$: an up step and a later down step with only flat
steps between them, where the up step ends at height $k$, recorded by the positions of its two
steps.

This is the paper's disjoint union $\bigcup_{1 \le k \le \lfloor n/2 \rfloor} \mathcal{H}_{n,k}$,
keeping the height index $k$ with each marked path.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public def MotzkinHumpFamily (n : ℕ) :=
  {q : ℕ × ((Fin n → Fin 3) × Fin n × Fin n) //
    1 ≤ q.1 ∧ q.1 ≤ n / 2 ∧ IsMotzkinPrefix n 0 q.2.1 ∧
      IsMotzkinHump n q.1 q.2.1 q.2.2.1 q.2.2.2}

/-- **Motzkin prefixes of even height whose last non-flat step is up.** Use the steps
$U = (1,1)$, $F = (1,0)$ and $D = (1,-1)$, and call a word in these steps a Motzkin prefix if
none of its initial segments ends below height $0$. For a natural number $n$, this is the set
of pairs $(k, p)$ where $k$ is a natural number with $1 \le k \le \lfloor n/2 \rfloor$ and $p$
is a Motzkin prefix of length $n$ ending at height $2k$ that contains a $U$ after which every
step is $F$.

This is the paper's disjoint union
$\bigcup_{1 \le k \le \lfloor n/2 \rfloor} \mathcal{M}^{*U}_{n,2k}$, keeping the index $k$ with
each path.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public def MotzkinLastUpEvenFamily (n : ℕ) :=
  {q : ℕ × (Fin n → Fin 3) //
    1 ≤ q.1 ∧ q.1 ≤ n / 2 ∧ IsMotzkinPrefix n (2 * q.1) q.2 ∧
      LastNonflatStepUp n q.2}

/-- **Motzkin prefixes whose first non-up step is down.** Use the steps $U = (1,1)$,
$F = (1,0)$ and $D = (1,-1)$, and call a word in these steps a Motzkin prefix if none of its
initial segments ends below height $0$. For a natural number $n$, this is the set of pairs
$(k, p)$ where $k$ is a natural number with $k \le n - 2$ and $p$ is a Motzkin prefix of length
$n$ ending at height $k$ whose first step other than $U$ exists and is $D$.

This is the paper's disjoint union $\bigcup_{0 \le k \le n-2} \mathcal{M}^{D*}_{n,k}$, keeping
the index $k$ with each path.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 6 (`jis-2025-25.8.1-lem-6`).
-/
public def MotzkinFirstDownFamily (n : ℕ) :=
  {q : ℕ × (Fin n → Fin 3) //
    q.1 + 2 ≤ n ∧ IsMotzkinPrefix n q.1 q.2 ∧ FirstNonupStepDown n q.2}

/-- **Hook tableaux of order 3 with row difference 1.** The number $\mathrm{SYT}_1(2,1;3)$ of
standard Young tableaux of order $3$ in the $(2,1)$-hook whose first row is longer than its
second row by exactly $1$ equals $2$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Initial-values table.
-/
public theorem sytHookCount_three_one : sytHookCount 3 1 = 2 := by
  rw [sytHookCount_eq_expanded]
  decide

/-- **Hook tableaux of order 3 with row difference 0.** The number $\mathrm{SYT}_0(2,1;3)$ of
standard Young tableaux of order $3$ in the $(2,1)$-hook whose first two rows have the same
length equals $1$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Initial-values table.
-/
public theorem sytHookCount_three_zero : sytHookCount 3 0 = 1 := by
  rw [sytHookCount_eq_expanded]
  decide

/-- **Hook tableaux of order 2 with row difference 1.** The number $\mathrm{SYT}_1(2,1;2)$ of
standard Young tableaux of order $2$ in the $(2,1)$-hook whose first row is longer than its
second row by exactly $1$ equals $0$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Initial-values table.
-/
public theorem sytHookCount_two_one : sytHookCount 2 1 = 0 := by
  rw [sytHookCount_eq_expanded]
  decide

/-- **Humps of height one in Motzkin paths of length four.** Let $H_{n,k}$ be the number of
pairs $(P, h)$ where $P$ is a Motzkin path of length $n$ and $h$ is a hump of height $k$ in $P$,
that is, an up step and a later down step with only flat steps between them, where the up step
ends at height $k$. Then $H_{4,1} = 8$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Hump-count table.
-/
public theorem motzkinHumpCount_four_one : motzkinHumpCount 4 1 = 8 := by
  rw [motzkinHumpCount_eq_expanded]
  decide

/-- **Closed formula for hook tableau counts.** For natural numbers $n$ and $k$ with
$k + 2 \le n$, let $\mathrm{SYT}_k(2,1;n)$ be the number of standard Young tableaux of order $n$
in the $(2,1)$-hook whose first row is longer than its second row by exactly $k$. Then, as an
identity of rational numbers,
$$
\mathrm{SYT}_k(2,1;n) = (-1)^{n+k} + \sum_{i=0}^{\lfloor (n-k-1)/2 \rfloor}
\sum_{\substack{0 \le j \le n-k-1-2i \\ j \equiv n+k-1 \pmod 2}}
\frac{2k+2}{n+k+1-2i-j} \binom{n-2i-2}{j} \binom{n-2i-j-1}{\frac{n+k-j-1}{2} - i}.
$$

When $k = 0$ and $2i = n - 1$, the upper argument $n - 2i - 2$ would be $-1$; it is read as $0$,
so the only term of that inner sum, $j = 0$, has binomial factor $\binom{0}{0} = 1$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Theorem 2 (`jis-2025-25.8.1-thm-2`).
-/
public theorem_wanted sytHookCount_closedForm (n k : ℕ) (hk : k + 2 ≤ n) :
    (sytHookCount n k : ℚ) =
      (-1 : ℚ) ^ (n + k) +
        ∑ i ∈ Finset.range ((n - k - 1) / 2 + 1),
          ∑ j ∈ Finset.range (n - k - 1 - 2 * i + 1),
            (if j % 2 = (n + k - 1) % 2 then (1 : ℚ) else 0) *
              ((2 * k + 2 : ℕ) : ℚ) / ((n + k + 1 - 2 * i - j : ℕ) : ℚ) *
              (Nat.choose (n - 2 * i - 2) j : ℚ) *
              (Nat.choose (n - 2 * i - j - 1) ((n + k - j - 1) / 2 - i) : ℚ)

/-- **Humps correspond to last-up prefixes of twice the height.** Use the steps $U = (1,1)$,
$F = (1,0)$ and $D = (1,-1)$. A Motzkin prefix of length $n$ ending at height $h$ is a word of
$n$ steps that never goes below height $0$ and ends at height $h$; a Motzkin path is a Motzkin
prefix ending at height $0$. A hump of height $k$ in a path is a pair of an up step and a later
down step with only flat steps between them, where the up step ends at height $k$; the hump is
a peak when the down step immediately follows the up step. For every natural number $n$ there
is a bijection from the set of triples $(k, P, h)$ with $1 \le k \le \lfloor n/2 \rfloor$, $P$
a Motzkin path of length $n$ and $h$ a hump of height $k$ in $P$, to the set of pairs $(k, p)$
with $1 \le k \le \lfloor n/2 \rfloor$ and $p$ a Motzkin prefix of length $n$ ending at height
$2k$ that contains a $U$ after which every step is $F$. This bijection keeps the index $k$, and
the hump $h$ is a peak exactly when the image path $p$ ends with an up step.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public theorem_wanted motzkinHumpFamily_equiv_lastUpEvenFamily (n : ℕ) :
    ∃ e : MotzkinHumpFamily n ≃ MotzkinLastUpEvenFamily n,
      (∀ q, (e q).val.1 = q.val.1) ∧
        ∀ q, IsMotzkinPeak n q.val.1 q.val.2.1 q.val.2.2.1 q.val.2.2.2 ↔
          EndsWithUp n (e q).val.2

/-- **Generating function for humps of a fixed height.** Let $H_{n,k}$ be the number of pairs
$(P, h)$ where $P$ is a Motzkin path of length $n$ and $h$ is a hump of height $k$ in $P$ (an up
step and a later down step with only flat steps between them, the up step ending at height
$k$), and let $M(x) = \sum_{n \ge 0} m_n x^n$, where $m_n$ is the $n$-th Motzkin number. For
every integer $k \ge 1$, in the ring $\mathbb{Z}[[x]]$ of formal power series,
$$(1 - x) \sum_{n \ge 2k} H_{n,k} \, x^n = x^{2k} M(x)^{2k}.$$

The source also states this result in Riordan-array form.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Corollary 5 (`jis-2025-25.8.1-cor-5`).
-/
public theorem_wanted motzkinHumpCount_generatingFunction (k : ℕ) (hk : 1 ≤ k) :
    (1 - (PowerSeries.X : PowerSeries ℤ)) *
        PowerSeries.mk (fun n => if 2 * k ≤ n then (motzkinHumpCount n k : ℤ) else 0) =
      PowerSeries.X ^ (2 * k) * motzkinSeries ^ (2 * k)

/-- **A bijection between first-down and even-height last-up Motzkin prefixes.** Use the steps
$U = (1,1)$, $F = (1,0)$ and $D = (1,-1)$, and call a word in these steps a Motzkin prefix if
none of its initial segments ends below height $0$. For every natural number $n$ there is a
bijection between the set of pairs $(k, p)$, where $k$ is a natural number with $k + 2 \le n$ and
$p$ is a Motzkin prefix of length $n$ ending at height $k$ whose first step other than $U$ exists
and is $D$, and the set of pairs $(k, p)$, where $k$ is a natural number with
$1 \le k \le \lfloor n/2 \rfloor$ and $p$ is a Motzkin prefix of length $n$ ending at height $2k$
that contains a $U$ after which every step is $F$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 6 (`jis-2025-25.8.1-lem-6`).
-/
public theorem_wanted motzkinFirstDownFamily_equiv_lastUpEvenFamily (n : ℕ) :
    Nonempty (MotzkinFirstDownFamily n ≃ MotzkinLastUpEvenFamily n)

/-- **Generating function for the adjusted $(2,1)$-hook tableau counts.** Let $k$ be a natural
number, and let $\mathrm{SYT}_k(2,1;n)$ be the number of standard Young tableaux with $n$ cells
in the $(2,1)$-hook whose first two rows differ in length by $k$. Set
$T_{n,k} = \mathrm{SYT}_k(2,1;n) + (-1)^{n+k+1}$ for $n \ge k$ and $T_{n,k} = 0$ for $n < k$, and
let $M(x) = \sum_{n \ge 0} m_n x^n$ be the generating function of the Motzkin numbers $m_n$.
Then in the ring $\mathbb{Z}[[x]]$ of formal power series

$$(1 + x) \sum_{n \ge 0} T_{n,k} x^n = (x M(x))^{k+1}.$$

Equivalently, $\sum_{n \ge k} T_{n,k} x^n = x^{k+1} M(x)^{k+1} / (1 + x)$; the identity is
stated without division.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 7 (`jis-2025-25.8.1-lem-7`).
-/
public theorem_wanted adjustedSytHookCount_generatingFunction (k : ℕ) :
    (1 + (PowerSeries.X : PowerSeries ℤ)) *
        PowerSeries.mk (fun n =>
          if k ≤ n then (sytHookCount n k : ℤ) + (-1 : ℤ) ^ (n + k + 1) else 0) =
      (PowerSeries.X * motzkinSeries) ^ (k + 1)

/-- **Generating function for hook tableau counts.** For a natural number $k$, let
$\mathrm{SYT}_k(2,1;n)$ be the number of standard Young tableaux of order $n$ in the
$(2,1)$-hook whose first row is longer than its second row by exactly $k$, and let
$M(x) = \sum_{n \ge 0} m_n x^n$ be the generating function of the Motzkin numbers $m_n$. Then,
in the ring of formal power series with integer coefficients,
$$
(1 + x) \sum_{n \ge k} \mathrm{SYT}_k(2,1;n)\, x^n = x^k \bigl(1 + x\, M(x)^{k+1}\bigr).
$$

The factor $1 + x$ is cleared, so the identity involves no division.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Corollary 9 (`jis-2025-25.8.1-cor-9`).
-/
public theorem_wanted sytHookCount_generatingFunction (k : ℕ) :
    (1 + (PowerSeries.X : PowerSeries ℤ)) *
        PowerSeries.mk (fun n => if k ≤ n then (sytHookCount n k : ℤ) else 0) =
      PowerSeries.X ^ k * (1 + PowerSeries.X * motzkinSeries ^ (k + 1))

/-- **Hook tableau counts as differences of hump counts.** For natural numbers $m$ and $j$, let
$\mathrm{SYT}_j(2,1;m)$ be the number of standard Young tableaux of order $m$ in the
$(2,1)$-hook whose first row is longer than its second row by exactly $j$, and let $H_{m,j}$ be
the number of Motzkin paths of length $m$ with one distinguished hump of height $j$ (a hump is
an up step followed by flat steps and then a down step; its height is the height reached by the
up step). For natural numbers $n$ and $k$ with $1 \le k \le \lfloor n/2 \rfloor$,
$$
\mathrm{SYT}_{2k-1}(2,1;n+1) + \mathrm{SYT}_{2k-1}(2,1;n) = H_{n+1,k} - H_{n,k},
$$
where the subtraction is taken in the integers.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Corollary 10 (`jis-2025-25.8.1-cor-10`).
-/
public theorem_wanted sytHookCount_add_eq_humpCount_sub (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n / 2) :
    (sytHookCount (n + 1) (2 * k - 1) : ℤ) + (sytHookCount n (2 * k - 1) : ℤ) =
      (motzkinHumpCount (n + 1) k : ℤ) - (motzkinHumpCount n k : ℤ)

end

end MetaMathlibExt
