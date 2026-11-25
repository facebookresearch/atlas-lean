/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# (u,l,d)-Motzkin numbers of rank r

Provenance: concept `jis_sem_cc3b9e9ca9863189c52ced84`,
source `jis_source_ed70e97a9239ad812ad2e1c8`
(`schork3.tex`, lines 259-275, statement `jis_a4c8498023ac94f370aead45`).
Boundary evidence only: statement `jis_6323169e4d744a20966ea9c4`.
-/

namespace MetaMathlibExt

@[expose] public section

namespace ULDMotzkin

/-- **Colored Motzkin steps of a given rank.** Let $r$ and $l$ be natural numbers and let
$u, d \colon \{0, \dots, r - 1\} \to \mathbb{N}$. The admissible steps of rank $r$ are the
up-steps $U_j$ with $0 \le j < r$ in one of $u(j)$ colors, the level steps in one of $l$ colors,
and the down-steps $D_j$ with $0 \le j < r$ in one of $d(j)$ colors: the disjoint union of the
sets $\{j\} \times \{0, \dots, u(j) - 1\}$ for $j < r$, the set $\{0, \dots, l - 1\}$, and the
sets $\{j\} \times \{0, \dots, d(j) - 1\}$ for $j < r$.

A step kind with zero colors contributes no steps. The steps $U_j$ and $D_j$ have jump size
$j + 1$, so no up- or down-step has jump size zero.

Source: concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `admissible_steps`,
statement `jis_a4c8498023ac94f370aead45`. -/
abbrev ULDMotzkinStep (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ) : Type :=
  (Σ _j : Fin r, Fin (u _j)) ⊕ Fin l ⊕ (Σ _j : Fin r, Fin (d _j))

/-- **Height change of a colored Motzkin step.** The height change of an admissible step of
rank $r$ is the integer $j + 1$ for an up-step $U_j$ with $0 \le j < r$, $0$ for a level step,
and $-(j + 1)$ for a down-step $D_j$ with $0 \le j < r$, whatever its color.

Source: concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `admissible_steps`,
statement `jis_a4c8498023ac94f370aead45`. -/
def stepHeight (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ)
    (s : ULDMotzkinStep r u l d) : ℤ :=
  match s with
  | Sum.inl ⟨j, _⟩ => ((j.val + 1 : ℕ) : ℤ)
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr ⟨j, _⟩) => -((j.val + 1 : ℕ) : ℤ)

/-- **Height of a colored step sequence after k steps.** For a sequence
$p = (p_0, \dots, p_{n-1})$ of $n$ admissible steps of rank $r$ and a natural number $k$, the
height of $p$ after $k$ steps is the integer $\sum_{i < \min(k, n)} h(p_i)$, where $h$ is the
height change of a step. For $k \ge n$ it is the height of the whole sequence.

Source: concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `paths`,
statement `jis_a4c8498023ac94f370aead45`. -/
def pathHeight (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ) (n : ℕ)
    (p : Fin n → ULDMotzkinStep r u l d) (k : ℕ) : ℤ :=
  Finset.sum (Finset.range k)
    (fun i => if h : i < n then stepHeight r u l d (p ⟨i, h⟩) else 0)

/-- **Colored Motzkin path condition.** Let $r \ge 1$. A sequence
$p = (p_0, \dots, p_{n-1})$ of $n$ admissible steps of rank $r$ is a Motzkin path when its
height after $k$ steps is nonnegative for every $k$ with $0 \le k \le n$ and its height after
$n$ steps is $0$.

Source: concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `paths`,
statement `jis_a4c8498023ac94f370aead45`. -/
def IsMotzkinPath (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ) (_hr : 1 ≤ r)
    (n : ℕ) (p : Fin n → ULDMotzkinStep r u l d) : Prop :=
  (∀ k ∈ Finset.range (n + 1), 0 ≤ pathHeight r u l d n p k) ∧
    pathHeight r u l d n p n = 0

/-- **Colored Motzkin paths of rank r and length n.** For $r \ge 1$ and a natural number $n$,
the colored Motzkin paths of rank $r$ and length $n$ are the sequences
$(p_0, \dots, p_{n-1})$ of $n$ admissible steps of rank $r$ that satisfy the Motzkin path
condition: the height after $k$ steps is nonnegative for every $k \le n$, and the height after
$n$ steps is $0$.

Source: concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `paths`,
statement `jis_a4c8498023ac94f370aead45`. -/
def ULDMotzkinPath (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ) (hr : 1 ≤ r)
    (n : ℕ) : Type :=
  { p : Fin n → ULDMotzkinStep r u l d // IsMotzkinPath r u l d hr n p }

/-- Decidability of the Motzkin path predicate, by computation over the
finite prefix quantification with decidability over the integers.
Concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `paths`,
statement `jis_a4c8498023ac94f370aead45`. -/
instance isMotzkinPathDecPred (r : ℕ) (u : Fin r → ℕ) (l : ℕ)
    (d : Fin r → ℕ) (hr : 1 ≤ r) (n : ℕ) :
    DecidablePred (IsMotzkinPath r u l d hr n) :=
  fun p => by unfold IsMotzkinPath; infer_instance

/-- Finite type of Motzkin paths, via the decidable subtype. Concept
`jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `number`,
statement `jis_a4c8498023ac94f370aead45`. -/
instance uldMotzkinPathFintype (r : ℕ) (u : Fin r → ℕ) (l : ℕ)
    (d : Fin r → ℕ) (hr : 1 ≤ r) (n : ℕ) :
    Fintype (ULDMotzkinPath r u l d hr n) :=
  Subtype.fintype _

/-- **(u,l,d)-Motzkin numbers of rank r.** Let $r \ge 1$ and $l$ be natural numbers and let
$u, d \colon \{0, \dots, r - 1\} \to \mathbb{N}$. For a natural number $n$, the
$(u,l,d)$-Motzkin number of rank $r$ and length $n$ is the number of colored Motzkin paths of
rank $r$ and length $n$ whose up-steps $U_j$ come in $u(j)$ colors, whose level steps come in
$l$ colors, and whose down-steps $D_j$ come in $d(j)$ colors.

Source: concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `number`,
statement `jis_a4c8498023ac94f370aead45`. -/
def uldMotzkinNumber (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ)
    (hr : 1 ≤ r) (n : ℕ) : ℕ :=
  Fintype.card (ULDMotzkinPath r u l d hr n)

/-- **The (u,l,d)-Motzkin number counts Motzkin step sequences.** Let $r \ge 1$ and $l$ be
natural numbers and let $u, d \colon \{0, \dots, r - 1\} \to \mathbb{N}$. For every natural
number $n$, the $(u,l,d)$-Motzkin number of rank $r$ and length $n$ equals the number of
sequences of $n$ admissible steps of rank $r$ with these color counts that satisfy the Motzkin
path condition.

This holds by definition.

Source: concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `number`,
statement `jis_a4c8498023ac94f370aead45`. -/
theorem uldMotzkinNumber_eq_card (r : ℕ) (u : Fin r → ℕ) (l : ℕ)
    (d : Fin r → ℕ) (hr : 1 ≤ r) (n : ℕ) :
    uldMotzkinNumber r u l d hr n =
      Fintype.card { p : Fin n → ULDMotzkinStep r u l d //
        IsMotzkinPath r u l d hr n p } :=
  rfl

end ULDMotzkin

end

end MetaMathlibExt
