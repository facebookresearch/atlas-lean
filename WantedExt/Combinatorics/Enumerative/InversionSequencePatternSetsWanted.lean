/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Inversion sequences avoiding sets of length-3 patterns

Statements from Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*,
INTEGERS 24 (2024), Article A76.

An inversion sequence of length `n` is `e : Fin n → ℕ` with `e i ≤ i` (zero-based
`e₀ e₁ ⋯ e_{n-1}`). It contains a pattern `p : Fin 3 → ℕ` (written as a digit string, `101` is
`![1, 0, 1]`) when some subsequence `e_a e_b e_c`, `a < b < c`, is order-isomorphic to `p`.
`I_n(B)` is the set of length-`n` inversion sequences avoiding every pattern in `B`, two pattern
sets are I-Wilf-equivalent (`A ∼ B`) when `|I_n(A)| = |I_n(B)|` for all `n`, and
`F_B(x) = ∑_{n ≥ 1} |I_n(B)| xⁿ`.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **Containment of a length-3 pattern.** A sequence $e = e_0 e_1 \cdots e_{n-1}$ of natural
numbers contains the length-3 pattern $p = p_0 p_1 p_2$ of natural numbers when there are
positions $i_0 < i_1 < i_2$ in $\{0, \dots, n - 1\}$ such that, for all $a, b \in \{0, 1, 2\}$,
$e_{i_a} < e_{i_b}$ if and only if $p_a < p_b$; that is, the subsequence $e_{i_0} e_{i_1} e_{i_2}$
is order-isomorphic to $p$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
def InvSeqContainsPattern {n : ℕ} (e : Fin n → ℕ) (p : Fin 3 → ℕ) : Prop :=
  ∃ f : Fin 3 ↪o Fin n, ∀ a b, e (f a) < e (f b) ↔ p a < p b

/-- **Short sequences contain no length-3 pattern.** If $n < 3$, then no sequence
$e_0 e_1 \cdots e_{n-1}$ of natural numbers contains a length-3 pattern $p$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
theorem not_invSeqContainsPattern_of_lt {n : ℕ} (hn : n < 3) (e : Fin n → ℕ)
    (p : Fin 3 → ℕ) : ¬ InvSeqContainsPattern e p := by
  rintro ⟨f, -⟩
  have := Fintype.card_le_of_embedding f.toEmbedding
  simp at this
  omega

/-- **Number of inversion sequences avoiding a set of patterns.** An inversion sequence of length
$n$ is a sequence $e = e_0 e_1 \cdots e_{n-1}$ of natural numbers with $e_i \le i$ for every $i$.
It contains a length-3 pattern $p = p_0 p_1 p_2$ (a triple of natural numbers) when some
subsequence $e_a e_b e_c$ with $a < b < c$ is order-isomorphic to $p$. For a set $B$ of length-3
patterns, $|I_n(B)|$ is the number of inversion sequences of length $n$ that contain no pattern
of $B$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
noncomputable def invSeqAvoidCount (B : Set (Fin 3 → ℕ)) (n : ℕ) : ℕ :=
  Nat.card {e : Fin n → ℕ // (∀ i, e i ≤ i) ∧ ∀ p ∈ B, ¬ InvSeqContainsPattern e p}

/-- **One inversion sequence of length one.** For every set $B$ of length-3 patterns, the number
$|I_1(B)|$ of inversion sequences of length one that avoid every pattern in $B$ equals $1$: the
only inversion sequence of length one is $0$, and it avoids every length-3 pattern.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
theorem invSeqAvoidCount_one (B : Set (Fin 3 → ℕ)) : invSeqAvoidCount B 1 = 1 := by
  rw [invSeqAvoidCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun e e' => Subtype.ext (funext fun i => ?_)⟩, ⟨⟨fun _ => 0, ?_⟩⟩⟩
  · have h := e.2.1 i
    have h' := e'.2.1 i
    have hi : (i : ℕ) = 0 := by omega
    omega
  · exact ⟨fun i => Nat.zero_le _, fun p _ => not_invSeqContainsPattern_of_lt (by omega) _ p⟩

/-- **Generating function of inversion sequences avoiding a set of patterns.** For a set $B$ of
length-3 patterns, $F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n$ is the formal power series in
$\mathbb{Q}[[x]]$ with constant coefficient $0$ whose coefficient of $x^n$, for $n \ge 1$, is the
number $|I_n(B)|$ of inversion sequences of length $n$ that avoid every pattern in $B$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Section 2. -/
noncomputable def invSeqAvoidGF (B : Set (Fin 3 → ℕ)) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (invSeqAvoidCount B n : ℚ)

/-- **Coefficients of the generating function of pattern-avoiding inversion sequences.** For
every set $B$ of length-3 patterns and every $n \ge 0$, the generating function
$F_B(x) = \sum_{m \ge 1} |I_m(B)| x^m \in \mathbb{Q}[[x]]$ has constant coefficient $0$, and its
coefficient of $x^{n+1}$ is $|I_{n+1}(B)|$, the number of inversion sequences of length $n + 1$
that avoid every pattern in $B$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Section 2. -/
theorem coeff_invSeqAvoidGF (B : Set (Fin 3 → ℕ)) (n : ℕ) :
    coeff 0 (invSeqAvoidGF B) = 0 ∧
      coeff (n + 1) (invSeqAvoidGF B) = (invSeqAvoidCount B (n + 1) : ℚ) := by
  simp [invSeqAvoidGF]

/-- **I-Wilf equivalence of $\{000, 010, 100, 101, 120\}$ and $\{000, 010, 100, 110, 120\}$.**
Write length-3 patterns as digit strings ($101$ is the pattern $(1, 0, 1)$) and let $|I_n(B)|$ be
the number of inversion sequences of length $n$ that avoid every pattern in the set $B$. Then for
every $n \ge 0$, $|I_n(\{000, 010, 100, 101, 120\})| = |I_n(\{000, 010, 100, 110, 120\})|$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 4 (`integers-2024-A76-thm-4`). -/
public theorem_wanted invSeq_wilf_000_010_100_120_101_110 :
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0]}
          : Set (Fin 3 → ℕ))

/-- **Three I-Wilf-equivalent sets of five patterns containing $000$, $010$ and $120$.** Write
length-3 patterns as digit strings ($101$ is the pattern $(1, 0, 1)$) and let $|I_n(B)|$ be the
number of inversion sequences of length $n$ that avoid every pattern in the set $B$. For
$B_1 = \{000, 010, 101, 120, 201\}$, $B_2 = \{000, 010, 101, 120, 210\}$ and
$B_3 = \{000, 010, 110, 120, 210\}$, and for every $n \ge 0$,
$|I_n(B_1)| = |I_n(B_2)| = |I_n(B_3)|$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 5 (`integers-2024-A76-thm-5`). -/
public theorem_wanted invSeq_wilf_000_010_120_five_class :
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **Inversion sequences avoiding $\{011, 102, 120\}$.** Let $B = \{011, 102, 120\}$, where a
pattern is written as a digit string ($101$ is the triple $(1, 0, 1)$), and let
$F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $B$. Then
$$(1 - 2x)^2 F_B(x) = x(1 - x)^2.$$

Since $(1 - 2x)^2$ is a unit in $\mathbb{Q}[[x]]$, this says $F_B(x) = x(1 - x)^2/(1 - 2x)^2$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 6 (`integers-2024-A76-thm-6`). -/
public theorem_wanted invSeqAvoidGF_011_102_120 :
    (1 - 2 * X) ^ 2 * invSeqAvoidGF ({![0, 1, 1], ![1, 0, 2], ![1, 2, 0]} : Set (Fin 3 → ℕ)) =
      X * (1 - X) ^ 2

/-- **Three I-Wilf-equivalent sets of five patterns containing $000$, $102$ and $120$.** Write
length-3 patterns as digit strings ($101$ is the pattern $(1, 0, 1)$) and let $|I_n(B)|$ be the
number of inversion sequences of length $n$ that avoid every pattern in the set $B$. For
$B_1 = \{000, 101, 102, 120, 201\}$, $B_2 = \{000, 101, 102, 120, 210\}$ and
$B_3 = \{000, 102, 110, 120, 210\}$, and for every $n \ge 0$,
$|I_n(B_1)| = |I_n(B_2)| = |I_n(B_3)|$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 7 (`integers-2024-A76-thm-7`). -/
public theorem_wanted invSeq_wilf_000_102_120_five_class :
    invSeqAvoidCount ({![0, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **Two I-Wilf equivalences exchanging $201$ and $210$ in five-pattern sets.** Write
length-3 patterns as digit strings ($101$ is the pattern $(1, 0, 1)$) and let $|I_n(B)|$ be the
number of inversion sequences of length $n$ that avoid every pattern in the set $B$. For a pattern
$\tau$ let $A_\tau = \{000, 100, 101, 120, \tau\}$ and $B_\tau = \{000, 100, 110, 120, \tau\}$.
Then for every $n \ge 0$, $|I_n(A_{201})| = |I_n(A_{210})|$ and $|I_n(B_{201})| = |I_n(B_{210})|$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 8 (`integers-2024-A76-thm-8`). -/
public theorem_wanted invSeq_wilf_000_100_120_201_210 :
    invSeqAvoidCount ({![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **I-Wilf equivalences among five-pattern sets containing $010$, $102$ and $120$.** Write
length-3 patterns as digit strings ($101$ is the pattern $(1, 0, 1)$) and let $|I_n(B)|$ be the
number of inversion sequences of length $n$ that avoid every pattern in the set $B$. For a pattern
$\tau$ let $A_\tau = \{010, \tau, 102, 120, 201\}$ and $A'_\tau = \{010, \tau, 102, 120, 210\}$,
and let $B = \{010, 101, 102, 120, 201\}$. Then for every $n \ge 0$,
$|I_n(A_{100})| = |I_n(A_{110})|$ and
$|I_n(A'_{100})| = |I_n(A'_{101})| = |I_n(A'_{110})| = |I_n(B)|$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 9 (`integers-2024-A76-thm-9`). -/
public theorem_wanted invSeq_wilf_010_102_120_five_classes :
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 1, 0], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 1, 0], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 1, 0], ![1, 1, 0], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
          : Set (Fin 3 → ℕ))

/-- **I-Wilf equivalence of $\{010, 100, 101, 120, 201\}$ and $\{010, 100, 101, 120, 210\}$.**
Write length-3 patterns as digit strings ($101$ is the pattern $(1, 0, 1)$) and let $|I_n(B)|$ be
the number of inversion sequences of length $n$ that avoid every pattern in the set $B$. Then for
every $n \ge 0$, $|I_n(\{010, 100, 101, 120, 201\})| = |I_n(\{010, 100, 101, 120, 210\})|$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 11 (`integers-2024-A76-thm-11`). -/
public theorem_wanted invSeq_wilf_010_100_101_120_201_210 :
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **Five I-Wilf-equivalent sets of six patterns containing $000$, $010$ and $120$.** Write
length-3 patterns as digit strings ($101$ is the pattern $(1, 0, 1)$) and let $|I_n(B)|$ be the
number of inversion sequences of length $n$ that avoid every pattern in the set $B$. For a pattern
$\tau$ let $A_\tau = \{000, 010, 100, 101, 120, \tau\}$ and $B_\tau = \{000, 010, 100, 110, 120,
\tau\}$, and let $C = \{000, 010, 101, 110, 120, 201\}$. Then for every $n \ge 0$,
$|I_n(A_{201})| = |I_n(A_{210})| = |I_n(B_{201})| = |I_n(B_{210})| = |I_n(C)|$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 13 (`integers-2024-A76-thm-13`). -/
public theorem_wanted invSeq_wilf_000_010_120_six_class :
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 1], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1]}
          : Set (Fin 3 → ℕ))

/-- **Three I-Wilf-equivalent six-pattern sets containing 102 and 110.** Write a length-3 pattern
as the word of its values, so $101$ is the pattern $(1, 0, 1)$, and for a set $B$ of patterns let
$|I_n(B)|$ be the number of inversion sequences of length $n$ that avoid every pattern in $B$.
Let $A_\tau = \{011, 101, 102, 110, 120, \tau\}$ and $C = \{011, 021, 102, 110, 201, 210\}$.
Then $|I_n(A_{201})| = |I_n(A_{210})| = |I_n(C)|$ for every $n \ge 0$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 14 (`integers-2024-A76-thm-14`). -/
public theorem_wanted invSeq_wilf_102_110_six_class :
    invSeqAvoidCount ({![0, 1, 1], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 1], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 1, 1], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 1], ![0, 2, 1], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **A common generating function for three sets of seven patterns.** Let
$B_1 = \{010, 011, 100, 101, 102, 201, 210\}$, $B_2 = \{010, 011, 100, 102, 110, 201, 210\}$ and
$B_3 = \{010, 011, 101, 102, 110, 201, 210\}$, where a pattern is written as a digit string ($101$
is the triple $(1, 0, 1)$). For a set $B$ of patterns let
$F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $B$. Then for each $j \in \{1, 2, 3\}$,
$$(1 - x)(1 - 2x)^2 F_{B_j}(x) = x(1 - 2x)^2 + x^2(1 - x)^2.$$

Since $(1 - x)(1 - 2x)^2$ is a unit in $\mathbb{Q}[[x]]$, this says
$F_{B_j}(x) = x/(1 - x) + x^2(1 - x)/(1 - 2x)^2$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 16 (`integers-2024-A76-thm-16`). -/
public theorem_wanted invSeqAvoidGF_010_011_102_201_210_seven :
    ∀ B : Set (Fin 3 → ℕ),
      (B = {![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]} ∨
        B = {![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]} ∨
        B = {![0, 1, 0], ![0, 1, 1], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}) →
      (1 - X) * (1 - 2 * X) ^ 2 * invSeqAvoidGF B =
        X * (1 - 2 * X) ^ 2 + X ^ 2 * (1 - X) ^ 2

/-- **Eight-pattern sets differing in 201 and 210: equivalence and generating function.** Write a
length-3 pattern as the word of its values, so $101$ is the pattern $(1, 0, 1)$. For a set $B$ of
patterns let $|I_n(B)|$ be the number of inversion sequences of length $n$ that avoid every
pattern in $B$, and let $F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B_\tau = \{000, 010, 100, 101, 102, 110, 120, \tau\}$. Then $|I_n(B_{201})| = |I_n(B_{210})|$
for every $n \ge 0$, and for every power series $s \in \mathbb{Q}[[x]]$ with constant term $1$
and $s^2 = 1 - 2x - 3x^2$,
$$
2x^3 (1 + x)(x^2 + 2x + 2) F_{B_{201}}(x) =
1 - x^2 - 4x^3 - 7x^4 - 5x^5 - 2x^6 - (1 + x + 2x^2 + 2x^3 + x^4) s.
$$

This is the paper's closed form for $F_{B_{201}}$ with the denominator cleared, where $s$ plays
the role of $\sqrt{1 - 2x - 3x^2}$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 17 (`integers-2024-A76-thm-17`). -/
public theorem_wanted invSeq_wilf_eight_201_210_and_gf :
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0],
        ![1, 2, 0], ![2, 0, 1]} : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0],
        ![1, 2, 0], ![2, 1, 0]} : Set (Fin 3 → ℕ)) ∧
    ∀ s : ℚ⟦X⟧, constantCoeff s = 1 → s ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
      2 * X ^ 3 * (1 + X) * (X ^ 2 + 2 * X + 2) *
          invSeqAvoidGF ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0],
            ![1, 2, 0], ![2, 0, 1]} : Set (Fin 3 → ℕ)) =
        1 - X ^ 2 - 4 * X ^ 3 - 7 * X ^ 4 - 5 * X ^ 5 - 2 * X ^ 6 -
          (1 + X + 2 * X ^ 2 + 2 * X ^ 3 + X ^ 4) * s

/-- **A common generating function for three sets of eight patterns.** Let
$B_1 = \{000, 010, 100, 101, 102, 120, 201, 210\}$,
$B_2 = \{000, 010, 100, 102, 110, 120, 201, 210\}$ and
$B_3 = \{000, 010, 101, 102, 110, 120, 201, 210\}$, where a pattern is written as a digit string
($101$ is the triple $(1, 0, 1)$). For a set $B$ of patterns let
$F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $B$. For each $j \in \{1, 2, 3\}$ and every power
series $s \in \mathbb{Q}[[x]]$ with constant term $1$ and $s^2 = 1 - 2x - 3x^2$,
$$x^2 F_{B_j}(x) = 1 - 2x - x^2 + x^3 - (1 - x) s.$$

This is the closed form $F_{B_j}(x) = (1 - 2x - x^2 + x^3 - (1 - x)\sqrt{1 - 2x - 3x^2}) / x^2$
with the denominator cleared, $s$ standing for $\sqrt{1 - 2x - 3x^2}$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 18 (`integers-2024-A76-thm-18`). -/
public theorem_wanted invSeqAvoidGF_eight_radical_three :
    ∀ B : Set (Fin 3 → ℕ),
      (B = {![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1],
          ![2, 1, 0]} ∨
        B = {![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1],
          ![2, 1, 0]} ∨
        B = {![0, 0, 0], ![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1],
          ![2, 1, 0]}) →
      ∀ s : ℚ⟦X⟧, constantCoeff s = 1 → s ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
        X ^ 2 * invSeqAvoidGF B = 1 - 2 * X - X ^ 2 + X ^ 3 - (1 - X) * s

/-- **Inversion sequences avoiding $\{000, 100, 101, 102, 110, 120, 201, 210\}$.** Let
$B = \{000, 100, 101, 102, 110, 120, 201, 210\}$, where a pattern is written as a digit string
($101$ is the triple $(1, 0, 1)$), and let
$F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $B$. For every power series $s \in \mathbb{Q}[[x]]$
with constant term $1$ and $s^2 = 1 - 2x - 3x^2$,
$$2x^2(1 + x) F_B(x) = 2 - 2x - 5x^2 - x^3 - (2 - x^2) s.$$

This is the closed form
$F_B(x) = (2 - 2x - 5x^2 - x^3 - (2 - x^2)\sqrt{1 - 2x - 3x^2}) / (2x^2(1 + x))$ with the
denominator cleared, $s$ standing for $\sqrt{1 - 2x - 3x^2}$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 21 (`integers-2024-A76-thm-21`). -/
public theorem_wanted invSeqAvoidGF_000_100_101_102_110_120_201_210 :
    ∀ s : ℚ⟦X⟧, constantCoeff s = 1 → s ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
      2 * X ^ 2 * (1 + X) *
          invSeqAvoidGF ({![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0],
            ![2, 0, 1], ![2, 1, 0]} : Set (Fin 3 → ℕ)) =
        2 - 2 * X - 5 * X ^ 2 - X ^ 3 - (2 - X ^ 2) * s

/-- **Inversion sequences avoiding nine patterns.** Let
$B = \{000, 010, 100, 101, 102, 110, 120, 201, 210\}$, where a pattern is written as a digit
string ($101$ is the triple $(1, 0, 1)$), and let
$F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $B$. For every power series $s \in \mathbb{Q}[[x]]$
with constant term $1$ and $s^2 = 1 - 2x - 3x^2$,
$$2x^2(1 + x) F_B(x) = 2 - 3x - 3x^2 + (x - 2) s.$$

This is the closed form
$F_B(x) = (2 - 3x - 3x^2 + (x - 2)\sqrt{1 - 2x - 3x^2}) / (2x^2(1 + x))$ with the denominator
cleared, $s$ standing for $\sqrt{1 - 2x - 3x^2}$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 22 (`integers-2024-A76-thm-22`). -/
public theorem_wanted invSeqAvoidGF_nine_patterns :
    ∀ s : ℚ⟦X⟧, constantCoeff s = 1 → s ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
      2 * X ^ 2 * (1 + X) *
          invSeqAvoidGF ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0],
            ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]} : Set (Fin 3 → ℕ)) =
        2 - 3 * X - 3 * X ^ 2 + (X - 2) * s

/-- **Number of I-Wilf classes of sets of length-3 patterns.** Let $P$ be the set of the thirteen
length-3 patterns $000, 001, 010, 011, 012, 021, 100, 101, 102, 110, 120, 201, 210$, each written
as the word of its values. For $B \subseteq P$ let $|I_n(B)|$ be the number of inversion sequences
of length $n$ that avoid every pattern in $B$, and let $w_d$ be the number of distinct sequences
$(|I_n(B)|)_{n \ge 0}$ as $B$ ranges over the $d$-element subsets of $P$ (the number of
I-Wilf-equivalence classes of such sets). Then $w_5 = 219$, $w_6 = 167$, $w_7 = 105$, $w_8 = 61$,
$w_9 = 35$, $w_{10} = 21$, $w_{11} = 10$, $w_{12} = 4$ and $w_{13} = 1$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 1 (`integers-2024-A76-thm-1`). -/
public theorem_wanted invSeq_wilfClassCount :
    let P : Finset (Fin 3 → ℕ) := {![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2],
      ![0, 2, 1], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1],
      ![2, 1, 0]}
    let w : ℕ → ℕ := fun d =>
      Nat.card ↥((fun B : Finset (Fin 3 → ℕ) => invSeqAvoidCount (B : Set (Fin 3 → ℕ))) ''
        (P.powersetCard d : Set (Finset (Fin 3 → ℕ))))
    w 5 = 219 ∧ w 6 = 167 ∧ w 7 = 105 ∧ w 8 = 61 ∧ w 9 = 35 ∧ w 10 = 21 ∧ w 11 = 10 ∧
      w 12 = 4 ∧ w 13 = 1

/-- **Reducible sets of length-3 patterns for inversion sequences.** An inversion sequence of
length $n$ is a sequence $e_0 e_1 \cdots e_{n-1}$ of natural numbers with $e_i \le i$ for all $i$;
write a length-3 pattern as a digit string ($101$ is the pattern $(1, 0, 1)$). For each pair
$(C, \tau)$ listed below and every $n$, every inversion sequence of length $n$ that avoids every
pattern in $C$ also avoids $\tau$, so $C \cup \{\tau\}$ and $C$ are avoided by the same inversion
sequences. The pairs are: $C = \{001\}$ with $\tau \in \{101, 102, 201\}$;
$C = \{011\}$ with $\tau \in \{101, 110\}$; $C = \{012\}$ with $\tau \in \{102, 120\}$;
$C = \{021\}$ with $\tau \in \{201, 210\}$; $C = \{000, 001\}$ with $\tau = 100$;
$C = \{000, 011\}$ with $\tau \in \{100, 201, 210\}$;
$C = \{000, 012\}$ with $\tau \in \{201, 210\}$; $C = \{000, 021\}$ with $\tau = 100$;
$C = \{001, 010\}$ with $\tau \in \{021, 100, 110, 120, 210\}$;
$C = \{001, 011\}$ with $\tau = 021$; $C = \{001, 012\}$ with $\tau = 021$;
$C = \{001, 110\}$ with $\tau = 210$; $C = \{001, 120\}$ with $\tau = 210$;
$C = \{010, 011\}$ with $\tau = 100$; $C = \{010, 012\}$ with $\tau \in \{101, 201\}$;
$C = \{010, 021\}$ with $\tau \in \{100, 101, 102, 110, 120\}$;
$C = \{001, 011, 012\}$ with $\tau = 210$; $C = \{001, 011, 100\}$ with $\tau = 210$; and
$C = \{001, 012, 100\}$ with $\tau = 210$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 2 (`integers-2024-A76-thm-2`). -/
public theorem_wanted invSeq_reducible_pattern_sets :
    ∀ Cτ ∈ ([(({![0, 0, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 0, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 2]),
        (({![0, 0, 1]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 1, 0]),
        (({![0, 1, 2]} : Set (Fin 3 → ℕ)), ![1, 0, 2]),
        (({![0, 1, 2]} : Set (Fin 3 → ℕ)), ![1, 2, 0]),
        (({![0, 2, 1]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 2, 1]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 0], ![0, 0, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 0, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 0, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![0, 2, 1]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![1, 1, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![1, 2, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![0, 2, 1]),
        (({![0, 0, 1], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![0, 2, 1]),
        (({![0, 0, 1], ![1, 1, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![1, 2, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 1, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 1, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 1, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 2]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 1, 0]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 2, 0]),
        (({![0, 0, 1], ![0, 1, 1], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![0, 1, 1], ![1, 0, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![0, 1, 2], ![1, 0, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0])]
      : List (Set (Fin 3 → ℕ) × (Fin 3 → ℕ))),
      ∀ (n : ℕ) (e : Fin n → ℕ), (∀ i, e i ≤ i) → (∀ p ∈ Cτ.1, ¬ InvSeqContainsPattern e p) →
        ¬ InvSeqContainsPattern e Cτ.2

/-- **A Catalan generating function for two sets of five patterns.** Let
$B = \{010, 101, 102, 201, 210\}$ and $B' = \{011, 101, 110, 201, 210\}$, where a pattern is
written as a digit string ($101$ is the triple $(1, 0, 1)$). For a set $A$ of patterns let
$F_A(x) = \sum_{n \ge 1} |I_n(A)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $A$, and let $C(x) = \sum_{n \ge 0} C_n x^n$ be the
generating function of the Catalan numbers $C_n = \binom{2n}{n}/(n + 1)$. Then $F_B = F_{B'}$
and
$$(1 - x)(2 - C(x)) F_B(x) = x.$$

Since $C(x) = (1 - \sqrt{1 - 4x})/(2x)$ and $(1 - x)(2 - C(x))$ is a unit in $\mathbb{Q}[[x]]$,
this says $F_B(x) = F_{B'}(x) = x / ((1 - x)(2 - (1 - \sqrt{1 - 4x})/(2x)))$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 3 (`integers-2024-A76-thm-3`). -/
public theorem_wanted invSeqAvoidGF_010_101_102_201_210_catalan :
    invSeqAvoidGF ({![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]} : Set (Fin 3 → ℕ)) =
        invSeqAvoidGF ({![0, 1, 1], ![1, 0, 1], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}
            : Set (Fin 3 → ℕ)) ∧
      (1 - X) * (2 - PowerSeries.mk fun n => (catalan n : ℚ)) *
          invSeqAvoidGF ({![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]}
              : Set (Fin 3 → ℕ)) = X

/-- **I-Wilf-equivalence of 101 and 110 alongside 102, 120, 210.** Write a length-3 pattern as the
word of its values, so $101$ is the pattern $(1, 0, 1)$, and for a set $S$ of patterns let
$|I_n(S)|$ be the number of inversion sequences of length $n$ that avoid every pattern in $S$.
Let $B_\tau = \{100, \tau, 102, 120, 210\}$ and $C_\tau = \{\tau, 102, 120, 201, 210\}$. Then for
every $n \ge 0$, $|I_n(B_{101})| = |I_n(B_{110})|$ and $|I_n(C_{101})| = |I_n(C_{110})|$.

The paper's Theorem 10 also claims $|I_n(A_{101})| = |I_n(A_{110})|$ for all $n$, where
$A_\tau = \{100, \tau, 102, 120, 201\}$; that claim is false, since for $n = 6$ the two counts
are $206$ and $205$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 10 (`integers-2024-A76-thm-10`). -/
public theorem_wanted invSeq_wilf_102_120_101_110_parts_B_C :
    invSeqAvoidCount ({![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![1, 0, 0], ![1, 1, 0], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![1, 1, 0], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **I-Wilf-equivalence of 101 and 110 alongside 010, 120, 201, 210.** Write a length-3 pattern
as the word of its values, so $101$ is the pattern $(1, 0, 1)$, and for a set $B$ of patterns let
$|I_n(B)|$ be the number of inversion sequences of length $n$ that avoid every pattern in $B$.
For every $n \ge 0$,
$$|I_n(\{010, 101, 120, 201, 210\})| = |I_n(\{010, 110, 120, 201, 210\})|.$$

The paper's Theorem 12 also claims this equality for $\{100, 101, 120, 201, 210\}$ and
$\{100, 110, 120, 201, 210\}$; that claim is false, since for $n = 5$ the two counts are $79$
and $81$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 12 (`integers-2024-A76-thm-12`). -/
public theorem_wanted invSeq_wilf_010_120_201_210_101_110 :
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **Exchanging $201$ and $210$ in $\{010, 100, 101, 102, 120, 201\}$.** Write length-3
patterns as digit strings ($101$ is the pattern $(1, 0, 1)$) and let $|I_n(B)|$ be the number of
inversion sequences of length $n$ that avoid every pattern in the set $B$. For a pattern $\tau$
let $A_\tau = \{010, 100, 101, 102, 120, \tau\}$. Then for every $n \ge 0$,
$|I_n(A_{201})| = |I_n(A_{210})|$.

The source further claims $|I_n(A_{210})| = |I_n(B)| = |I_n(C)|$ for all $n$, with
$B = \{010, 100, 110, 102, 120, 201\}$ and $C = \{010, 101, 110, 102, 120, 210\}$; these claims are
false as printed ($|I_7| = 538, 537, 539$ for $A_{210}$, $B$, $C$) and are omitted.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 15 (`integers-2024-A76-thm-15`). -/
public theorem_wanted invSeq_wilf_010_100_101_102_120_201_210 :
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

end

end MetaMathlibExt
