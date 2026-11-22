/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Alternating sequences of sum- and difference-dominated sets

Statements from Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller
and Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88 (arXiv:2509.12829). Journal labels: Lemma 1,
Theorems 1-3 are arXiv Lemma 2.4 and Theorems 2.1, 2.3, 2.5.

A finite set `A ⊆ ℤ` is MSTD (sum-dominated) when `|A + A| > |A - A|` and MDTS
(difference-dominated) when `|A - A| > |A + A|`; both are written out with Mathlib's pointwise
`Finset` operations.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Int.Interval

namespace MetaMathlibExt

@[expose] public section

open Pointwise

/-- **Sums and differences of an interval with one point removed.** Let $m$ and $r$ be integers
with $m \ge 4$ and $2 \le r \le m - 3$, and let $B = \{0, 1, \dots, m - 1\} \setminus \{r\}$. Then
the sumset $B + B = \{b + b' : b, b' \in B\}$ is $\{0, 1, \dots, 2m - 2\}$ and the difference set
$B - B = \{b - b' : b, b' \in B\}$ is the set of integers from $-(m - 1)$ to $m - 1$.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Lemma 1 (`integers-2026-A88-lem-1`). -/
public theorem_wanted interval_erase_add_sub {m r : ℤ} (hm : 4 ≤ m) (hr : 2 ≤ r)
    (hrm : r ≤ m - 3) :
    (Finset.Icc 0 (m - 1)).erase r + (Finset.Icc 0 (m - 1)).erase r = Finset.Icc 0 (2 * m - 2) ∧
      (Finset.Icc 0 (m - 1)).erase r - (Finset.Icc 0 (m - 1)).erase r =
        Finset.Icc (-(m - 1)) (m - 1)

/-- **Alternating sum- and difference-dominated sets from shifted copies.** For a set $S$ of
integers write $S + S = \{s + s' : s, s' \in S\}$ and $S - S = \{s - s' : s, s' \in S\}$. Let $A_1$
be a finite set of integers with $|A_1 - A_1| < |A_1 + A_1|$ and $0 \in A_1$, and let $n$ be an
integer with $0 \le a < n$ for every $a \in A_1$. Suppose that (a) $A_1 + A_1$ and $A_1 - A_1$
meet the same number of residue classes modulo $n$, and (b) with
$x = \#\{a \in A_1 : n + a \notin A_1 + A_1\}$ and $y = \#\{b \in A_1 : n - b \notin A_1 - A_1\}$
we have $2y - x - 1 > |A_1 + A_1| - |A_1 - A_1|$. Let $A_1, A_2, A_3, \dots$ be finite sets of
integers, starting with this $A_1$, such that for every $l \ge 1$, $A_{2l} = A_{2l-1} \cup \{ln\}$
and $A_{2l+1} = A_{2l-1} \cup \{a + ln : a \in A_1\}$. Then for every $l \ge 1$,
$|A_{2l} + A_{2l}| < |A_{2l} - A_{2l}|$, $|A_{2l+1} - A_{2l+1}| < |A_{2l+1} + A_{2l+1}|$ and
$A_{2l-1} \subsetneq A_{2l} \subsetneq A_{2l+1}$.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Theorem 1 (`integers-2026-A88-thm-1`). -/
public theorem_wanted alternating_sequence_of_copies (A₁ : Finset ℤ) (n : ℤ)
    (hmstd : (A₁ - A₁).card < (A₁ + A₁).card) (h0 : 0 ∈ A₁) (hn : ∀ a ∈ A₁, 0 ≤ a ∧ a < n)
    (hmod : ((A₁ + A₁).image (· % n)).card = ((A₁ - A₁).image (· % n)).card)
    (hxy : 2 * ((A₁.filter fun b => n - b ∉ A₁ - A₁).card : ℤ) -
        (A₁.filter fun a => n + a ∉ A₁ + A₁).card - 1 >
      ((A₁ + A₁).card : ℤ) - (A₁ - A₁).card)
    (A : ℕ → Finset ℤ) (h1 : A 1 = A₁)
    (heven : ∀ l ≥ 1, A (2 * l) = A (2 * l - 1) ∪ {(l : ℤ) * n})
    (hodd : ∀ l ≥ 1, A (2 * l + 1) = A (2 * l - 1) ∪ (A₁ + {(l : ℤ) * n})) :
    ∀ l ≥ 1, (A (2 * l) + A (2 * l)).card < (A (2 * l) - A (2 * l)).card ∧
      (A (2 * l + 1) - A (2 * l + 1)).card < (A (2 * l + 1) + A (2 * l + 1)).card ∧
      A (2 * l - 1) ⊂ A (2 * l) ∧ A (2 * l) ⊂ A (2 * l + 1)

/-- **Nathanson's sum-dominated set.** For a set $S$ of integers write
$S + S = \{s + s' : s, s' \in S\}$ and $S - S = \{s - s' : s, s' \in S\}$. Let $m$, $d$, $k$ be
integers with $m \ge 4$, $1 \le d \le m - 1$ and $2d \ne m$, and suppose $k \ge 3$ if $2d < m$
and $k \ge 4$ if $2d > m$. Let $B = \{0, 1, \dots, m - 1\} \setminus \{d\}$,
$L = \{jm - d : 1 \le j \le k\}$, $A^* = B \cup L \cup \{(k + 1)m - 2d - b : b \in B\}$ and
$A = A^* \cup \{m\}$. Then $|A - A| < |A + A|$, $2m \in A + A$, $2m \notin A^* + A^*$, and
$\{a - m : a \in A^*\} \subseteq A^* - A^*$.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Theorem 2 (`integers-2026-A88-thm-2`). -/
public theorem_wanted nathanson_mstd_construction {m d k : ℤ} (hm : 4 ≤ m) (hd : 1 ≤ d)
    (hdm : d ≤ m - 1) (hd2 : 2 * d ≠ m) (hk3 : 2 * d < m → 3 ≤ k) (hk4 : m < 2 * d → 4 ≤ k) :
    let B := (Finset.Icc 0 (m - 1)).erase d
    let As := B ∪ (Finset.Icc 1 k).image (fun j => j * m - d) ∪
      B.image (fun b => (k + 1) * m - 2 * d - b)
    let A := insert m As
    (A - A).card < (A + A).card ∧ 2 * m ∈ A + A ∧ 2 * m ∉ As + As ∧ As - {m} ⊆ As - As

/-- **Alternating sum- and difference-dominated sets from Nathanson's construction.** For a set
$S$ of integers write $S + S = \{s + s' : s, s' \in S\}$, $S - S = \{s - s' : s, s' \in S\}$,
$c + S = \{c + s : s \in S\}$ and $c - S = \{c - s : s \in S\}$. Let $m$, $d$, $k$ be integers with
$m \ge 4$, $m \equiv 0 \pmod 4$ and $4d = m$ or $4d = 3m$, and suppose $k \ge 3$ if $2d < m$ and
$k \ge 4$ if $2d > m$. Let $B = \{0, 1, \dots, m - 1\} \setminus \{d\}$,
$L = \{jm - d : 1 \le j \le k\}$ and $A^* = B \cup L \cup \{(k + 1)m - 2d - b : b \in B\}$. Let
$A_1, A_2, A_3, \dots$ be finite sets of integers with $A_1 = A^* \cup \{m, -d, (k + 1)m - d\}$
and, for every $r \ge 1$, $A_{2r} = A_{2r-1} \cup \{(k + r + 1)m - d\}$ and
$A_{2r+1} = A_{2r-1} \cup \{-rm - d, (k + r + 1)m - d\}$. Then $|A_1 - A_1| < |A_1 + A_1|$, and
for every $r \ge 1$, writing $A'_{2r-1} = A_{2r-1} \setminus \{m\}$: we have
$|A_{2r} + A_{2r}| < |A_{2r} - A_{2r}|$ and $|A_{2r+1} - A_{2r+1}| < |A_{2r+1} + A_{2r+1}|$;
$A_{2r-1} \subsetneq A_{2r} \subsetneq A_{2r+1}$; $m + A'_{2r-1} \subseteq A'_{2r-1} + A'_{2r-1}$
and $m - A'_{2r-1} \subseteq A'_{2r-1} - A'_{2r-1}$;
$|A_{2r-1} + A_{2r-1}| = |A_{2r-1} - A_{2r-1}| + 1$; and
$|A_{2r} + A_{2r}| \le |A_{2r} - A_{2r}| - m + 3$.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Theorem 3 (`integers-2026-A88-thm-3`). -/
public theorem_wanted alternating_sequence_from_nathanson {m d k : ℤ} (hm : 4 ≤ m)
    (hm4 : m % 4 = 0) (hd : 4 * d = m ∨ 4 * d = 3 * m) (hk3 : 2 * d < m → 3 ≤ k)
    (hk4 : m < 2 * d → 4 ≤ k) (A : ℕ → Finset ℤ)
    (h1 : A 1 = insert (-d) (insert ((k + 1) * m - d) (insert m
      ((Finset.Icc 0 (m - 1)).erase d ∪ (Finset.Icc 1 k).image (fun j => j * m - d) ∪
        ((Finset.Icc 0 (m - 1)).erase d).image (fun b => (k + 1) * m - 2 * d - b)))))
    (heven : ∀ r ≥ 1, A (2 * r) = insert ((k + r + 1) * m - d) (A (2 * r - 1)))
    (hodd : ∀ r ≥ 1, A (2 * r + 1) =
      insert (-(r : ℤ) * m - d) (insert ((k + r + 1) * m - d) (A (2 * r - 1)))) :
    (A 1 - A 1).card < (A 1 + A 1).card ∧
    ∀ r ≥ 1, (A (2 * r) + A (2 * r)).card < (A (2 * r) - A (2 * r)).card ∧
      (A (2 * r + 1) - A (2 * r + 1)).card < (A (2 * r + 1) + A (2 * r + 1)).card ∧
      A (2 * r - 1) ⊂ A (2 * r) ∧ A (2 * r) ⊂ A (2 * r + 1) ∧
      {m} + (A (2 * r - 1)).erase m ⊆ (A (2 * r - 1)).erase m + (A (2 * r - 1)).erase m ∧
      {m} - (A (2 * r - 1)).erase m ⊆ (A (2 * r - 1)).erase m - (A (2 * r - 1)).erase m ∧
      (A (2 * r - 1) + A (2 * r - 1)).card = (A (2 * r - 1) - A (2 * r - 1)).card + 1 ∧
      ((A (2 * r) + A (2 * r)).card : ℤ) ≤ (A (2 * r) - A (2 * r)).card - m + 3

end

end MetaMathlibExt
