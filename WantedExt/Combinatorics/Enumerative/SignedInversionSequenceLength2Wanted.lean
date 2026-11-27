/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2BarredPrefix
public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2BarredSuffix
public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2ClassC3
public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2ClassC38
public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2ClassC45
public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2FirstBarCount
public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2FirstBars
public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2Harmonic
public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2LastBars

/-!
# Signed inversion sequences avoiding sets of length-2 signed patterns

Statements from Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of
Length-2 Signed Patterns*, INTEGERS 26 (2026), Article A74.

A signed inversion sequence of length `n` is `e₁ ⋯ eₙ` with `e_{i+1} ∈ {0, 0̄, 1, 1̄, …, i, ī}`;
here it is `e : Fin n → ℕ × Bool` with `(e i).1 ≤ i` (zero-based positions), the second
component recording a bar. A length-2 signed pattern is one of `00`, `01`, `10` with each letter
possibly barred (twelve patterns); `e` contains it when some `i < j` has `|e_i| |e_j|`
order-isomorphic to `|τ₁| |τ₂|` and `e_i`, `e_j` barred exactly when `τ₁`, `τ₂` are. `Ī_n(B)` is
the set of length-`n` signed inversion sequences avoiding every pattern of `B`, `B ∼ C`
(Wilf-equivalence) means `|Ī_n(B)| = |Ī_n(C)|` for all `n ≥ 0`, and
`F_B(x) = ∑_{n ≥ 0} |Ī_n(B)| xⁿ`. In the declarations, the paper's pattern `1̄0` is
`⟨.gt, true, false⟩`, `0̄1̄` is `⟨.lt, true, true⟩`, `00̄` is `⟨.eq, false, true⟩`, and so on.
-/

namespace MetaMathlibExt

open Nat PowerSeries

@[expose] public section

/-- **Mansour–Safadi Lemma 1 (signed patterns 0̄1̄, 0̄0, 01).** A signed inversion sequence of
length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1, \dots, k - 1,
\overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$, $01$, $10$,
each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as $|\tau_1|$,
$|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write $\bar I_n(B)$ for the
set of signed inversion sequences of length $n$ that avoid every pattern in $B$, and
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)|\,x^n$ in $\mathbb{Q}[[x]]$. Let
$B_1 = \{\bar 0\bar 1, \bar 0 0, 01\}$ and $B_2 = \{\bar 0\bar 1, \bar 0 1, 01\}$. Then
$|\bar I_n(B_1)| = |\bar I_n(B_2)|$ for every $n \ge 0$, and $(1 - 3x + x^2)\,F_{B_1}(x) = 1 - x$,
that is, $F_{B_1}(x) = (1 - x)/(1 - 3x + x^2)$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 1 (`integers-2026-A74-lem-1`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b00_01 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, false⟩} ∧
    (1 - 3 * X + X ^ 2) * signedInvAvoidGF {⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, false⟩} = 1 - X

/-- **Wilf-equivalence and count for {0̄0̄, 0̄0, 01̄} (Lemma 2).** Write a length-2 signed pattern
as $\tau_1\tau_2$, where $00$, $01$ and $10$ record whether $|\tau_1|$ is equal to, smaller than
or larger than $|\tau_2|$ and a bar marks a barred letter, and write $|\bar I_n(B)|$ for the
number of signed inversion sequences of length $n$ avoiding every pattern of a set $B$ of such
patterns. Let $B = \lbrace \bar 0\bar 0, \bar 0 0, 0\bar 1 \rbrace$ and
$C = \lbrace \bar 0 0, \bar 0 1, 0\bar 1 \rbrace$. Then $B$ and $C$ are Wilf-equivalent, that is,
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and for every $n \ge 0$,
$$
|\bar I_n(B)| = 1 + \sum_{j=0}^{n-1} (2j + 1)\, j!.
$$

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 2 (`integers-2026-A74-lem-2`). -/
public theorem_wanted signedInvSeq_wilf_and_count_b0b0_b00_0b1 :
    signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩} ∧
    ∀ n, signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} n =
        1 + ∑ j ∈ Finset.range n, (2 * j + 1) * j !

/-- **Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, 01\}$.** For a set $B$ of
length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of signed
inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar1, 01\}$ and $C = \{\bar10, \bar0\bar1, 01\}$. Then
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and
$$
(1 - 2x)(1 - 3x + x^2)(1 - x)^2 F_B(x) = (1 - 2x)(1 - 3x + x^2)(1 - x)^2 + x(1 - x)^4 +
x(1 - x + x^2)(1 - 3x + x^2),
$$
that is,
$F_B(x) = 1 + \frac{x(1 - x)^2}{(1 - 2x)(1 - 3x + x^2)} + \frac{x(1 - x + x^2)}{(1 - 2x)(1 - x)^2}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 5 (`integers-2026-A74-lem-5`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, false, false⟩} ∧
    (1 - 2 * X) * (1 - 3 * X + X ^ 2) * (1 - X) ^ 2 * signedInvAvoidGF {⟨.gt, true, true⟩,
        ⟨.lt, true, true⟩, ⟨.lt, false, false⟩} =
      (1 - 2 * X) * (1 - 3 * X + X ^ 2) * (1 - X) ^ 2 + X * (1 - X) ^ 4 +
        X * (1 - X + X ^ 2) * (1 - 3 * X + X ^ 2)

/-- **Mansour–Safadi Lemma 6.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}\bar{0}, \bar{0}1\})| =
|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}0, \bar{0}1\})|$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 6 (`integers-2026-A74-lem-6`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b0_b01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩}

/-- **Mansour–Safadi Lemma 7.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{1}0, \bar{0}\bar{1}, \bar{0}\bar{0}\})| =
|\bar{I}_n(\{\bar{1}0, \bar{0}\bar{1}, \bar{0}0\})|$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 7 (`integers-2026-A74-lem-7`). -/
public theorem_wanted signedInvSeq_wilf_b10_b0b1_b0b0 :
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩}

/-- **Eight signed-pattern triples with (n + 1)! avoiders (Lemma 8).** Write a length-2 signed
pattern as $\tau_1\tau_2$, where $00$, $01$ and $10$ record whether $|\tau_1|$ is equal to, smaller
than or larger than $|\tau_2|$ and a bar marks a barred letter, and write $|\bar I_n(B)|$ for the
number of signed inversion sequences of length $n$ avoiding every pattern of a set $B$ of such
patterns. For every $n \ge 0$ and each of the eight sets
$B = \lbrace \bar 1\bar 0, \bar 0\bar 1, \bar 0\bar 0 \rbrace$,
$\lbrace \bar 1\bar 0, \bar 0\bar 1, \bar 0 0 \rbrace$,
$\lbrace \bar 1\bar 0, \bar 0\bar 1, 0\bar 1 \rbrace$,
$\lbrace \bar 1 0, \bar 0\bar 1, 0\bar 1 \rbrace$,
$\lbrace \bar 1 0, \bar 0 0, \bar 0 1 \rbrace$,
$\lbrace \bar 1\bar 0, \bar 0\bar 1, 0\bar 0 \rbrace$,
$\lbrace \bar 1 0, \bar 0 0, 0\bar 1 \rbrace$ and
$\lbrace \bar 1 0, 0\bar 0, 0\bar 1 \rbrace$, we have $|\bar I_n(B)| = (n+1)!$.

The source prints an unbarred $I_n$ in parts (iii) and (iv); it is read as $\bar I_n$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 8 (`integers-2026-A74-lem-8`). -/
public theorem_wanted signedInvAvoidCount_eq_factorial_succ :
    ∀ n,
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, false, true⟩, ⟨.lt, false, true⟩} n = (n + 1)!

/-- **Mansour–Safadi Lemma 9: a Wilf-equivalence of three-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar10, \bar0\bar0\} \sim \{\bar1\bar0, \bar10, \bar00\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 9 (`integers-2026-A74-lem-9`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b10_b0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, false⟩}

/-- **Mansour–Safadi Lemma 10.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}\bar{0}, 1\bar{0}\})| =
|\bar{I}_n(\{\bar{1}\bar{0}, 0\bar{0}, 1\bar{0}\})|$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 10 (`integers-2026-A74-lem-10`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b0_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, false, true⟩, ⟨.gt, false, true⟩}

/-- **Signed Wilf classes of sets of three to twelve patterns.** Let $\mathrm{sw}_k$ be the number
of Wilf-equivalence classes among the sets of $k$ length-2 signed patterns. Then
$\mathrm{sw}_3 = 93$, $\mathrm{sw}_4 = 195$, $239 \le \mathrm{sw}_5 \le 240$, $\mathrm{sw}_6 = 190$,
$\mathrm{sw}_7 = 107$, $\mathrm{sw}_8 = 49$, $\mathrm{sw}_9 = 22$, $\mathrm{sw}_{10} = 8$,
$\mathrm{sw}_{11} = 3$ and $\mathrm{sw}_{12} = 1$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 1 (`integers-2026-A74-thm-1`). -/
public theorem_wanted signedWilfClassCount_three_to_twelve :
    signedWilfClassCount 3 = 93 ∧ signedWilfClassCount 4 = 195 ∧
    239 ≤ signedWilfClassCount 5 ∧ signedWilfClassCount 5 ≤ 240 ∧
    signedWilfClassCount 6 = 190 ∧ signedWilfClassCount 7 = 107 ∧ signedWilfClassCount 8 = 49 ∧
    signedWilfClassCount 9 = 22 ∧ signedWilfClassCount 10 = 8 ∧ signedWilfClassCount 11 = 3 ∧
    signedWilfClassCount 12 = 1

/-- **Mansour–Safadi Class 141 Wilf-equivalence.** Length-2 signed patterns are written as in
the paper, a bar marking a barred letter, and $B \sim C$ means that for every $n \ge 0$ the
number $|\bar I_n(B)|$ of signed inversion sequences of length $n$ avoiding every pattern of $B$
equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar10, \bar0\bar0, \bar00, 00\} \sim
\{\bar1\bar0, \bar10, \bar0\bar1, 0\bar1, 00\}$.

The paper leaves this equivalence (Class 141 of its Table 6) open; it is what remains to be shown
for the number of Wilf classes of five-pattern sets to be exactly $239$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 1, closing remark
(`integers-2026-A74-thm-1`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b10_b0b0_b00_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
          ⟨.lt, false, true⟩, ⟨.eq, false, false⟩}

/-- **Signed Wilf classes of sets of three patterns.** The number $\mathrm{sw}_3$ of
Wilf-equivalence classes among the sets of $3$ length-2 signed patterns is $93$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 2 (`integers-2026-A74-thm-2`). -/
public theorem_wanted signedWilfClassCount_three :
    signedWilfClassCount 3 = 93

/-- **Signed Wilf classes of sets of four patterns.** The number $\mathrm{sw}_4$ of
Wilf-equivalence classes among the sets of $4$ length-2 signed patterns is $195$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 10 (`integers-2026-A74-thm-10`). -/
public theorem_wanted signedWilfClassCount_four :
    signedWilfClassCount 4 = 195

/-- **Signed Wilf classes of sets of five to twelve patterns.** Let $\mathrm{sw}_k$ be the number
of Wilf-equivalence classes among the sets of $k$ length-2 signed patterns. Then
$239 \le \mathrm{sw}_5 \le 240$, $\mathrm{sw}_6 = 190$, $\mathrm{sw}_7 = 107$, $\mathrm{sw}_8 = 49$,
$\mathrm{sw}_9 = 22$, $\mathrm{sw}_{10} = 8$, $\mathrm{sw}_{11} = 3$ and $\mathrm{sw}_{12} = 1$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 11 (`integers-2026-A74-thm-11`). -/
public theorem_wanted signedWilfClassCount_five_to_twelve :
    239 ≤ signedWilfClassCount 5 ∧ signedWilfClassCount 5 ≤ 240 ∧
    signedWilfClassCount 6 = 190 ∧ signedWilfClassCount 7 = 107 ∧ signedWilfClassCount 8 = 49 ∧
    signedWilfClassCount 9 = 22 ∧ signedWilfClassCount 10 = 8 ∧ signedWilfClassCount 11 = 3 ∧
    signedWilfClassCount 12 = 1

/-- **Mansour–Safadi Theorem 3, class C2 (signed patterns 0̄0̄, 0̄0, 0̄1, 01).** A signed inversion
sequence of length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1, \dots,
k - 1, \overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$, $01$,
$10$, each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as
$|\tau_1|$, $|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write
$\bar I_n(B)$ for the set of signed inversion sequences of length $n$ that avoid every pattern in
$B$, and $F_B(x) = \sum_{n \ge 0} |\bar I_n(B)|\,x^n$ in $\mathbb{Q}[[x]]$. Let
$B_1 = \{\bar 0\bar 0, \bar 0 0, \bar 0 1, 01\}$ and
$B_2 = \{\bar 0\bar 0, \bar 0 1, 0\bar 0, 01\}$.
For every $n \ge 0$, $|\bar I_n(B_1)| = |\bar I_n(B_2)|$, and the coefficient of $x^n$ in
$F_{B_1}(x)$ equals the coefficient of $x^n$ in
$1 + 2\sum_{k=1}^{n} x^k \prod_{i=1}^{k} (1 - ix)^{-1}$.

Since the terms with $k > n$ contribute nothing to $x^n$, this says
$F_{B_1}(x) = 1 + 2\sum_{k \ge 1} x^k / \prod_{i=1}^{k} (1 - ix)$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C2) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b0_b00_b01_01 :
    signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    ∀ n, coeff n (signedInvAvoidGF {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩}) =
      coeff n (1 + 2 * ∑ k ∈ Finset.Icc 1 n, X ^ k * ∏ i ∈ Finset.Icc 1 k, (1 - (i : ℚ⟦X⟧) * X)⁻¹)

/-- **Mansour–Safadi Theorem 3, class C4 (signed patterns 0̄1̄, 0̄0̄, 0̄0, 01̄).** A signed
inversion sequence of length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1,
\dots, k - 1, \overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$,
$01$, $10$, each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as
$|\tau_1|$, $|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write
$\bar I_n(B)$ for the set of signed inversion sequences of length $n$ that avoid every pattern in
$B$. Let $B_1 = \{\bar 0\bar 1, \bar 0\bar 0, \bar 0 0, 0\bar 1\}$,
$B_2 = \{\bar 0\bar 1, \bar 0\bar 0, 0\bar 1, 0\bar 0\}$,
$B_3 = \{\bar 0\bar 1, \bar 0 0, 0\bar 1, 0\bar 0\}$ and
$B_4 = \{\bar 0 0, \bar 0 1, 0\bar 1, 0\bar 0\}$. Then
$|\bar I_n(B_1)| = |\bar I_n(B_2)| = |\bar I_n(B_3)| = |\bar I_n(B_4)|$ for every $n \ge 0$, and
$|\bar I_n(B_1)| = 2\,n!$ for every $n \ge 1$.

Together with $|\bar I_0(B)| = 1$, which holds for every $B$, this says that
$\sum_{n \ge 0} |\bar I_n(B_1)|\,x^n = 1 + 2\sum_{k \ge 1} k!\,x^k$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C4) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b0b0_b00_0b1 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩} ∧
    ∀ n, signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, true⟩} (n + 1) = 2 * (n + 1)!

/-- **Mansour–Safadi Theorem 3, class C12 (signed patterns 0̄1̄, 0̄0̄, 01̄, 01).** A signed
inversion sequence of length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1,
\dots, k - 1, \overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$,
$01$, $10$, each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as
$|\tau_1|$, $|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write
$\bar I_n(B)$ for the set of signed inversion sequences of length $n$ that avoid every pattern in
$B$, and $F_B(x) = \sum_{n \ge 0} |\bar I_n(B)|\,x^n$ in $\mathbb{Q}[[x]]$. Let
$B_1 = \{\bar 0\bar 1, \bar 0\bar 0, 0\bar 1, 01\}$, $B_2 = \{\bar 0\bar 1, \bar 0 1, 0\bar 1, 00\}$
and $B_3 = \{\bar 0\bar 1, \bar 0 1, 0\bar 0, 00\}$. Then
$|\bar I_n(B_1)| = |\bar I_n(B_2)| = |\bar I_n(B_3)|$ for every $n \ge 0$, and
$(1 - x)^2\,F_{B_1}(x) = 1 + x^2$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C12) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b0b0_0b1_01 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    ((1 - X) ^ 2) * signedInvAvoidGF {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      1 + X ^ 2

/-- **Mansour–Safadi Theorem 3, class C15 (signed patterns 0̄1̄, 0̄0̄, 0̄1, 01).** A signed
inversion sequence of length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1,
\dots, k - 1, \overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$,
$01$, $10$, each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as
$|\tau_1|$, $|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write
$\bar I_n(B)$ for the set of signed inversion sequences of length $n$ that avoid every pattern in
$B$, and $F_B(x) = \sum_{n \ge 0} |\bar I_n(B)|\,x^n$ in $\mathbb{Q}[[x]]$. Let
$B_1 = \{\bar 0\bar 1, \bar 0\bar 0, \bar 0 1, 01\}$,
$B_2 = \{\bar 0\bar 1, \bar 0 0, \bar 0 1, 00\}$,
$B_3 = \{\bar 0\bar 1, \bar 0\bar 0, 0\bar 1, 00\}$,
$B_4 = \{\bar 0\bar 1, \bar 0\bar 0, 0\bar 0, 00\}$,
$B_5 = \{\bar 0\bar 1, \bar 0 1, 0\bar 1, 01\}$, $B_6 = \{\bar 0\bar 0, \bar 0 0, 0\bar 1, 00\}$ and
$B_7 = \{\bar 0\bar 0, \bar 0 0, 0\bar 0, 00\}$. Then
$|\bar I_n(B_1)| = |\bar I_n(B_2)| = \cdots = |\bar I_n(B_7)|$ for every $n \ge 0$, and
$(1 - 2x)\,F_{B_1}(x) = 1$, that is, $F_{B_1}(x) = 1/(1 - 2x)$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C15) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_01 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    (1 - 2 * X) * signedInvAvoidGF {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      1

/-- **Mansour–Safadi Theorem 3, class C16 (signed patterns 0̄1̄, 0̄0, 01̄, 01).** A signed inversion
sequence of length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1, \dots,
k - 1, \overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$, $01$,
$10$, each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as
$|\tau_1|$, $|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write
$\bar I_n(B)$ for the set of signed inversion sequences of length $n$ that avoid every pattern in
$B$, and $F_B(x) = \sum_{n \ge 0} |\bar I_n(B)|\,x^n$ in $\mathbb{Q}[[x]]$. Let
$B_1 = \{\bar 0\bar 1, \bar 0 0, 0\bar 1, 01\}$ and $B_2 = \{\bar 0\bar 1, \bar 0 1, 0\bar 0, 01\}$.
Then $|\bar I_n(B_1)| = |\bar I_n(B_2)|$ for every $n \ge 0$, and
$(1 - x)^2 (1 - 3x + x^2)\,F_{B_1}(x) = 1 - 3x + 2x^2 - x^3$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C16) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b00_0b1_01 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    ((1 - X) ^ 2 * (1 - 3 * X + X ^ 2)) * signedInvAvoidGF {⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, true⟩, ⟨.lt, false, false⟩} =
      1 - 3 * X + 2 * X ^ 2 - X ^ 3

/-- **Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, \bar01, 00\}$.** For a set $B$
of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar1, \bar01, 00\}$ and $C = \{\bar10, \bar0\bar0, 0\bar1, 01\}$. Then
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and $(1 - x)^3 F_B(x) = 1 - x + 2x^2$, that is,
$F_B(x) = (1 - x + 2x^2)/(1 - x)^3$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C23) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_b01_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    ((1 - X) ^ 3) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, false⟩} =
      1 - X + 2 * X ^ 2

/-- **Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar0, 0\bar1, 01\}$.** For a set $B$
of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar0, 0\bar1, 01\}$ and $C = \{\bar10, \bar0\bar1, \bar01, 00\}$. Then
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and $(1 - x)(1 - 2x) F_B(x) = 1 - x + x^2$,
that is, $F_B(x) = (1 - x + x^2)/((1 - x)(1 - 2x))$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C25) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b0_0b1_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, false⟩} ∧
    ((1 - X) * (1 - 2 * X)) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.lt, false, true⟩, ⟨.lt, false, false⟩} =
      1 - X + X ^ 2

/-- **Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, \bar0\bar0, 00\}$.** For a set
$B$ of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B_1 = \{\bar1\bar0, \bar0\bar1, \bar0\bar0, 00\}$, $B_2 = \{\bar1\bar0, \bar0\bar1, \bar01, 01\}$,
$B_3 = \{\bar10, \bar0\bar1, \bar01, 01\}$, $B_4 = \{\bar10, \bar0\bar0, 0\bar1, 00\}$ and
$B_5 = \{\bar0\bar0, \bar01, 00, 1\bar0\}$. Then
$|\bar I_n(B_1)| = |\bar I_n(B_2)| = |\bar I_n(B_3)| = |\bar I_n(B_4)| = |\bar I_n(B_5)|$ for every
$n \ge 0$, and $(1 - x)^2(1 - 2x) F_{B_1}(x) = 1 - 2x + 2x^2$, that is,
$F_{B_1}(x) = (1 - 2x + 2x^2)/((1 - x)^2(1 - 2x))$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C30) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_b0b0_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
          ⟨.lt, false, false⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
          ⟨.lt, false, false⟩} ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.eq, false, false⟩,
          ⟨.gt, false, true⟩} ∧
    ((1 - X) ^ 2 * (1 - 2 * X)) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, false, false⟩} =
      1 - 2 * X + 2 * X ^ 2

/-- **Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, \bar00, 01\}$.** For a set $B$
of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar1, \bar00, 01\}$ and $C = \{\bar10, \bar0\bar1, \bar00, 01\}$. Then
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and
$(1 - x)(1 - 2x)(1 - 3x + x^2) F_B(x) = 1 - 4x + 5x^2 - 3x^3$, that is,
$F_B(x) = (1 - 4x + 5x^2 - 3x^3)/((1 - x)(1 - 2x)(1 - 3x + x^2))$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C32) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_b00_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
          ⟨.lt, false, false⟩} ∧
    ((1 - X) * (1 - 2 * X) * (1 - 3 * X + X ^ 2)) * signedInvAvoidGF {⟨.gt, true, true⟩,
        ⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, false⟩} =
      1 - 4 * X + 5 * X ^ 2 - 3 * X ^ 3

/-- **Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar0, \bar00, 01\}$.** For a set $B$
of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar0, \bar00, 01\}$ and $C = \{\bar1\bar0, \bar01, 0\bar1, 01\}$. Then
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and for every power series
$S \in \mathbb{Q}[[x]]$ with constant term $1$ and $S^2 = 1 - 4x$,
$$
2x(1 - x)^2(1 - 2x) F_B(x) = 1 - 3x + 2x^2 + 2x^3 - (1 - 3x + 2x^2) S.
$$
This is the formula
$F_B(x) = \bigl(1 - 3x + 2x^2 + 2x^3 - (1 - 3x + 2x^2)\sqrt{1 - 4x}\bigr)/(2x(1 - x)^2(1 - 2x))$
multiplied by its denominator, with $S = \sqrt{1 - 4x}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C39) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b0_b00_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    ∀ S : ℚ⟦X⟧, constantCoeff S = 1 → S ^ 2 = 1 - 4 * X →
      2 * X * (1 - X) ^ 2 * (1 - 2 * X) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.eq, true, false⟩, ⟨.lt, false, false⟩} =
        1 - 3 * X + 2 * X ^ 2 + 2 * X ^ 3 - (1 - 3 * X + 2 * X ^ 2) * S

/-- **Mansour–Safadi Theorem 3, class C41 (signed patterns 1̄0̄, 0̄0̄, 01̄, 00).** A signed
inversion sequence of length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1,
\dots, k - 1, \overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$,
$01$, $10$, each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as
$|\tau_1|$, $|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write
$\bar I_n(B)$ for the set of signed inversion sequences of length $n$ that avoid every pattern in
$B$, and $F_B(x) = \sum_{n \ge 0} |\bar I_n(B)|\,x^n$ in $\mathbb{Q}[[x]]$. Let
$B_1 = \{\bar 1\bar 0, \bar 0\bar 0, 0\bar 1, 00\}$ and
$B_2 = \{\bar 1 0, \bar 0\bar 0, \bar 0 0, 01\}$.
For every $n \ge 0$, $|\bar I_n(B_1)| = |\bar I_n(B_2)|$, and the coefficient of $x^n$ in
$F_{B_1}(x)$ equals the coefficient of $x^n$ in
$(1 - x)^{-1} + (1 - x)^{-1} \sum_{j=1}^{n} x^j (1 - (j + 1)x)^{-1}$.

Since the terms with $j > n$ contribute nothing to $x^n$, this says
$F_{B_1}(x) = \frac{1}{1 - x}\bigl(1 + \sum_{j \ge 1} x^j / (1 - (j + 1)x)\bigr)$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C41) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b0_0b1_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩,
          ⟨.lt, false, false⟩} ∧
    ∀ n, coeff n (signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩}) =
      coeff n ((1 - X)⁻¹ + (1 - X)⁻¹ * ∑ j ∈ Finset.Icc 1 n, X ^ j * (1 - ((j + 1 : ℕ) : ℚ⟦X⟧) *
            X)⁻¹)

/-- **Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, \bar00, 00\}$.** For a set $B$
of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B_1 = \{\bar1\bar0, \bar0\bar1, \bar00, 00\}$, $B_2 = \{\bar1\bar0, \bar0\bar1, 0\bar0, 00\}$ and
$B_3 = \{\bar10, \bar0\bar1, 0\bar0, 00\}$. Then
$|\bar I_n(B_1)| = |\bar I_n(B_2)| = |\bar I_n(B_3)|$ for every $n \ge 0$, and for every $n \ge 0$
the coefficient of $x^n$ in $F_{B_1}(x)$ equals the coefficient of $x^n$ in
$$
\frac{1}{1 - x} + \frac{1}{1 - x} \sum_{j=1}^{n} \frac{x^j (1 - jx)}{\prod_{i=1}^{j+1} (1 - ix)}.
$$

The terms with $j > n$ are divisible by $x^{n+1}$, so this says
$F_{B_1}(x) = \frac{1}{1 - x}\Bigl(1 + \sum_{j \ge 1} x^j (1 - jx) /
\prod_{i=1}^{j+1} (1 - ix)\Bigr)$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C46) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_b00_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    ∀ n, coeff n (signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.eq, false, false⟩}) =
      coeff n ((1 - X)⁻¹ + (1 - X)⁻¹ * ∑ j ∈ Finset.Icc 1 n, X ^ j * (1 - (j : ℚ⟦X⟧) * X) * ∏ i ∈
            Finset.Icc 1 (j + 1), (1 - (i : ℚ⟦X⟧) * X)⁻¹)

/-- **Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, \bar01, 0\bar1\}$.** For a set
$B$ of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar1, \bar01, 0\bar1\}$ and $C = \{\bar10, \bar0\bar1, \bar01, 0\bar1\}$.
Then $|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and
$(1 - 2x) F_B(x) = (1 - x) \sum_{j \ge 0} j!\, x^j$, that is,
$F_B(x) = \frac{1 - x}{1 - 2x} \sum_{j \ge 0} j!\, x^j$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C50) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_b01_0b1 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
          ⟨.lt, false, true⟩} ∧
    (1 - 2 * X) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} =
      (1 - X) * PowerSeries.mk fun j => (j ! : ℚ)

/-- **Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, 0\bar1, 00\}$.** For a set $B$
of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar1, 0\bar1, 00\}$ and $C = \{\bar10, \bar0\bar1, 0\bar1, 00\}$. Then
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and for every $n \ge 0$ the coefficient of
$x^n$ in $F_B(x)$ equals the coefficient of $x^n$ in
$\sum_{j=0}^{n} x^j \prod_{i=1}^{j+1} (1 - ix)^{-1}$.

The terms with $j > n$ are divisible by $x^{n+1}$, so this says
$F_B(x) = \sum_{j \ge 0} x^j / \prod_{i=1}^{j+1} (1 - ix)$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C60) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_0b1_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    ∀ n, coeff n (signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩}) =
      coeff n (∑ j ∈ Finset.range (n + 1), X ^ j * ∏ i ∈ Finset.Icc 1 (j + 1), (1 - (i : ℚ⟦X⟧) *
            X)⁻¹)

/-- **Mansour–Safadi Theorem 4.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{0}\bar{1}, \bar{0}\bar{0}, \bar{0}1, 0\bar{0}\})| =
|\bar{I}_n(\{\bar{0}\bar{1}, \bar{0}0, \bar{0}1, 0\bar{0}\})|$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 4 (`integers-2026-A74-thm-4`). -/
public theorem_wanted signedInvSeq_wilf_b0b1_b0b0_b01_0b0 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, true⟩}

/-- **Mansour–Safadi Theorem 5.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}\bar{0}, \bar{0}1, 0\bar{0}\})| =
|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}0, \bar{0}1, 0\bar{0}\})|$,
$|\bar{I}_n(\{\bar{1}0, \bar{0}\bar{1}, \bar{0}\bar{0}, 0\bar{0}\})| =
|\bar{I}_n(\{\bar{1}0, \bar{0}\bar{1}, \bar{0}0, 0\bar{0}\})|$, and
$|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}\bar{0}, \bar{0}1, 1\bar{0}\})| =
|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}0, \bar{0}1, 1\bar{0}\})|$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 5 (`integers-2026-A74-thm-5`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b0_b01_0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.gt, false, true⟩}

/-- **Mansour–Safadi Theorem 6.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{1}0, \bar{0}0, 0\bar{1}, 00\})| =
|\bar{I}_n(\{\bar{1}0, 0\bar{1}, 0\bar{0}, 00\})|$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 6 (`integers-2026-A74-thm-6`). -/
public theorem_wanted signedInvSeq_wilf_b10_b00_0b1_00 :
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, false, true⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩}

/-- **Mansour–Safadi Theorem 7: four Wilf-equivalent four-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar0\bar1, \bar0\bar0, \bar00\} \sim \{\bar1\bar0, \bar0\bar1, \bar0\bar0, 0\bar0\}
\sim \{\bar1\bar0, \bar0\bar1, \bar00, 0\bar0\} \sim \{\bar10, \bar00, 0\bar1, 0\bar0\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 7 (`integers-2026-A74-thm-7`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b1_b0b0_b00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩}

/-- **Mansour–Safadi Theorem 12: four Wilf-equivalences of five-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar0\bar1, \bar00, \bar01, 0\bar0\} \sim
\{\bar1\bar0, \bar0\bar1, \bar0\bar0, \bar01, 0\bar0\}$,
$\{\bar1\bar0, \bar10, \bar0\bar1, \bar00, 0\bar0\} \sim
\{\bar1\bar0, \bar10, \bar0\bar1, \bar0\bar0, 0\bar0\}$,
$\{\bar1\bar0, \bar0\bar1, \bar0\bar0, \bar00, 1\bar0\} \sim
\{\bar1\bar0, \bar0\bar1, \bar00, 0\bar0, 1\bar0\}$ and
$\{\bar1\bar0, \bar10, \bar0\bar1, \bar00, 00\} \sim
\{\bar1\bar0, \bar10, \bar0\bar1, 0\bar0, 00\}$.

The paper prints a third set in the first equivalence,
$\{\bar1\bar0, \bar0\bar1, \bar01, 0\bar0, 1\bar0\}$; it is left out here because it has
$|\bar I_2| = 5$, against $4$ for the first two sets.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 12 (`integers-2026-A74-thm-12`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b1_b00_b01_0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, true, false⟩, ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.lt, true, false⟩, ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
          ⟨.eq, true, true⟩, ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
          ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
          ⟨.eq, false, true⟩, ⟨.eq, false, false⟩}

/-- **Mansour–Safadi Theorem 14.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Let
$B_1 = \{\bar{1}0, \bar{0}\bar{1}, 0\bar{1}, 0\bar{0}, 1\bar{0}\}$,
$B_2 = \{\bar{1}\bar{0}, \bar{0}\bar{1}, 0\bar{1}, 0\bar{0}, 1\bar{0}\}$,
$B_3 = \{\bar{1}\bar{0}, \bar{1}0, \bar{0}\bar{0}, \bar{0}0, 0\bar{0}\}$,
$B_4 = \{\bar{1}\bar{0}, \bar{0}\bar{0}, 0\bar{1}, 0\bar{0}, 1\bar{0}\}$,
$B_5 = \{\bar{1}\bar{0}, \bar{0}\bar{1}, \bar{0}\bar{0}, 0\bar{1}, 1\bar{0}\}$,
$B_6 = \{\bar{1}0, \bar{0}\bar{1}, \bar{0}\bar{0}, 0\bar{1}, 1\bar{0}\}$, and
$B_7 = \{\bar{1}\bar{0}, \bar{1}0, \bar{0}\bar{0}, \bar{0}0, \bar{0}1\}$.
Then for every $n \ge 0$,
$|\bar{I}_n(B_1)| = |\bar{I}_n(B_2)| = |\bar{I}_n(B_3)| = |\bar{I}_n(B_4)| = |\bar{I}_n(B_5)| =
|\bar{I}_n(B_6)| = |\bar{I}_n(B_7)|$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 14 (`integers-2026-A74-thm-14`). -/
public theorem_wanted signedInvSeq_wilf_b10_b0b1_0b1_0b0_1b0 :
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
          ⟨.eq, true, false⟩, ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.lt, false, true⟩, ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.lt, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.lt, false, true⟩, ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.lt, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
          ⟨.eq, true, false⟩, ⟨.lt, true, false⟩}

/-- **Mansour–Safadi Theorem 15.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}0, \bar{0}1, 0\bar{0}, 1\bar{0}\})| =
|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}\bar{0}, \bar{0}1, 0\bar{0}, 1\bar{0}\})|$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 15 (`integers-2026-A74-thm-15`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b00_b01_0b0_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, true⟩, ⟨.gt, false, true⟩}

/-- **Three six-pattern sets with 2 · n! avoiders (Theorem 17).** Write a length-2 signed pattern
as $\tau_1\tau_2$, where $00$, $01$ and $10$ record whether $|\tau_1|$ is equal to, smaller than
or larger than $|\tau_2|$ and a bar marks a barred letter, and write $|\bar I_n(A)|$ for the
number of signed inversion sequences of length $n$ avoiding every pattern of a set $A$ of such
patterns. For every $n \ge 1$ and each of the three sets
$A = \lbrace \bar 1\bar 0, \bar 1 0, \bar 0\bar 1, \bar 0\bar 0, \bar 0 0, 0\bar 1 \rbrace$,
$\lbrace \bar 1\bar 0, \bar 1 0, \bar 0\bar 1, \bar 0\bar 0, \bar 0 0, 0\bar 0 \rbrace$ and
$\lbrace \bar 1\bar 0, \bar 0\bar 1, \bar 0\bar 0, \bar 0 0, \bar 0 1, 1\bar 0 \rbrace$, we have
$|\bar I_n(A)| = 2 \cdot n!$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 17 (`integers-2026-A74-thm-17`). -/
public theorem_wanted signedInvAvoidCount_eq_two_mul_factorial :
    ∀ n, 1 ≤ n →
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} n = 2 * n ! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩} n = 2 * n ! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} n = 2 * n !

end

end MetaMathlibExt
