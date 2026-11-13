/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.SetTheory.Cardinal.Finite

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

/-- **Length-2 signed pattern.** A length-2 signed pattern is a word $\tau_1\tau_2$ whose
underlying word $|\tau_1||\tau_2|$ is $00$, $01$ or $10$ and each of whose letters may be barred,
for example $\bar10$ or $0\bar1$. It is given by the comparison of $|\tau_1|$ with $|\tau_2|$
(equal for $00$, less for $01$, greater for $10$) together with whether $\tau_1$ is barred and
whether $\tau_2$ is barred.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
structure SignedPattern2 where
  /-- The comparison of `|τ₁|` with `|τ₂|`. -/
  ord : Ordering
  /-- Whether the first letter is barred. -/
  bar₁ : Bool
  /-- Whether the second letter is barred. -/
  bar₂ : Bool
deriving DecidableEq, Fintype

/-- **Number of length-2 signed patterns.** There are exactly twelve length-2 signed patterns.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Section 5 (`binom 12 k` sets of `k`
patterns). -/
theorem card_signedPattern2 : Fintype.card SignedPattern2 = 12 := by decide

/-- **Containment of a length-2 signed pattern.** Let $e = e_1 \cdots e_n$ be a sequence whose
entries are natural numbers $|e_i|$, each barred or not, and let $\tau_1\tau_2$ be a length-2
signed pattern. Then $e$ contains $\tau_1\tau_2$ if there are positions $i < j$ such that $|e_i|$
is equal to, smaller than or larger than $|e_j|$ exactly as $|\tau_1|$ is equal to, smaller than
or larger than $|\tau_2|$, and $e_i$ and $e_j$ are barred exactly when $\tau_1$ and $\tau_2$ are.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
def SignedInvSeqContains {n : ℕ} (e : Fin n → ℕ × Bool) (p : SignedPattern2) : Prop :=
  ∃ i j : Fin n, i < j ∧ compare (e i).1 (e j).1 = p.ord ∧ (e i).2 = p.bar₁ ∧ (e j).2 = p.bar₂

/-- **Number of signed inversion sequences avoiding a set of patterns.** A signed inversion
sequence of length $n$ is a word $e_1 \cdots e_n$ in which each entry $e_i$ is a natural number
$|e_i| \le i - 1$, either barred or not; that is, $e_i \in \lbrace 0, \bar 0, 1, \bar 1, \dots,
i - 1, \overline{i - 1} \rbrace$. For a finite set $B$ of length-2 signed patterns and $n \ge 0$,
$|\bar I_n(B)|$ is the number of signed inversion sequences of length $n$ that contain no pattern
of $B$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
noncomputable def signedInvAvoidCount (B : Finset SignedPattern2) (n : ℕ) : ℕ :=
  Nat.card {e : Fin n → ℕ × Bool // (∀ i, (e i).1 ≤ i) ∧ ∀ p ∈ B, ¬ SignedInvSeqContains e p}

/-- **Signed inversion sequences of length zero.** The empty sequence is the only signed inversion
sequence of length $0$, and it contains no pattern, so for every finite set $B$ of length-2 signed
patterns the number $|\bar I_0(B)|$ of signed inversion sequences of length $0$ avoiding every
pattern of $B$ is $1$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
theorem signedInvAvoidCount_zero (B : Finset SignedPattern2) : signedInvAvoidCount B 0 = 1 := by
  rw [signedInvAvoidCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun e e' => Subtype.ext (funext fun i => i.elim0)⟩, ⟨⟨fun i => i.elim0, ?_⟩⟩⟩
  exact ⟨fun i => i.elim0, fun _ _ ⟨i, _⟩ => i.elim0⟩

/-- **Signed inversion sequences of length one.** The signed inversion sequences of length $1$ are
$0$ and $\bar 0$, and neither contains a length-2 signed pattern, so for every finite set $B$ of
length-2 signed patterns the number $|\bar I_1(B)|$ of signed inversion sequences of length $1$
avoiding every pattern of $B$ is $2$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
theorem signedInvAvoidCount_one (B : Finset SignedPattern2) : signedInvAvoidCount B 1 = 2 := by
  have hpat : ∀ (e : Fin 1 → ℕ × Bool) (p : SignedPattern2), ¬ SignedInvSeqContains e p := by
    rintro e p ⟨i, j, hij, -⟩
    exact absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl j)
  let f : {e : Fin 1 → ℕ × Bool // (∀ i, (e i).1 ≤ i) ∧ ∀ p ∈ B, ¬ SignedInvSeqContains e p} ≃
      Bool :=
    { toFun := fun e => (e.1 0).2
      invFun := fun b => ⟨fun _ => (0, b), fun i => Nat.zero_le _, fun p _ => hpat _ p⟩
      left_inv := fun e => by
        refine Subtype.ext (funext fun i => ?_)
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        have h0 : (e.1 0).1 = 0 := Nat.le_zero.mp (e.2.1 0)
        exact Prod.ext h0.symm rfl
      right_inv := fun b => rfl }
  rw [signedInvAvoidCount, Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_bool]

/-- **Generating function of signed inversion sequences avoiding a set of patterns.** For a finite
set $B$ of length-2 signed patterns, $F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n$ is the formal
power series with rational coefficients whose coefficient of $x^n$ is the number $|\bar I_n(B)|$
of signed inversion sequences of length $n$ avoiding every pattern of $B$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Section 2. -/
noncomputable def signedInvAvoidGF (B : Finset SignedPattern2) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (signedInvAvoidCount B n : ℚ)

/-- **Coefficients of the avoidance generating function.** For a finite set $B$ of length-2
signed patterns and $m \ge 0$, let $|\bar I_m(B)|$ be the number of signed inversion sequences of
length $m$ avoiding every pattern of $B$, and let $F_B(x) = \sum_{m \ge 0} |\bar I_m(B)| x^m$ be
their generating function, a formal power series with rational coefficients. Then for every
$n \ge 0$ the coefficient of $x^n$ in $F_B(x)$ is $|\bar I_n(B)|$, viewed as a rational number.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Section 2. -/
theorem coeff_signedInvAvoidGF (B : Finset SignedPattern2) (n : ℕ) :
    coeff n (signedInvAvoidGF B) = (signedInvAvoidCount B n : ℚ) := by
  simp [signedInvAvoidGF]

/-- **Number of signed Wilf classes.** For $k \ge 0$, $\mathrm{sw}_k$ is the number of
Wilf-equivalence classes among the sets of $k$ length-2 signed patterns, that is, the number of
distinct counting functions $n \mapsto |\bar{I}_n(B)|$ (for $n \ge 0$) over all sets $B$ of exactly
$k$ length-2 signed patterns, where $|\bar{I}_n(B)|$ is the number of signed inversion sequences of
length $n$ avoiding every pattern of $B$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 1. -/
noncomputable def signedWilfClassCount (k : ℕ) : ℕ :=
  Set.ncard ((fun B => signedInvAvoidCount B) '' {B : Finset SignedPattern2 | B.card = k})

/-- **The empty pattern set forms one signed Wilf class.** The number $\mathrm{sw}_0$ of
Wilf-equivalence classes among the sets of $0$ length-2 signed patterns is $1$: the empty set is
the only set of no patterns.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 1 (definition of `sw_k`). -/
theorem signedWilfClassCount_zero : signedWilfClassCount 0 = 1 := by
  have : {B : Finset SignedPattern2 | B.card = 0} = {∅} := by
    ext B
    simp
  rw [signedWilfClassCount, this, Set.image_singleton, Set.ncard_singleton]

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

/-- **Mansour–Safadi Lemma 3 (signed patterns 0̄1̄, 0̄0̄, 01̄).** A signed inversion sequence of
length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1, \dots, k - 1,
\overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$, $01$, $10$,
each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as $|\tau_1|$,
$|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write $\bar I_n(B)$ for the
set of signed inversion sequences of length $n$ that avoid every pattern in $B$. Let
$B_1 = \{\bar 0\bar 1, \bar 0\bar 0, 0\bar 1\}$, $B_2 = \{\bar 0\bar 1, \bar 0 0, 0\bar 1\}$ and
$B_3 = \{\bar 0\bar 1, 0\bar 1, 0\bar 0\}$. For every $n \ge 0$,
$|\bar I_n(B_1)| = |\bar I_n(B_2)| = |\bar I_n(B_3)| = n!\,(1 + H_n)$, where
$H_n = \sum_{k=1}^{n} 1/k$ is the $n$th harmonic number.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 3 (`integers-2026-A74-lem-3`). -/
public theorem_wanted signedInvSeq_wilf_and_count_b0b1_b0b0_0b1 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, false, true⟩, ⟨.eq, false, true⟩} ∧
    ∀ n, (signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩} n : ℚ) =
        n ! * (1 + harmonic n)

/-- **Mansour–Safadi Lemma 4 (signed patterns 0̄1̄, 0̄0̄, 0̄1).** A signed inversion sequence of
length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1, \dots, k - 1,
\overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$, $01$, $10$,
each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as $|\tau_1|$,
$|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write $\bar I_n(B)$ for the
set of signed inversion sequences of length $n$ that avoid every pattern in $B$. For every
$n \ge 0$, $|\bar I_n(\{\bar 0\bar 1, \bar 0\bar 0, \bar 0 1\})| =
|\bar I_n(\{\bar 0\bar 1, \bar 0 0, \bar 0 1\})| = \sum_{j=0}^{n} j!\,(j + 1)^{n - j}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 4 (`integers-2026-A74-lem-4`). -/
public theorem_wanted signedInvSeq_wilf_and_count_b0b1_b0b0_b01 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩} ∧
    ∀ n, signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩} n =
        ∑ j ∈ Finset.range (n + 1), j ! * (j + 1) ^ (n - j)

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

/-- **Mansour–Safadi Theorem 3, class C3 (signed patterns 0̄1̄, 0̄0̄, 0̄1, 01̄).** A signed
inversion sequence of length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1,
\dots, k - 1, \overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$,
$01$, $10$, each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as
$|\tau_1|$, $|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write
$\bar I_n(B)$ for the set of signed inversion sequences of length $n$ that avoid every pattern in
$B$. Let $B_1 = \{\bar 0\bar 1, \bar 0\bar 0, \bar 0 1, 0\bar 1\}$,
$B_2 = \{\bar 0\bar 1, \bar 0 0, \bar 0 1, 0\bar 1\}$ and
$B_3 = \{\bar 0\bar 0, \bar 0 0, 0\bar 1, 0\bar 0\}$. For every $n \ge 0$,
$|\bar I_n(B_1)| = |\bar I_n(B_2)| = |\bar I_n(B_3)| = \sum_{i=0}^{n} i!$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C3) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.lt, false, true⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩} ∧
    ∀ n, signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} n =
      ∑ i ∈ Finset.range (n + 1), i !

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

/-- **Mansour–Safadi Theorem 3, class C21.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{0}\bar{1}, \bar{0}1, 0\bar{1}, 0\bar{0}\})| =
|\bar{I}_n(\{\bar{0}\bar{0}, \bar{0}1, 0\bar{1}, 0\bar{0}\})|$.

The generating function printed in the paper, $1/(1 - x)^2 + \sum_{j \ge 0} j!\, x^j$, is false
(its constant term is $2$, while $|\bar{I}_0(B)| = 1$) and is omitted.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C21) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_b0b1_b01_0b1_0b0 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩}

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

/-- **Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, 0\bar1, 01\}$.** For a set $B$
of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar1, 0\bar1, 01\}$ and $C = \{\bar10, \bar0\bar1, 0\bar1, 01\}$. Then
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and $(1 - 3x + x^2) F_B(x) = 1 - x$, that is,
$F_B(x) = (1 - x)/(1 - 3x + x^2)$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C38) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_0b1_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    (1 - 3 * X + X ^ 2) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩,
        ⟨.lt, false, true⟩, ⟨.lt, false, false⟩} =
      1 - X

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

/-- **Mansour–Safadi Theorem 3, class C45.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}\bar{0}, \bar{0}1, 01\})| =
|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}0, \bar{0}1, 00\})|$.

The generating function $C(x)$ printed in the paper is not defined there and is omitted.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C45) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b0_b01_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, false⟩}

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

/-- **Mansour–Safadi Theorem 8: two Wilf-equivalences of four-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar0\bar1, \bar0\bar0, 1\bar0\} \sim \{\bar1\bar0, \bar0\bar1, 0\bar0, 1\bar0\}$
and $\{\bar1\bar0, \bar0\bar0, \bar00, 1\bar0\} \sim \{\bar1\bar0, \bar00, 0\bar0, 1\bar0\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 8 (`integers-2026-A74-thm-8`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b1_b0b0_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩,
          ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩,
          ⟨.gt, false, true⟩}

/-- **Mansour–Safadi Theorem 9: a Wilf-equivalence of four-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar10, \bar0\bar0, 0\bar0\} \sim \{\bar1\bar0, \bar10, \bar00, 0\bar0\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 9 (`integers-2026-A74-thm-9`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b10_b0b0_0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, false⟩,
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

/-- **Mansour–Safadi Theorem 13: a Wilf-equivalence of five-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar0\bar1, \bar00, \bar01, 1\bar0\} \sim
\{\bar1\bar0, \bar0\bar1, \bar0\bar0, \bar01, 1\bar0\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 13 (`integers-2026-A74-thm-13`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.lt, true, false⟩, ⟨.gt, false, true⟩}

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

/-- **Mansour–Safadi Theorem 16: a Wilf-equivalence of six-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar10, \bar0\bar1, \bar00, \bar01, 0\bar0\} \sim
\{\bar1\bar0, \bar10, \bar0\bar1, \bar0\bar0, \bar01, 0\bar0\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 16 (`integers-2026-A74-thm-16`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b10_b0b1_b00_b01_0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
          ⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩}

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

/-- **Mansour–Safadi Theorem 18: a Wilf-equivalence of seven-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar10, \bar0\bar1, \bar0\bar0, \bar00, \bar01, 1\bar0\} \sim
\{\bar1\bar0, \bar10, \bar0\bar0, \bar00, \bar01, 0\bar0, 1\bar0\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 18 (`integers-2026-A74-thm-18`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b10_b0b1_b0b0_b00_b01_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
          ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩, ⟨.gt, false, true⟩}

end

end MetaMathlibExt
