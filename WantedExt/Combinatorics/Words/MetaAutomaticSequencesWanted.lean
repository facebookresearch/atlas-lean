/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Log
public import MathlibExt.Combinatorics.InfiniteWord.ThueMorse
public import MathlibExt.Combinatorics.InfiniteWord.ThueMorseFactors
public import MathlibExt.Combinatorics.InfiniteWord.WordFactorComplexity
public import MathlibExt.Combinatorics.Words.BalancedDyadicNestedEventuallyPeriodic
public import MathlibExt.Combinatorics.Words.BalancedNestedXor
public import MathlibExt.Combinatorics.Words.CobhamUniformMorphism
public import MathlibExt.Combinatorics.Words.MetaAutomaticOne
public import MathlibExt.Combinatorics.Words.MetaAutomaticTwo
public import MathlibExt.Combinatorics.Words.MetaAutomaticTwoDigitMask
public import MathlibExt.Combinatorics.Words.RegularSequence
public import MathlibExt.Combinatorics.Words.RightSpecialFactors
public import MathlibExt.Combinatorics.Words.ThueMorseQuarto

namespace MetaMathlibExt

open Filter Asymptotics

@[expose] public section

/-- **First sixteen terms of $\mathcal{M}_1$.** Writing the values of the meta-automatic sequence
$\mathcal{M}_1$ as $0$ and $1$, the terms $\mathcal{M}_1(0), \dots, \mathcal{M}_1(15)$ are
$0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 3. -/
public theorem metaAutomaticOne_small : (List.range 16).map metaAutomaticOne =
    [false, true, true, false, true, false, true, false, true, false, true, false, false,
      true, false, true] := by
  simp [List.range_succ, metaAutomaticOne]

/-- **Allouche–Shallit criterion for automatic sequences.** Let $A$ be a finite set,
$U : \mathbb{N} \to A$ a sequence and $q \ge 2$ a natural number. Let $t, a, b, n_0$ be natural
numbers, let $P$ be the set of pairs $(i, j')$ of natural numbers with $i \le t$, $j' < q^i$ and
$(i, j') \ne (0, 0)$, and for each natural number $j$ let $f_j$ map families of elements of $A$
indexed by the disjoint union of $\{0, 1, \dots, a + b\}$ and $P$ to $A$. Suppose that for all
$n \ge n_0$ and $j < q^{t+1}$, $U(q^{t+1} n + j)$ is the value of $f_j$ at the family sending
$k \in \{0, \dots, a + b\}$ to $U(n + k - a)$ and $(i, j') \in P$ to $U(q^i n + j')$, where
$n + k - a$ is read as $0$ when it is negative. Then $U$ is $q$-automatic.

The arguments $U(n - a), \dots, U(n + b)$ are truncated only when $n < a$, which is harmless
since only large $n$ matter; the paper notes that the order of the arguments plays no role.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 2, quoting Allouche and Shallit
(2012), Theorem 2.2 (`jis-2026-26.4.1-thm-2`). -/
public theorem_wanted isKAutomaticSequence_of_digit_recurrence {A : Type} [Fintype A]
    (U : ℕ → A) (q : ℕ) (hq : 2 ≤ q) (t a b n₀ : ℕ)
    (f : ℕ → ((Fin (a + b + 1) ⊕
      {p : ℕ × ℕ // p.1 ≤ t ∧ p.2 < q ^ p.1 ∧ p ≠ (0, 0)}) → A) → A)
    (hf : ∀ n, n₀ ≤ n → ∀ j, j < q ^ (t + 1) →
      U (q ^ (t + 1) * n + j) =
        f j (Sum.elim (fun i => U (n + i - a)) (fun p => U (q ^ p.1.1 * n + p.1.2)))) :
    IsKAutomaticSequence q U

/-- **An automaton for the meta-automatic sequence $\mathcal{M}_1$.** The meta-automatic sequence
$\mathcal{M}_1$ is $4$-automatic. Moreover, let $\delta$ be the transition map on the states
$\{0, 1, 2, 3\}$ and the digits $\{0, 1, 2, 3\}$ given by $\delta(0, \cdot) = 0112$,
$\delta(1, \cdot) = 1230$, $\delta(2, \cdot) = 2301$ and $\delta(3, \cdot) = 3023$, where the
symbol at position $d$ (counted from $0$) of the word listed for $q$ is $\delta(q, d)$. For every
$n \in \mathbb{N}$, let $q_n$ be the state reached by starting in state $0$ and reading the
base-$4$ digits of $n$ with $\delta$, most significant digit first (no digits when $n = 0$).
Then, reading the values of $\mathcal{M}_1$ as $0$ and $1$, $\mathcal{M}_1(n) = q_n \bmod 2$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 13 (`jis-2026-26.4.1-thm-13`). -/
public theorem_wanted metaAutomaticOne_dfao :
    IsKAutomaticSequence 4 metaAutomaticOne ∧
      ∀ n, metaAutomaticOne n = decide (((Nat.digits 4 n).reverse.foldl
        (fun q d => ([[0, 1, 1, 2], [1, 2, 3, 0], [2, 3, 0, 1], [3, 0, 2, 3]].getD q []).getD d 0)
        0) % 2 = 1)

/-- **$\mathcal{M}_1$ as a coding of a uniform morphism fixed point.** Let $\sigma$ be the
$4$-uniform morphism on $\{0, 1, 2, 3\}$ with $\sigma(0) = 0112$, $\sigma(1) = 1230$,
$\sigma(2) = 2301$ and $\sigma(3) = 3023$, and write $\sigma(c)_r$ for the letter of $\sigma(c)$
at position $r$, counted from $0$. There is a sequence $w : \mathbb{N} \to \mathbb{N}$ with
$w(0) = 0$ and $w(4n + r) = \sigma(w(n))_r$ for all $n \in \mathbb{N}$ and $r < 4$, such that,
reading the values of the meta-automatic sequence $\mathcal{M}_1$ as $0$ and $1$,
$\mathcal{M}_1(n) = w(n) \bmod 2$ for every $n \in \mathbb{N}$. In other words, $\mathcal{M}_1$
is the image of the fixed point of $\sigma$ starting with $0$ under the coding $0, 2 \mapsto 0$,
$1, 3 \mapsto 1$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Corollary 16 (`jis-2026-26.4.1-cor-16`). -/
public theorem_wanted metaAutomaticOne_morphism_coding :
    ∃ w : ℕ → ℕ, w 0 = 0 ∧
      (∀ n r, r < 4 → w (4 * n + r) =
        ([[0, 1, 1, 2], [1, 2, 3, 0], [2, 3, 0, 1], [3, 0, 2, 3]].getD (w n) []).getD r 0) ∧
      ∀ n, metaAutomaticOne n = decide (w n % 2 = 1)

/-- **Pair recurrence and $4$-automaticity of $\mathcal{M}_2$.** Read the meta-automatic
sequence $\mathcal{M}_2$ as taking values in $\{0, 1\}$, write $\oplus$ for addition modulo $2$,
and let $s(n) = (\mathcal{M}_2(n), \mathcal{M}_2(2n + \mathcal{M}_2(n)))$. For every $n \ge 0$,
writing $s(n) = (x, y)$, we have $s(4n) = (y, x \oplus y)$, $s(4n+1) = (y \oplus 1, x \oplus y)$,
$s(4n+2) = (y \oplus 1, x \oplus y \oplus 1)$ and $s(4n+3) = (y, x \oplus y \oplus 1)$.
Moreover, $\mathcal{M}_2$ is $4$-automatic, and it is computed by a four-state automaton: there
are maps $\delta : \{0, 1, 2, 3\} \times \{0, 1, 2, 3\} \to \{0, 1, 2, 3\}$ and
$\tau : \{0, 1, 2, 3\} \to \{0, 1\}$ such that for every $n$, $\mathcal{M}_2(n) = \tau(q)$, where
$q$ is the state reached from the state $0$ by reading the base-$4$ digits of $n$ with $\delta$,
most significant digit first (for $n = 0$ no digit is read, so $q = 0$).

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 20 (`jis-2026-26.4.1-thm-20`). -/
public theorem_wanted metaAutomaticTwo_affine (s : ℕ → Bool × Bool)
    (hs : ∀ m, s m = (metaAutomaticTwo m,
      metaAutomaticTwo (2 * m + (metaAutomaticTwo m).toNat))) :
    (∀ n, s (4 * n) = ((s n).2, xor (s n).1 (s n).2) ∧
      s (4 * n + 1) = (!(s n).2, xor (s n).1 (s n).2) ∧
      s (4 * n + 2) = (!(s n).2, !xor (s n).1 (s n).2) ∧
      s (4 * n + 3) = ((s n).2, !xor (s n).1 (s n).2)) ∧
    IsKAutomaticSequence 4 metaAutomaticTwo ∧
    ∃ δ : Fin 4 → Fin 4 → Fin 4, ∃ τ : Fin 4 → Bool, ∀ n,
      metaAutomaticTwo n = τ ((Nat.digits 4 n).reverse.foldl (fun q d => δ q (Fin.ofNat 4 d)) 0)

/-- **A four-state automaton computing $\mathcal{M}_2$.** Let
$\delta : \{0, 1, 2, 3\} \times \{0, 1, 2, 3\} \to \{0, 1, 2, 3\}$ be the map for which the word
$\delta(q, 0)\,\delta(q, 1)\,\delta(q, 2)\,\delta(q, 3)$ is $0132$ for $q = 0$, $2310$ for $q = 1$,
$3201$ for $q = 2$ and $1023$ for $q = 3$. For every natural number $n$, the meta-automatic
sequence $\mathcal{M}_2$, read as taking values in $\{0, 1\}$, satisfies
$\mathcal{M}_2(n) = q \bmod 2$, where $q$ is the state reached from the state $0$ by reading the
base-$4$ digits of $n$ with $\delta$, most significant digit first (for $n = 0$ no digit is read,
so $q = 0$).

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 22 (`jis-2026-26.4.1-thm-22`). -/
public theorem_wanted metaAutomaticTwo_dfao (n : ℕ) :
    metaAutomaticTwo n = decide (((Nat.digits 4 n).reverse.foldl
      (fun q d => ([[0, 1, 3, 2], [2, 3, 1, 0], [3, 2, 0, 1], [1, 0, 2, 3]].getD q []).getD d 0)
      0) % 2 = 1)

/-- **Digit formula for $\mathcal{M}_2$.** For a natural number $n$ and $k \ge 0$, let
$d_k = \lfloor n / 4^k \rfloor \bmod 4$ be the $k$-th base-$4$ digit of $n$, and write
$d_k = 2 j_k + i_k$ with $i_k, j_k \in \{0, 1\}$. Let $c_k = i_k + j_k$ if $k \equiv 0 \pmod 3$,
$c_k = j_k$ if $k \equiv 1 \pmod 3$, and $c_k = i_k$ if $k \equiv 2 \pmod 3$. Then the
meta-automatic sequence $\mathcal{M}_2$, read as taking values in $\{0, 1\}$, satisfies
$\mathcal{M}_2(n) = (c_0 + c_1 + \cdots + c_n) \bmod 2$.

The digits $d_k$ with $k > n$ vanish, so the sum runs over all base-$4$ digits of $n$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 25 (`jis-2026-26.4.1-thm-25`). -/
public theorem_wanted metaAutomaticTwo_digit_formula (n : ℕ) :
    metaAutomaticTwo n = decide ((∑ k ∈ Finset.range (n + 1),
      (if k % 3 = 0 then n / 4 ^ k % 4 % 2 + n / 4 ^ k % 4 / 2
        else if k % 3 = 1 then n / 4 ^ k % 4 / 2 else n / 4 ^ k % 4 % 2)) % 2 = 1)

/-- **Right-special factor counts of automatic sequences are regular.** Let $k$ be a natural
number and $a$ an infinite binary word that is $k$-automatic, and for each $n$ let
$\mathrm{RS}_a(n)$ be the set of right-special factors of $a$ of length $n$. Then the integer
sequence $n \mapsto \#\mathrm{RS}_a(n)$ is $k$-regular. Moreover, for every natural number $C$
with $\#\mathrm{RS}_a(n) \le C$ for all $n$, the sequence $n \mapsto \#\mathrm{RS}_a(n)$, taken
with values in $\{0, 1, \ldots, C\}$, is $k$-automatic.

The source also states that this sequence is effectively computable from any automaton for
$a$; that algorithmic claim is not part of this statement.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 28 (`jis-2026-26.4.1-lem-28`). -/
public theorem_wanted rightSpecial_count_regular (k : ℕ) (a : ℕ → Bool)
    (ha : IsKAutomaticSequence k a) :
    IsKRegularSequence k (fun n => ((rightSpecialFactors a n).ncard : ℤ)) ∧
      ∀ C : ℕ, (∀ n, (rightSpecialFactors a n).ncard ≤ C) →
        IsKAutomaticSequence k (fun n => Fin.ofNat (C + 1) (rightSpecialFactors a n).ncard)

/-- **Factor complexity of the Thue–Morse Quarto word versus Thue–Morse.** Let $\mathcal{Q}$ be
the Thue–Morse Quarto sequence and $t$ the Thue–Morse sequence, with factor complexities
$p_{\mathcal{Q}}$ and $p_t$. For every natural number $n$, let $J_n$ be the set of length-$n$
factors of $\mathcal{Q}$ that are not factors of $t$. Then $p_{\mathcal{Q}}(n) = p_t(n) + |J_n|$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 30 (`jis-2026-26.4.1-prop-30`). -/
public theorem_wanted thueMorseQuarto_complexity_eq (n : ℕ) :
    wordFactorComplexity thueMorseQuarto n = wordFactorComplexity thueMorse n +
      (InfiniteWord.factorSet thueMorseQuarto n \ InfiniteWord.factorSet thueMorse n).ncard

/-- **Factor complexity of the Thue–Morse Quarto word at powers of two.** Let $\mathcal{Q}$ be
the Thue–Morse Quarto sequence and $t$ the Thue–Morse sequence, with factor complexities
$p_{\mathcal{Q}}$ and $p_t$, and for a natural number $n$ let $J_n$ be the set of length-$n$
factors of $\mathcal{Q}$ that are not factors of $t$. Then for every natural number $k \ge 4$,
$p_{\mathcal{Q}}(2^k) = 13 \cdot 2^{k-2} - 2$, $p_{\mathcal{Q}}(2^k) = p_t(2^k) + 2^{k-2}$ and
$|J_{2^k}| = 2^{k-2}$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 31 (`jis-2026-26.4.1-thm-31`). -/
public theorem_wanted thueMorseQuarto_complexity_two_pow (k : ℕ) (hk : 4 ≤ k) :
    wordFactorComplexity thueMorseQuarto (2 ^ k) = 13 * 2 ^ (k - 2) - 2 ∧
      wordFactorComplexity thueMorseQuarto (2 ^ k) =
        wordFactorComplexity thueMorse (2 ^ k) + 2 ^ (k - 2) ∧
      (InfiniteWord.factorSet thueMorseQuarto (2 ^ k) \
        InfiniteWord.factorSet thueMorse (2 ^ k)).ncard = 2 ^ (k - 2)

/-- **Factor complexity and right-special factors of the Thue–Morse Quarto word.** Let
$\mathcal{Q}$ be the Thue–Morse Quarto sequence, $p_{\mathcal{Q}}$ its factor complexity and
$\mathrm{RS}_{\mathcal{Q}}(n)$ its set of right-special factors of length $n$. Let $n \ge 16$ and
$k = \lfloor \log_2 n \rfloor$, so that $2^k \le n < 2^{k+1}$. Then
$p_{\mathcal{Q}}(n) = 13 \cdot 2^{k-2} - 2$ if $n = 2^k$,
$p_{\mathcal{Q}}(n) = 4n - 3 \cdot 2^{k-2} - 4$ if $2^k < n \le 2^k + 2^{k-1}$,
$p_{\mathcal{Q}}(n) = 3n + 3 \cdot 2^{k-2} - 3$ if $2^k + 2^{k-1} < n \le 2^k + 3 \cdot 2^{k-2}$,
and $p_{\mathcal{Q}}(n) = 2n + 5 \cdot 2^{k-1} - 2$ if $2^k + 3 \cdot 2^{k-2} < n$. Moreover
$\#\mathrm{RS}_{\mathcal{Q}}(n) = p_{\mathcal{Q}}(n+1) - p_{\mathcal{Q}}(n)$, and
$\#\mathrm{RS}_{\mathcal{Q}}(n)$ equals $4$ if $2^k < n \le 3 \cdot 2^{k-1}$, $3$ if
$3 \cdot 2^{k-1} < n \le 7 \cdot 2^{k-2}$, and $2$ if $7 \cdot 2^{k-2} < n$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 33 (`jis-2026-26.4.1-prop-33`). -/
public theorem_wanted thueMorseQuarto_complexity_formula (n : ℕ) (hn : 16 ≤ n) :
    (n = 2 ^ Nat.log 2 n →
        (wordFactorComplexity thueMorseQuarto n : ℤ) = 13 * 2 ^ (Nat.log 2 n - 2) - 2) ∧
      (2 ^ Nat.log 2 n < n ∧ n ≤ 2 ^ Nat.log 2 n + 2 ^ (Nat.log 2 n - 1) →
        (wordFactorComplexity thueMorseQuarto n : ℤ) =
          4 * n - 3 * 2 ^ (Nat.log 2 n - 2) - 4) ∧
      (2 ^ Nat.log 2 n + 2 ^ (Nat.log 2 n - 1) < n ∧
          n ≤ 2 ^ Nat.log 2 n + 3 * 2 ^ (Nat.log 2 n - 2) →
        (wordFactorComplexity thueMorseQuarto n : ℤ) =
          3 * n + 3 * 2 ^ (Nat.log 2 n - 2) - 3) ∧
      (2 ^ Nat.log 2 n + 3 * 2 ^ (Nat.log 2 n - 2) < n →
        (wordFactorComplexity thueMorseQuarto n : ℤ) =
          2 * n + 5 * 2 ^ (Nat.log 2 n - 1) - 2) ∧
      ((rightSpecialFactors thueMorseQuarto n).ncard : ℤ) =
        wordFactorComplexity thueMorseQuarto (n + 1) - wordFactorComplexity thueMorseQuarto n ∧
      (2 ^ Nat.log 2 n < n ∧ n ≤ 3 * 2 ^ (Nat.log 2 n - 1) →
        (rightSpecialFactors thueMorseQuarto n).ncard = 4) ∧
      (3 * 2 ^ (Nat.log 2 n - 1) < n ∧ n ≤ 7 * 2 ^ (Nat.log 2 n - 2) →
        (rightSpecialFactors thueMorseQuarto n).ncard = 3) ∧
      (7 * 2 ^ (Nat.log 2 n - 2) < n → (rightSpecialFactors thueMorseQuarto n).ncard = 2)

/-- **The meta-automatic sequences have linear factor complexity.** Let $p_{\mathcal{M}_1}$ and
$p_{\mathcal{M}_2}$ be the factor complexities of the meta-automatic sequences $\mathcal{M}_1$
and $\mathcal{M}_2$. Then $p_{\mathcal{M}_1}(n) = \Theta(n)$ and $p_{\mathcal{M}_2}(n) = \Theta(n)$
as $n \to \infty$: for each $i \in \{1, 2\}$ there are real constants $c, C > 0$ with
$c n \le p_{\mathcal{M}_i}(n) \le C n$ for all sufficiently large $n$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 34 (`jis-2026-26.4.1-prop-34`). -/
public theorem_wanted metaAutomatic_complexity_isTheta :
    (fun n : ℕ => (wordFactorComplexity metaAutomaticOne n : ℝ)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ)) ∧
      (fun n : ℕ => (wordFactorComplexity metaAutomaticTwo n : ℝ)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ))

/-- **Factor complexity of $\mathcal{M}_2$ at powers of two.** Let $p(n)$ be the factor
complexity of the meta-automatic sequence $\mathcal{M}_2$, and let $k \ge 3$. If $3 \mid k$, then
$p(2^k) = 5 \cdot 2^{k-1} - 2$; if $3 \nmid k$, then $p(2^k) = 3 \cdot 2^k - 2$. Moreover,
$p(2^{k+3}) = 8\, p(2^k) + 14$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 36 (`jis-2026-26.4.1-prop-36`). -/
public theorem_wanted metaAutomaticTwo_complexity_two_pow (k : ℕ) (hk : 3 ≤ k) :
    (3 ∣ k → wordFactorComplexity metaAutomaticTwo (2 ^ k) = 5 * 2 ^ (k - 1) - 2) ∧
      (¬ 3 ∣ k → wordFactorComplexity metaAutomaticTwo (2 ^ k) = 3 * 2 ^ k - 2) ∧
      wordFactorComplexity metaAutomaticTwo (2 ^ (k + 3)) =
        8 * wordFactorComplexity metaAutomaticTwo (2 ^ k) + 14

/-- **Factor complexity of $\mathcal{M}_2$.** Let $p(n)$ be the factor complexity of the
meta-automatic sequence $\mathcal{M}_2$. Then $p(1) = 2$, and for every $n \ge 2$, writing
$k = \lfloor \log_2 n \rfloor$ (so that $2^k \le n < 2^{k+1}$), the following hold.
If $k \equiv 0 \pmod 3$, then $p(n) = 2n + 2^{k-1} - 2$ when $n \le 2^k + 1$,
$p(n) = 4n - (3 \cdot 2^{k-1} + 4)$ when $2^k + 1 \le n \le 7 \cdot 2^{k-2} + 1$, and
$p(n) = 2n + 2^{k+1} - 2$ when $n \ge 7 \cdot 2^{k-2} + 1$.
If $k \equiv 1 \pmod 3$, then $p(n) = 2n + 2^k - 2$ when $n \le 2^k + 1$,
$p(n) = 4n - (2^k + 4)$ when $2^k + 1 \le n \le 3 \cdot 2^{k-1} + 1$, and
$p(n) = 2n + 2^{k+1} - 2$ when $n \ge 3 \cdot 2^{k-1} + 1$.
If $k \equiv 2 \pmod 3$, then $p(n) = 2n + 2^k - 2$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 37 (`jis-2026-26.4.1-prop-37`). -/
public theorem_wanted metaAutomaticTwo_complexity_formula :
    wordFactorComplexity metaAutomaticTwo 1 = 2 ∧
    ∀ n : ℕ, 2 ≤ n →
      (Nat.log 2 n % 3 = 0 →
        (n ≤ 2 ^ Nat.log 2 n + 1 → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ (Nat.log 2 n - 1) - 2)) ∧
        (2 ^ Nat.log 2 n + 1 ≤ n ∧ n ≤ 7 * 2 ^ (Nat.log 2 n - 2) + 1 →
          (wordFactorComplexity metaAutomaticTwo n : ℤ) =
            4 * n - (3 * 2 ^ (Nat.log 2 n - 1) + 4)) ∧
        (7 * 2 ^ (Nat.log 2 n - 2) + 1 ≤ n → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ (Nat.log 2 n + 1) - 2))) ∧
      (Nat.log 2 n % 3 = 1 →
        (n ≤ 2 ^ Nat.log 2 n + 1 → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ Nat.log 2 n - 2)) ∧
        (2 ^ Nat.log 2 n + 1 ≤ n ∧ n ≤ 3 * 2 ^ (Nat.log 2 n - 1) + 1 →
          (wordFactorComplexity metaAutomaticTwo n : ℤ) = 4 * n - (2 ^ Nat.log 2 n + 4)) ∧
        (3 * 2 ^ (Nat.log 2 n - 1) + 1 ≤ n → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ (Nat.log 2 n + 1) - 2))) ∧
      (Nat.log 2 n % 3 = 2 →
        (wordFactorComplexity metaAutomaticTwo n : ℤ) = 2 * n + (2 ^ Nat.log 2 n - 2))

end

end MetaMathlibExt
