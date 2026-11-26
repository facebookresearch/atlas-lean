/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Infix
public import MathlibExt.Combinatorics.Enumerative.AntiTribonacci
public import MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsumGap
public import MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsumPalindromeLimit

/-!
# Problems from the OEIS settled with Walnut

Statements from Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to
Solve Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article
25.3.8 (arXiv:2503.04122): the theorem of Hajdu, Tijdeman, and Varga on
`(x-1)^c (x+1)^d` modulo `3`, Kimberling's conjecture on the anti-Tribonacci
sequence, and the greedy `3`-subsumfree sequences `S_{1,2,3}`, `S_{1,3,4}`,
`S_{1,4,5}`; the gaps between unsums of upper Wythoff numbers (Section 2, Lemmas 1-9)
and Zaslavsky's description of the anti-Fibonacci numbers (Theorem 11).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Mex of $\{1, 2, 3, 6\}$.** The least positive integer not in $\{1, 2, 3, 6\}$ is $4$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_example : antiTribonacciMex {1, 2, 3, 6} = 4 := by
  decide +kernel

/-- **Members of a greedy $3$-subsumfree sequence below a bound.** For natural numbers $x$, $y$
and $z$ (the source takes $x < y < z$), let $S_{x,y,z}$ consist of $x$, $y$, $z$ and every natural
number $n > z$ that is not a sum $a + b + c$ of members $a < b < c$ of $S_{x,y,z}$ smaller than
$n$. This definition gives, for each natural number $m$, the finite set of members of $S_{x,y,z}$
below $m$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 6. -/
public def greedySubsumfreeBelow (x y z : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | m + 1 =>
    let s := greedySubsumfreeBelow x y z m
    if m = x ∨ m = y ∨ m = z ∨
        (z < m ∧ ¬ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a < b ∧ b < c ∧ a + b + c = m) then
      insert m s
    else s

/-- **First members of $S_{1,2,3}$.** The members of the greedy $3$-subsumfree sequence
$S_{1,2,3}$ below $26$ are exactly $1, 2, 3, 4, 5, 13, 14, 15, 25$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 6. -/
public theorem greedySubsumfreeBelow_one_two_three :
    greedySubsumfreeBelow 1 2 3 26 = {1, 2, 3, 4, 5, 13, 14, 15, 25} := by
  decide +kernel

/-- **Hajdu–Tijdeman–Varga theorem on $(x-1)^c (x+1)^d$ modulo $3$.** Let $c$ and $d$ be natural
numbers. If none of the coefficients of $x^0, x^1, \dots, x^{c+d}$ in the integer polynomial
$(x-1)^c (x+1)^d$ is divisible by $3$, then there are natural numbers $i > j$ such that $c + d + 1$
equals $3^j$, $2 \cdot 3^j$, $3^i + 3^j$ or $2 \cdot 3^i + 3^j$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 10 (`jis-2025-25.3.8-thm-10`), citing Hajdu, Tijdeman, and Varga. -/
public theorem_wanted coeff_not_dvd_three_shape (c d : ℕ)
    (h : ∀ k ≤ c + d,
      ¬ (3 : ℤ) ∣ (((Polynomial.X - 1) ^ c * (Polynomial.X + 1) ^ d : Polynomial ℤ)).coeff k) :
    ∃ i j : ℕ, j < i ∧ (c + d + 1 = 3 ^ j ∨ c + d + 1 = 2 * 3 ^ j ∨
      c + d + 1 = 3 ^ i + 3 ^ j ∨ c + d + 1 = 2 * 3 ^ i + 3 ^ j)

/-- **Membership in three greedy 3-subsumfree sequences.** For $x < y < z$, the greedy
$3$-subsumfree sequence $S_{x,y,z}$ consists of $x$, $y$, $z$ and every $m > z$ that is not the
sum of three different members of $S_{x,y,z}$ smaller than $m$. For every positive integer $n$:
$n \in S_{1,2,3}$ if and only if $n \in \{1, 5, 13\}$ or $n \bmod 23 \in \{2, 3, 4, 14, 15\}$;
$n \in S_{1,3,4}$ if and only if $n \in \{1, 7, 19\}$ or
$n \bmod 33 \in \{3, 4, 5, 6, 20, 21, 22\}$; and $n \in S_{1,4,5}$ if and only if
$n \in \{1, 9, 25\}$ or $n \bmod 43 \in \{4, 5, 6, 7, 8, 26, 27, 28, 29\}$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 15 (`jis-2025-25.3.8-thm-15`). -/
public theorem_wanted mem_greedySubsumfree_iff {z : ℕ} (hz : 0 < z) :
    (z ∈ greedySubsumfreeBelow 1 2 3 (z + 1) ↔
      z ∈ ({1, 5, 13} : Finset ℕ) ∨ z % 23 ∈ ({2, 3, 4, 14, 15} : Finset ℕ)) ∧
    (z ∈ greedySubsumfreeBelow 1 3 4 (z + 1) ↔
      z ∈ ({1, 7, 19} : Finset ℕ) ∨ z % 33 ∈ ({3, 4, 5, 6, 20, 21, 22} : Finset ℕ)) ∧
    (z ∈ greedySubsumfreeBelow 1 4 5 (z + 1) ↔
      z ∈ ({1, 9, 25} : Finset ℕ) ∨ z % 43 ∈ ({4, 5, 6, 7, 8, 26, 27, 28, 29} : Finset ℕ))


/-- **Digit sums between markers are two less than Fibonacci numbers.** For every $j$, the digit
sum of the $j$-th word between markers of the unsum gap sequence, plus $2$, is a Fibonacci
number: it equals $F_m$ for some natural number $m$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 2 (`jis-2025-25.3.8-lem-2`). -/
public theorem_wanted upperWythoffUnsumWord_sum_add_two_isFib (j : ℕ) :
    ∃ m, (upperWythoffUnsumWord j).sum + 2 = Nat.fib m

/-- **Digit sums of the words between markers.** Let $F_n$ be the Fibonacci numbers, with
$F_0 = 0$ and $F_1 = 1$. For every $j$ (words counted from zero), the digit sum of the $j$-th
word between markers of the unsum gap sequence, plus $2$, equals $F_{\lfloor j/2 \rfloor + 5}$.

So the digit sums are $3, 3, 6, 6, 11, \ldots$; adding the preceding marker digit $2$ gives
$F_5, F_5, F_6, F_6, F_7, \ldots$, which is how the source's Lemma 3 must be read, since the
bare digit sum of the first word is $3 \ne F_5 = 5$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 3 (`jis-2025-25.3.8-lem-3`). -/
public theorem_wanted upperWythoffUnsumWord_sum_add_two (j : ℕ) :
    (upperWythoffUnsumWord j).sum + 2 = Nat.fib (j / 2 + 5)

/-- **A word $3V3$ between markers is followed by a word starting with $3V$.** Let $V$ be a
finite word of natural numbers, and suppose that the $j$-th word between markers of the unsum
gap sequence is $3V3$. Then $3V$ is a prefix of the $(j+1)$-th word between markers, and if the
$(j+1)$-th word has the same digit sum as the $j$-th word, then the two words are equal.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 6 (`jis-2025-25.3.8-lem-6`). -/
public theorem_wanted upperWythoffUnsumWord_prefix_next {j : ℕ} {V : List ℕ}
    (h : upperWythoffUnsumWord j = 3 :: V ++ [3]) :
    (3 :: V) <+: upperWythoffUnsumWord (j + 1) ∧
      ((upperWythoffUnsumWord (j + 1)).sum = (upperWythoffUnsumWord j).sum →
        upperWythoffUnsumWord (j + 1) = upperWythoffUnsumWord j)

/-- **When one palindrome is a prefix of the next.** Let $g_k$ be the $k$-th gap between
consecutive unsums (OEIS A260317), counted from zero, and let $m_0 < m_1 < \cdots$ be the
markers, the indices $k \ge 10$ with $g_k = 2$, in increasing order. For $i \ge 1$ let $W_i$
be the word of the gaps $g_k$ with $m_{2i-2} < k < m_{2i-1}$, in increasing order of $k$. Then
for every $i \ge 1$, the word $W_i$ is a prefix of $W_{i+1}$ if and only if $i$ is odd.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 7 (`jis-2025-25.3.8-lem-7`). -/
public theorem_wanted upperWythoffUnsumPalindrome_isPrefix_succ_iff {i : ℕ} (hi : 1 ≤ i) :
    upperWythoffUnsumPalindrome i <+: upperWythoffUnsumPalindrome (i + 1) ↔ Odd i

/-- **Recursion for the words $W_i$ of the unsum gap sequence.** For each $i$ let $V_i$ be the
word $W_i$ with its first and last digit removed, write $|W|$ for the length of a word $W$, and
denote concatenation of words by juxtaposition. For every $i \ge 2$: if $i$ is odd, then
$W_{i+1} = W_i \, 5 \, V_{i-1} \, 3$; if $i$ is even, then $W_{i+1} = 3 \, V_i \, 5 \, W_{i-1}$;
and in both cases $|W_{i+1}| = |W_i| + |W_{i-1}|$. Moreover $|W_1| = 1$, $|W_2| = 2$, and
$|W_i| = F_{i+1}$ for every $i \ge 1$, where $F_m$ is the $m$-th Fibonacci number ($F_0 = 0$,
$F_1 = 1$).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 8 (`jis-2025-25.3.8-lem-8`). -/
public theorem_wanted upperWythoffUnsumPalindrome_succ :
    (∀ i, 2 ≤ i →
      (Odd i → upperWythoffUnsumPalindrome (i + 1) = upperWythoffUnsumPalindrome i ++
        5 :: (upperWythoffUnsumPalindrome (i - 1)).tail.dropLast ++ [3]) ∧
      (Even i → upperWythoffUnsumPalindrome (i + 1) =
        3 :: (upperWythoffUnsumPalindrome i).tail.dropLast ++
          5 :: upperWythoffUnsumPalindrome (i - 1)) ∧
      (upperWythoffUnsumPalindrome (i + 1)).length =
        (upperWythoffUnsumPalindrome i).length + (upperWythoffUnsumPalindrome (i - 1)).length) ∧
    (upperWythoffUnsumPalindrome 1).length = 1 ∧ (upperWythoffUnsumPalindrome 2).length = 2 ∧
    ∀ i, 1 ≤ i → (upperWythoffUnsumPalindrome i).length = Nat.fib (i + 1)

/-- **Iterates of the period-doubling substitution.** Write the period-doubling substitution
$a \mapsto ab$, $b \mapsto aa$ over the letters $a = 1$ and $b = 0$, so that it sends $1$ to $10$
and $0$ to $11$. The $n$-th period-doubling iterate is the word obtained by applying this
substitution $n$ times to the one-letter word $1$; the iterates begin $1$, $10$, $1011$,
$10111010$, and their limit is the period-doubling word (Walnut's PD).

The source's prose takes $a = 0$ and $b = 1$, but its Walnut definition `antifib`
(`PD[k]=@1` gives $9 + 10k$) and its displayed anti-Fibonacci numbers $0, 3, 9, 13, \ldots$ need
the first letter of PD to be $1$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def periodDoublingWord : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => (periodDoublingWord n).flatMap fun c => if c = 1 then [1, 0] else [1, 1]

/-- **The period-doubling word.** For a natural number $k$, the letter at index $k$ (indices start
at $0$) of the period-doubling word is the letter at index $k$ of the word obtained by applying
the period-doubling substitution $1 \mapsto 10$, $0 \mapsto 11$ to the one-letter word $1$ a total
of $\lfloor \log_2 k \rfloor + 1$ times, where $\lfloor \log_2 0 \rfloor$ is taken to be $0$.
That word has length $2^{\lfloor \log_2 k \rfloor + 1} \le 2k + 2$, so it contains index $k$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def periodDoubling (k : ℕ) : ℕ := (periodDoublingWord (Nat.log 2 k + 1)).getD k 0

/-- **Length of the period-doubling iterates.** For every natural number $n$, the word obtained by
applying the period-doubling substitution $1 \mapsto 10$, $0 \mapsto 11$ to the one-letter word
$1$ a total of $n$ times has length $2^n$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem length_periodDoublingWord (n : ℕ) : (periodDoublingWord n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : ∀ L : List ℕ, (L.flatMap fun c => if c = 1 then [1, 0] else [1, 1]).length =
        2 * L.length := by
      intro L
      induction L with
      | nil => rfl
      | cons c L ihL =>
        simp only [List.flatMap_cons, List.length_append, ihL, List.length_cons]
        split_ifs <;> simp <;> omega
    rw [periodDoublingWord, h, ih, Nat.pow_succ, Nat.mul_comm]

private theorem periodDoublingWord_prefix_succ (n : ℕ) :
    periodDoublingWord n <+: periodDoublingWord (n + 1) := by
  induction n with
  | zero => exact ⟨[0], rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t.flatMap fun c => if c = 1 then [1, 0] else [1, 1], ?_⟩
    change (periodDoublingWord n).flatMap (fun c => if c = 1 then [1, 0] else [1, 1]) ++ _ =
      (periodDoublingWord (n + 1)).flatMap (fun c => if c = 1 then [1, 0] else [1, 1])
    rw [← ht, List.flatMap_append]

private theorem periodDoublingWord_prefix {n m : ℕ} (h : n ≤ m) :
    periodDoublingWord n <+: periodDoublingWord m := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (periodDoublingWord_prefix_succ _)

/-- **Letters of the period-doubling iterates.** Let $w_m$ be the word obtained by applying the
period-doubling substitution $1 \mapsto 10$, $0 \mapsto 11$ to the one-letter word $1$ a total of
$m$ times. For all natural numbers $m$ and $k$ with $k < 2^m$, the letter of $w_m$ at index $k$
(indices start at $0$) equals the letter of the period-doubling word at index $k$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem periodDoublingWord_getD {m k : ℕ} (hk : k < 2 ^ m) :
    (periodDoublingWord m).getD k 0 = periodDoubling k := by
  have hk' : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by decide) k
  unfold periodDoubling
  have key : ∀ {a b : ℕ}, a ≤ b → k < 2 ^ a →
      (periodDoublingWord a).getD k 0 = (periodDoublingWord b).getD k 0 := by
    intro a b hab hka
    have hp := periodDoublingWord_prefix hab
    have hla : k < (periodDoublingWord a).length := by
      rw [length_periodDoublingWord]; exact hka
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hla,
      List.getElem?_eq_getElem (lt_of_lt_of_le hla hp.length_le), Option.getD_some]
    exact hp.getElem hla
  rcases le_total m (Nat.log 2 k + 1) with h | h
  · exact key h hk
  · exact (key h hk').symm

/-- **First letters of the period-doubling word.** The letters at indices $0, 1, \ldots, 7$ of the
period-doubling word (the fixed point of $1 \mapsto 10$, $0 \mapsto 11$ that starts with $1$) are
$1, 0, 1, 1, 1, 0, 1, 0$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem periodDoubling_small :
    (List.range 8).map periodDoubling = [1, 0, 1, 1, 1, 0, 1, 0] := by
  decide +kernel

/-- **The anti-Fibonacci construction.** For each $n \ge 0$, entry $n$ of the construction is the
triple $(A_{n+1}, B_{n+1}, C_{n+1})$ of natural numbers together with the finite set $U_{n+1}$ of
values used so far. Entry $0$ is $(1, 2, 3)$ with $U_1 = \{1, 2, 3\}$. For $n \ge 1$, $A_{n+1}$ is
the least positive integer not in $U_n$, $B_{n+1}$ is the least positive integer not in
$U_n \cup \{A_{n+1}\}$, $C_{n+1} = A_{n+1} + B_{n+1}$, and
$U_{n+1} = U_n \cup \{A_{n+1}, B_{n+1}, C_{n+1}\}$.

The $C_n$ are the anti-Fibonacci numbers (OEIS A075326 without its initial $0$) and the missing
numbers $A_1, B_1, A_2, B_2, \dots$ are the non-anti-Fibonacci numbers $Y_1, Y_2, \dots$
(OEIS A249031).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciState : ℕ → (ℕ × ℕ × ℕ) × Finset ℕ
  | 0 => ((1, 2, 3), {1, 2, 3})
  | n + 1 =>
    let s := (antiFibonacciState n).2
    let a := antiTribonacciMex s
    let b := antiTribonacciMex (insert a s)
    ((a, b, a + b), insert (a + b) (insert b (insert a s)))

/-- **First summands of the anti-Fibonacci construction.** For $n \ge 1$, $A_n$ is the first
entry of the $n$-th triple $(A_n, B_n, C_n)$ of the anti-Fibonacci construction: $A_1 = 1$, and
for $n \ge 2$, $A_n$ is the least positive integer that is not among the values $A_k$, $B_k$,
$C_k$ with $1 \le k < n$. At $n = 0$ the definition gives $A_0 = A_1 = 1$.

In the source's notation $A_n = Y_{2n-1}$, where $Y_1 < Y_2 < \dots$ are the non-anti-Fibonacci
numbers.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciA (n : ℕ) : ℕ := (antiFibonacciState (n - 1)).1.1

/-- **Second summands of the anti-Fibonacci construction.** For $n \ge 1$, $B_n$ is the second
entry of the $n$-th triple $(A_n, B_n, C_n)$ of the anti-Fibonacci construction: $B_1 = 2$, and
for $n \ge 2$, $B_n$ is the second smallest positive integer that is not among the values $A_k$,
$B_k$, $C_k$ with $1 \le k < n$. At $n = 0$ the definition gives $B_0 = B_1 = 2$.

In the source's notation $B_n = Y_{2n}$, where $Y_1 < Y_2 < \dots$ are the non-anti-Fibonacci
numbers.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciB (n : ℕ) : ℕ := (antiFibonacciState (n - 1)).1.2.1

/-- **Anti-Fibonacci numbers.** For $n \ge 1$, the anti-Fibonacci number $X_n = C_n$ is the third
entry of the $n$-th triple $(A_n, B_n, C_n)$ of the anti-Fibonacci construction, so
$C_n = A_n + B_n$ and $C_1 = 3$. At $n = 0$ the definition gives $C_0 = C_1 = 3$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciC (n : ℕ) : ℕ := (antiFibonacciState (n - 1)).1.2.2

/-- **First anti-Fibonacci and non-anti-Fibonacci numbers.** In the anti-Fibonacci construction
with triples $(A_n, B_n, C_n)$, the first four anti-Fibonacci numbers are $C_1 = 3$, $C_2 = 9$,
$C_3 = 13$ and $C_4 = 18$, and $(A_1, B_1) = (1, 2)$, $(A_2, B_2) = (4, 5)$,
$(A_3, B_3) = (6, 7)$ and $(A_4, B_4) = (8, 10)$.

Since $A_1, B_1, A_2, B_2, \dots$ are the non-anti-Fibonacci numbers, the first eight
non-anti-Fibonacci numbers are $1, 2, 4, 5, 6, 7, 8, 10$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiFibonacci_small :
    (List.range 4).map (fun n => antiFibonacciC (n + 1)) = [3, 9, 13, 18] ∧
      (List.range 4).map (fun n => (antiFibonacciA (n + 1), antiFibonacciB (n + 1))) =
        [(1, 2), (4, 5), (6, 7), (8, 10)] := by
  decide +kernel

/-- **Zaslavsky's formulas for the anti-Fibonacci numbers.** Let $A_1 = 1$, $B_1 = 2$,
$C_1 = 3$, and for $n \ge 1$ let $A_{n+1} < B_{n+1}$ be the two smallest positive integers not
among $A_1, B_1, C_1, \ldots, A_n, B_n, C_n$ and $C_{n+1} = A_{n+1} + B_{n+1}$. Let
$\mathrm{PD}[0], \mathrm{PD}[1], \ldots$ be the letters of the period-doubling word, the fixed
point of $1 \mapsto 10$, $0 \mapsto 11$ starting with $1$. Then for every $k \ge 0$,
$C_{2k+1} = 10k + 3$, $C_{2k+2} = 10k + 8 + \mathrm{PD}[k]$, $A_{2k+1} = 5k + 1$,
$B_{2k+1} = 5k + 2$, $A_{2k+2} = 5k + 3 + \mathrm{PD}[k]$, and $B_{2k+2} = 5(k + 1)$.

In the source's notation the anti-Fibonacci numbers are $X_n = C_n$ and the
non-anti-Fibonacci numbers are $Y_{2n-1} = A_n$ and $Y_{2n} = B_n$, so the formulas read
$X_{2k+1} = 10k + 3$, $X_{2k+2} = 10k + 8 + \mathrm{PD}[k]$, $Y_{4k+1} = 5k + 1$,
$Y_{4k+2} = 5k + 2$, $Y_{4k+3} = 5k + 3 + \mathrm{PD}[k]$ and $Y_{4k+4} = 5(k + 1)$ (the
source's $Y_{4k} = 5k$ for $k \ge 1$). The source's prose writes the period-doubling word
over letters $a, b$ with $a = 0$, but its Walnut code and its values $X_2 = 9$ and $Y_3 = 4$
need $\mathrm{PD}[0] = 1$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 11 (`jis-2025-25.3.8-thm-11`), due to Zaslavsky. -/
public theorem_wanted zaslavsky_antiFibonacci (k : ℕ) :
    antiFibonacciC (2 * k + 1) = 3 + 10 * k ∧
      antiFibonacciC (2 * k + 2) = 8 + 10 * k + periodDoubling k ∧
      antiFibonacciA (2 * k + 1) = 5 * k + 1 ∧ antiFibonacciB (2 * k + 1) = 5 * k + 2 ∧
      antiFibonacciA (2 * k + 2) = 5 * k + 3 + periodDoubling k ∧
      antiFibonacciB (2 * k + 2) = 5 * (k + 1)

end

end MetaMathlibExt
