/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.List.Destutter
public import Mathlib.Data.Nat.Fib.Zeckendorf
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
public import WantedExt.NumberTheory.Digits.BasePhiRepresentationsWanted

/-!
# The structure of base phi expansions

Statements from F. Michel Dekking, *The Structure of Base Phi Expansions*,
INTEGERS 24 (2024), Article A24 (arXiv:2305.08349).

The base phi expansion `β(N)` of a natural number `N` is its unique finite
expansion `N = ∑ dᵢ φ ^ i` with digits `0, 1` and no two adjacent digits `1`.
It is encoded, as in `BasePhiRepresentationsWanted`, by the finite set
`S : Finset ℤ` of positions of its digits `1`. Statements about `β(N)` are stated
for every `S` with `IsBasePhiExpansion N S`; existence and uniqueness of `S` are
Bergman's theorem and are not assumed. The positive part `β⁺(N)` is
`S.filter (0 ≤ ·)` and the negative part `β⁻(N)` is `S.filter (· < 0)`.
A free-group word identity of the paper such as
`β(N) = 1000 (10)⁻¹ β(M) (01)⁻¹ 1001` is stated as the corresponding operation on
the position sets, together with the digit facts that make the cancellations
`(10)⁻¹` and `(01)⁻¹` valid.
-/

open scoped goldenRatio

namespace MetaMathlibExt

@[expose] public section

/-- **Base phi expansion.** Let $\varphi$ be the golden ratio. A finite set $S$ of integers, read as
the positions of the digits $1$ of a finite expansion with digits $0$ and $1$, is a base phi
expansion of the natural number $N$ when it is a Bergman expansion (no two digits $1$ are
adjacent: $i \in S$ implies $i + 1 \notin S$) and its value $\sum_{i \in S} \varphi^i$ equals $N$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 1 (definition of `β(N)`). -/
def IsBasePhiExpansion (N : ℕ) (S : Finset ℤ) : Prop :=
  IsBergmanExpansion S ∧ basePhiValue S = N

/-- **Base phi expansion of zero.** The empty set of positions, the expansion with no digit $1$, is
a base phi expansion of $0$: it has no two adjacent digits $1$, and its value, the empty sum, is
equal to $0$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 1. -/
theorem isBasePhiExpansion_zero : IsBasePhiExpansion 0 ∅ := by
  refine ⟨fun i hi => by simp at hi, ?_⟩
  simp [basePhiValue]

/-- **Base phi expansion of one.** The set $\{0\}$, read as the positions of the digits $1$, is a
base phi expansion of $1$: the expansion with a single digit $1$ at position $0$ has no two
adjacent digits $1$, and its value $\varphi^0$ equals $1$, where $\varphi$ is the golden ratio.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Table 1. -/
theorem isBasePhiExpansion_one : IsBasePhiExpansion 1 {0} := by
  refine ⟨fun i hi => by simp at hi ⊢; omega, ?_⟩
  simp [basePhiValue]

/-- **Digit block of an expansion.** Let $S$ be a finite set of integers, read as the positions of
the digits $1$ of an expansion with digits $d_i$, so $d_i = 1$ if $i \in S$ and $d_i = 0$
otherwise. For an integer $k$ and a finite word $w = w_0 w_1 \cdots w_{m-1}$ over the natural
numbers, $w$ occurs as a digit block of $S$ at position $k$ when the digits
$d_k d_{k-1} \cdots d_{k-m+1}$, read from the highest position down, are the letters of $w$: for
every $i < m$, $d_{k-i} = 1$ holds exactly when $w_i = 1$. A letter $1$ stands for the digit $1$
and any other letter for the digit $0$; the empty word occurs at every position.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Sections 6 and 7 (digit blocks `d_{m-1} ⋯ d_0` and
`d_{-1} ⋯ d_{-m}`). -/
def HasDigitBlock (S : Finset ℤ) : ℤ → List ℕ → Prop
  | _, [] => True
  | k, b :: w => (k ∈ S ↔ b = 1) ∧ HasDigitBlock S (k - 1) w

/-- **The empty digit block occurs everywhere.** For every finite set $S$ of integers, read as the
positions of the digits $1$ of an expansion, and every integer $k$, the empty word occurs as a
digit block of $S$ at position $k$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 6. -/
theorem hasDigitBlock_nil (S : Finset ℤ) (k : ℤ) : HasDigitBlock S k [] := trivial

/-- **Peeling off the leading letter of a digit block.** Let $S$ be a finite set of integers, read
as the positions of the digits $1$ of an expansion. For every integer $k$, every natural number
$b$ and every finite word $w$ over the natural numbers, the word $bw$ (the letter $b$ followed by
$w$) occurs as a digit block of $S$ at position $k$ if and only if both $k \in S$ holds exactly
when $b = 1$, and $w$ occurs as a digit block of $S$ at position $k - 1$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 6. -/
theorem hasDigitBlock_cons (S : Finset ℤ) (k : ℤ) (b : ℕ) (w : List ℕ) :
    HasDigitBlock S k (b :: w) ↔ (k ∈ S ↔ b = 1) ∧ HasDigitBlock S (k - 1) w :=
  Iff.rfl

/-- **Occurrence set of a digit block.** For an integer $k$ and a word $w = w_1 w_2 \cdots w_\ell$
of natural numbers, the occurrence set of $w$ at position $k$ is the set of natural numbers $N$
that have a base phi expansion $S$ (the set of positions of its digits $1$) whose digits
$d_k d_{k-1} \cdots d_{k-\ell+1}$ spell $w$: for each $j = 1, \dots, \ell$, the position
$k - j + 1$ lies in $S$ if and only if $w_j = 1$.

The paper's $R_w$, the set of $N$ whose expansion has the end block $w$ at positions
$\ell - 1, \dots, 0$, is the case $k = \ell - 1$, and $R_{\cdot w}$, the set of $N$ whose digits at
positions $-1, \dots, -\ell$ spell $w$, is the case $k = -1$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Sections 6 and 7 (occurrence sequences `R_w`). -/
def basePhiOccurrences (k : ℤ) (w : List ℕ) : Set ℕ :=
  {N | ∃ S, IsBasePhiExpansion N S ∧ HasDigitBlock S k w}

/-- **A base phi expansion of 1 ends in the digit 1.** The number $1$ lies in the occurrence
set of the one-letter digit block $1$ placed at position $0$ (the paper's $R_1$): some base phi
expansion of $1$ has the digit $1$ at position $0$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 6. -/
theorem one_mem_basePhiOccurrences_one : 1 ∈ basePhiOccurrences 0 [1] :=
  ⟨{0}, isBasePhiExpansion_one, by simp [HasDigitBlock]⟩

/-- **Generalized Beatty sequence.** Let $\varphi$ be the golden ratio. For integers $p, q, r$, the
generalized Beatty sequence $V(p, q, r)$ is the integer sequence defined for every natural number
$n$, including $n = 0$, by $V(p, q, r)(n) = p\lfloor n\varphi \rfloor + qn + r$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 5. -/
noncomputable def generalizedBeatty (p q r : ℤ) (n : ℕ) : ℤ :=
  p * ⌊(n : ℝ) * φ⌋ + q * n + r

/-- **Generalized Beatty sequence at zero.** Let $\varphi$ be the golden ratio. For all integers
$p, q, r$, the generalized Beatty sequence $V(p, q, r)(n) = p\lfloor n\varphi \rfloor + qn + r$
takes the value $V(p, q, r)(0) = r$ at $n = 0$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 6 (`V₀`). -/
theorem generalizedBeatty_zero (p q r : ℤ) : generalizedBeatty p q r 0 = r := by
  simp [generalizedBeatty]

/-- **Generalized Beatty sequence at one.** Let $\varphi$ be the golden ratio. For all integers
$p, q, r$, the generalized Beatty sequence $V(p, q, r)(n) = p\lfloor n\varphi \rfloor + qn + r$
takes the value $V(p, q, r)(1) = p + q + r$ at $n = 1$, since $\lfloor \varphi \rfloor = 1$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 5. -/
theorem generalizedBeatty_one (p q r : ℤ) : generalizedBeatty p q r 1 = p + q + r := by
  have h : ⌊φ⌋ = 1 := by
    rw [Int.floor_eq_iff]
    exact ⟨by simpa using Real.one_lt_goldenRatio.le, by
      simpa [one_add_one_eq_two] using Real.goldenRatio_lt_two⟩
  simp [generalizedBeatty, h]

/-- **Terms of a generalized Beatty sequence.** For integers $p$, $q$ and $r$, this is the set of
integers $p \lfloor n\varphi \rfloor + qn + r$ for natural numbers $n \ge 1$, where $\varphi$ is
the golden ratio: the set of terms $V(p, q, r)(n)$, $n \ge 1$, of the generalized Beatty
sequence $V(p, q, r)$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 5. -/
def beattySet (p q r : ℤ) : Set ℤ :=
  {x | ∃ n : ℕ, 1 ≤ n ∧ x = generalizedBeatty p q r n}

/-- **Terms of a generalized Beatty sequence from index zero.** For integers $p$, $q$ and $r$, this
is the set of integers $p \lfloor n\varphi \rfloor + qn + r$ for all natural numbers $n \ge 0$,
where $\varphi$ is the golden ratio: the set of values $V(p, q, r)(n)$, $n \ge 0$, of the
generalized Beatty sequence $V(p, q, r)$, which the paper denotes $V_0(p, q, r)$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 6 (definition of `V₀`). -/
def beattySet₀ (p q r : ℤ) : Set ℤ :=
  Set.range (generalizedBeatty p q r)

/-- **The value at one is a term of a generalized Beatty sequence.** Let $\varphi$ be the golden
ratio. For all integers $p, q, r$, the number $p + q + r$ is a term
$p \lfloor n \varphi \rfloor + q n + r$, $n \ge 1$, of the generalized Beatty sequence
$V(p, q, r)$; it is the term at $n = 1$, since $\lfloor \varphi \rfloor = 1$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 5. -/
theorem add_add_mem_beattySet (p q r : ℤ) : p + q + r ∈ beattySet p q r :=
  ⟨1, le_rfl, (generalizedBeatty_one p q r).symm⟩

/-- **The initial term of a generalized Beatty set.** For all integers $p$, $q$ and $r$, the
integer $r$ belongs to the set $V_0(p, q, r)$ of terms $p \lfloor n\varphi \rfloor + qn + r$,
$n \ge 0$, of the generalized Beatty sequence, where $\varphi$ is the golden ratio; indeed $r$
is its term at $n = 0$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 6. -/
theorem mem_beattySet₀_self (p q r : ℤ) : r ∈ beattySet₀ p q r :=
  ⟨0, generalizedBeatty_zero p q r⟩

/-- **The blocks $10^{2m} \cdot 1$ and $10^{2m+1} \cdot 0$ never occur.** For every $m \ge 1$, no
base phi expansion of a natural number has digits
$d_{2m} \cdots d_0 \cdot d_{-1} = 10^{2m} \cdot 1$, and none has digits
$d_{2m+1} \cdots d_0 \cdot d_{-1} = 10^{2m+1} \cdot 0$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 1 (`integers-2024-A24-lem-1`). -/
public theorem_wanted basePhi_no_block_one_zeros_dot (m : ℕ) (hm : 1 ≤ m) (N : ℕ)
    (S : Finset ℤ) (hS : IsBasePhiExpansion N S) :
    ¬ HasDigitBlock S (2 * m) (1 :: List.replicate (2 * m) 0 ++ [1]) ∧
      ¬ HasDigitBlock S (2 * m + 1) (1 :: List.replicate (2 * m + 1) 0 ++ [0])

/-- **Propagation principle for base phi expansions.** Let $w = w_1 \cdots w_8$ be a word of
length $8$ over the natural numbers. Say that a base phi expansion $S$ (the set of positions of its
digits $1$) contains $w$ centrally if for each $j = 1, \dots, 8$ the position $4 - j$ lies in $S$
exactly when $w_j = 1$, that is, if its digits $d_3 d_2 d_1 d_0 \cdot d_{-1} d_{-2} d_{-3} d_{-4}$
spell $w$. If no base phi expansion of any natural number $N \le 17$ contains $w$ centrally, then
no base phi expansion of any natural number contains $w$ centrally.

The hypothesis includes $N = 0$, as in the paper's proof.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 2 (a) (`integers-2024-A24-lem-2`). -/
public theorem_wanted basePhi_propagation_principle (w : List ℕ) (hw : w.length = 8)
    (h : ∀ N ≤ 17, ∀ S, IsBasePhiExpansion N S → ¬ HasDigitBlock S 3 w) (N : ℕ)
    (S : Finset ℤ) (hS : IsBasePhiExpansion N S) : ¬ HasDigitBlock S 3 w

/-- **Generalized Beatty sequences composed with the Wythoff sequences.** Let $\varphi$ be the
golden ratio and, for integers $a$, $b$, $c$ and natural numbers $n$, let
$V(a, b, c)(n) = a \lfloor n\varphi \rfloor + bn + c$. Let $A(n) = \lfloor n\varphi \rfloor$ and
$B(n) = \lfloor n\varphi \rfloor + n$ be the lower and upper Wythoff sequences. For all integers
$p$, $q$, $r$ and every natural number $n \ge 1$,
$V(p, q, r)(A(n)) = V(p + q, p, r - p)(n)$ and $V(p, q, r)(B(n)) = V(2p + q, p + q, r)(n)$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 3 (`integers-2024-A24-lem-3`). -/
public theorem_wanted generalizedBeatty_comp_wythoff (p q r : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    generalizedBeatty p q r ⌊(n : ℝ) * φ⌋₊ = generalizedBeatty (p + q) p (r - p) n ∧
      generalizedBeatty p q r (⌊(n : ℝ) * φ⌋₊ + n) =
        generalizedBeatty (2 * p + q) (p + q) r n

/-- **Complement of the lower Wythoff part of a generalized Beatty sequence.** Let $\varphi$ be the
golden ratio and, for integers $a$, $b$, $c$, let $V(a, b, c)$ be the set of integers
$a \lfloor n\varphi \rfloor + bn + c$ for natural numbers $n \ge 1$. Let $p$, $q$, $r$ be
integers with $p + q > 0$ and $2p + q > 0$. If $U$ and $W$ are disjoint sets of integers with
$U \cup W = V(p, q, r)$ and $U = V(p + q, p, r - p)$, then $W = V(2p + q, p + q, r)$.

This is the converse of the composition lemma. The hypotheses $p + q > 0$ and $2p + q > 0$ say
that the sequence $n \mapsto p \lfloor n\varphi \rfloor + qn + r$ is increasing, as the paper's
sequences are.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 4 (`integers-2024-A24-lem-4`). -/
public theorem_wanted beattySet_complement_of_lowerWythoff (p q r : ℤ) (hpq : 0 < p + q)
    (h2pq : 0 < 2 * p + q) (U W : Set ℤ) (hdisj : Disjoint U W)
    (hunion : U ∪ W = beattySet p q r) (hU : U = beattySet (p + q) p (r - p)) :
    W = beattySet (2 * p + q) (p + q) r

/-- **First differences of a generalized Beatty sequence.** Let $\varphi$ be the golden ratio, for
integers $p, q, r$ let $V(p, q, r)$ be the sequence $n \mapsto p\lfloor n\varphi \rfloor + qn + r$
on the natural numbers, and let $x_0 x_1 x_2 \cdots$ be the infinite Fibonacci word. For all
integers $p, q, r$ and every $n \ge 1$, the difference $V(p, q, r)(n+1) - V(p, q, r)(n)$ equals
$p + q$ if $x_{n-1} = 1$ and $2p + q$ if $x_{n-1} = 0$. Conversely, for all integers $a, b$ and
every sequence $v$ of integers indexed by the natural numbers such that, for every $n \ge 1$,
$v(n+1) - v(n)$ equals $b$ if $x_{n-1} = 1$ and $a$ if $x_{n-1} = 0$, there is an integer $r'$
with $v(n) = V(a - b, 2b - a, r')(n)$ for every $n \ge 1$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 5 (`integers-2024-A24-lem-5`). -/
public theorem_wanted generalizedBeatty_diff_eq_fibInf (p q r : ℤ) :
    (∀ n : ℕ, 1 ≤ n → generalizedBeatty p q r (n + 1) - generalizedBeatty p q r n =
      if fibInf (n - 1) then p + q else 2 * p + q) ∧
    ∀ (a b : ℤ) (v : ℕ → ℤ),
      (∀ n : ℕ, 1 ≤ n → v (n + 1) - v n = if fibInf (n - 1) then b else a) →
        ∃ r' : ℤ, ∀ n : ℕ, 1 ≤ n → v n = generalizedBeatty (a - b) (2 * b - a) r' n

/-- **For $m \ge 2$, no base phi expansion has end block $1\,0^{2m}\,1$.** Let $m \ge 2$, let $N$
be a natural number and let $S$ be a base phi expansion of $N$, given as the set of positions of
its digits $1$. Then the digits $d_{2m+1} d_{2m} \cdots d_1 d_0$ at positions $2m+1, \dots, 0$ are
not $1\,0^{2m}\,1$: it is not the case that $2m+1 \in S$, $0 \in S$ and no $i$ with
$1 \le i \le 2m$ lies in $S$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 6 (`integers-2024-A24-lem-6`). -/
public theorem_wanted basePhi_no_end_block_one_zeros_one (m : ℕ) (hm : 2 ≤ m) (N : ℕ)
    (S : Finset ℤ) (hS : IsBasePhiExpansion N S) :
    ¬ HasDigitBlock S (2 * m + 1) (1 :: List.replicate (2 * m) 0 ++ [1])

/-- **End blocks $u1 \cdot 0$ and $u0 \cdot 0$ of consecutive numbers.** Let $u$ be a nonempty
word of length $m - 1$, read as the digits $d_{m-1} \cdots d_1$ (a letter $1$ is a digit $1$,
any other letter a digit $0$), such that the word $u1$ has no two adjacent letters $1$. Then
for every $N \ge 1$, some base phi expansion of $N$ has digits
$d_{m-1} \cdots d_1 d_0 \cdot d_{-1} = u1 \cdot 0$ if and only if some base phi expansion of
$N - 1$ has digits $d_{m-1} \cdots d_1 d_0 \cdot d_{-1} = u0 \cdot 0$.

The hypothesis that $u1$ has no $11$ is the paper's implicit standing assumption on digit blocks:
for $u = 1$ the block $11 \cdot 0$ never occurs, while $10 \cdot 0$ occurs in the expansion
$10 \cdot 01$ of $2$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 7 (`integers-2024-A24-lem-7`). -/
public theorem_wanted basePhi_end_block_one_iff_pred (u : List ℕ) (hu : u ≠ [])
    (hz : List.IsChain (fun a b => ¬ (a = 1 ∧ b = 1)) (u ++ [1])) (N : ℕ) (hN : 1 ≤ N) :
    N ∈ basePhiOccurrences u.length (u ++ [1, 0]) ↔
      N - 1 ∈ basePhiOccurrences u.length (u ++ [0, 0])

/-- **Lucas numbers from Fibonacci numbers.** For every natural number $n$,
$F_n + 3F_{n+1} = L_{n+2}$, where $F_j$ is the $j$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$) and
$L_j$ is the $j$-th Lucas number ($L_0 = 2$, $L_1 = 1$).

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 9 (`integers-2024-A24-lem-9`). -/
public theorem_wanted fib_add_three_mul_fib_succ_eq_lucasNumber (n : ℕ) :
    Nat.fib n + 3 * Nat.fib (n + 1) = lucasNumber (n + 2)

/-- **Border words and codes of Lucas numbers.** Let $n \ge 1$, and write $F_k$ for the Fibonacci
numbers and $L_k$ for the Lucas numbers. Let $S_1, S_2, S_3, S_4$ be base phi expansions (sets
of positions of the digits $1$) of $L_{2n}$, $L_{2n+1}$, $L_{2n+1} + 1$ and $L_{2n+2} - 1$
respectively, and let $S_k^-$ be the set of negative positions in $S_k$. Then
$S_1^- = \{-2n\}$, $S_2^- = \{-2j : 1 \le j \le n\}$,
$S_3^- = \{-2n-2\} \cup \{1 - 2j : 1 \le j \le n\}$ and $S_4^- = \{-2n-2\}$; that is, the
negative parts $\beta^-$ of these numbers are the words $0^{2n-2}01$, $(01)^n$, $(10)^n 01$ and
$0^{2n}01$. Moreover $\sum_{i \in S_1^-} F_{i+2n} = 0$,
$\sum_{i \in S_2^-} F_{i+2n} = F_{2n-1} - 1$, $\sum_{i \in S_3^-} F_{i+2n+2} = F_{2n+2} - 1$
and $\sum_{i \in S_4^-} F_{i+2n+2} = 0$.

In the paper's notation, with $\gamma^-(N)$ the word $\beta^-(N)$ with its final $01$ removed,
this says $\gamma^-(L_{2n}) = 0^{2n-2}$, $\gamma^-(L_{2n+1}) = (01)^{n-1}$,
$\gamma^-(L_{2n+1}+1) = (10)^n$ and $\gamma^-(L_{2n+2}-1) = 0^{2n}$, and that the codes $C(N)$
of the words $\gamma^-(N)$, which equal $\sum_{i \in \beta^-(N)} F_{i+2j}$ when $\beta^-(N)$
has length $2j$, are $C(L_{2n}) = 0$, $C(L_{2n+1}) = F_{2n-1} - 1$,
$C(L_{2n+1}+1) = F_{2n+2} - 1$ and $C(L_{2n+2}-1) = 0$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 10 (`integers-2024-A24-lem-10`). -/
public theorem_wanted basePhi_lucas_border_codes (n : ℕ) (hn : 1 ≤ n) (S₁ S₂ S₃ S₄ : Finset ℤ)
    (h₁ : IsBasePhiExpansion (lucasNumber (2 * n)) S₁)
    (h₂ : IsBasePhiExpansion (lucasNumber (2 * n + 1)) S₂)
    (h₃ : IsBasePhiExpansion (lucasNumber (2 * n + 1) + 1) S₃)
    (h₄ : IsBasePhiExpansion (lucasNumber (2 * n + 2) - 1) S₄) :
    S₁.filter (· < 0) = {-(2 * n : ℤ)} ∧
    S₂.filter (· < 0) = (Finset.Icc 1 n).image (fun j : ℕ => -(2 * j : ℤ)) ∧
    S₃.filter (· < 0) =
      insert (-(2 * n + 2 : ℤ)) ((Finset.Icc 1 n).image (fun j : ℕ => 1 - (2 * j : ℤ))) ∧
    S₄.filter (· < 0) = {-(2 * n + 2 : ℤ)} ∧
    ∑ i ∈ S₁.filter (· < 0), Nat.fib (i + 2 * n).toNat = 0 ∧
    ∑ i ∈ S₂.filter (· < 0), Nat.fib (i + 2 * n).toNat = Nat.fib (2 * n - 1) - 1 ∧
    ∑ i ∈ S₃.filter (· < 0), Nat.fib (i + 2 * n + 2).toNat = Nat.fib (2 * n + 2) - 1 ∧
    ∑ i ∈ S₄.filter (· < 0), Nat.fib (i + 2 * n + 2).toNat = 0

/-- **The digit blocks $10 \cdot 1$ and $00 \cdot 1$ around the radix point.** Let $\varphi$ be the
golden ratio, let $N \ge 1$ and let $S$ be a base phi expansion of $N$, with digits $d_i$
($d_i = 1$ if $i \in S$, else $d_i = 0$). Then $d_1 d_0 \cdot d_{-1} \ne 10 \cdot 1$, and
$d_1 d_0 \cdot d_{-1} = 00 \cdot 1$ if and only if $N = 3 \lfloor n \varphi \rfloor + n + 1$ for
some integer $n \ge 1$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Proposition 1 (`integers-2024-A24-prop-1`). -/
public theorem_wanted basePhi_digits_dot_one (N : ℕ) (hN : 1 ≤ N) (S : Finset ℤ)
    (hS : IsBasePhiExpansion N S) :
    ¬ HasDigitBlock S 1 [1, 0, 1] ∧
      (HasDigitBlock S 1 [0, 0, 1] ↔ (N : ℤ) ∈ beattySet 3 1 1)

/-- **End blocks of length at most three ending in $0$.** Let $\varphi$ be the golden ratio.
For integers $p, q, r$ let $V(p, q, r) = \{p \lfloor n\varphi \rfloor + qn + r : n \ge 1\}$ and
$V_0(p, q, r) = \{p \lfloor n\varphi \rfloor + qn + r : n \ge 0\}$. For a word $w$ of length $\ell$
let $R_w$ be the set of natural numbers having a base phi expansion whose digits
$d_{\ell-1} \cdots d_0$ at positions $\ell - 1, \dots, 0$ spell $w$. Then for every natural number
$N \ge 1$: $N \in R_0$ if and only if $N \in V(-1, 3, 0)$; $N \in R_{00}$ if and only if
$N \in V_0(1, 2, 0) \cup V(3, 1, 1)$; $N \in R_{10}$ if and only if $N \in V(1, 2, -1)$;
$N \in R_{010}$ if and only if $N \in V(1, 2, -1)$; $N \in R_{000}$ if and only if
$N \in V_0(4, 3, 0) \cup V(3, 1, 1)$; and $N \in R_{100}$ if and only if $N \in V(3, 1, -1)$.
Moreover $V_0(1, 2, 0)$ and $V_0(4, 3, 0)$ are each disjoint from $V(3, 1, 1)$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Proposition 2 (`integers-2024-A24-prop-2`). -/
public theorem_wanted basePhi_short_end_blocks_zero (N : ℕ) (hN : 1 ≤ N) :
    (N ∈ basePhiOccurrences 0 [0] ↔ (N : ℤ) ∈ beattySet (-1) 3 0) ∧
    (N ∈ basePhiOccurrences 1 [0, 0] ↔ (N : ℤ) ∈ beattySet₀ 1 2 0 ∪ beattySet 3 1 1) ∧
    (N ∈ basePhiOccurrences 1 [1, 0] ↔ (N : ℤ) ∈ beattySet 1 2 (-1)) ∧
    (N ∈ basePhiOccurrences 2 [0, 1, 0] ↔ (N : ℤ) ∈ beattySet 1 2 (-1)) ∧
    (N ∈ basePhiOccurrences 2 [0, 0, 0] ↔ (N : ℤ) ∈ beattySet₀ 4 3 0 ∪ beattySet 3 1 1) ∧
    (N ∈ basePhiOccurrences 2 [1, 0, 0] ↔ (N : ℤ) ∈ beattySet 3 1 (-1)) ∧
    Disjoint (beattySet₀ 1 2 0) (beattySet 3 1 1) ∧ Disjoint (beattySet₀ 4 3 0) (beattySet 3 1 1)

/-- **Short prefixes of the negative parts of base phi expansions.** Let $\varphi$ be the golden
ratio. For integers $p, q, r$ let $V(p, q, r) = \{p \lfloor n\varphi \rfloor + qn + r : n \ge 1\}$
and $V_0(p, q, r) = \{p \lfloor n\varphi \rfloor + qn + r : n \ge 0\}$. For a word $w$ of length
$\ell$ let $R_{\cdot w}$ be the set of natural numbers having a base phi expansion whose digits
$d_{-1} d_{-2} \cdots d_{-\ell}$ spell $w$, where $d_i = 1$ if position $i$ carries a digit $1$
and $d_i = 0$ otherwise. Then for every natural number $N \ge 2$:
$N \in R_{\cdot 0}$ if and only if $N \in V(1, 2, -1) \cup V(1, 2, 0) \cup V(1, 2, 1)$;
$N \in R_{\cdot 1}$ if and only if $N \in V(3, 1, 1)$;
$N \in R_{\cdot 10}$ if and only if $N \in V(3, 1, 1)$;
$N \in R_{\cdot 00}$ if and only if $N \in V(3, 1, 2) \cup V(3, 1, 3) \cup V(3, 1, 4)$;
$N \in R_{\cdot 01}$ if and only if $N \in V_0(4, 3, 2) \cup V_0(4, 3, 3) \cup V_0(4, 3, 4)$;
$N \in R_{\cdot 010}$ if and only if $N \in V_0(4, 3, 2) \cup V_0(4, 3, 3) \cup V_0(4, 3, 4)$;
$N \in R_{\cdot 000}$ if and only if $N \in V(4, 3, -1) \cup V(4, 3, 0) \cup V(4, 3, 1)$;
$N \in R_{\cdot 001}$ if and only if $N \in V(7, 4, 2) \cup V(7, 4, 3) \cup V(7, 4, 4)$;
$N \in R_{\cdot 100}$ if and only if $N \in V(4, 3, -2)$; and
$N \in R_{\cdot 101}$ if and only if $N \in V(7, 4, 1)$.

The bound $N \ge 2$ makes the negative part nonempty: the expansion of $1$ is $1$ itself. The first
equivalence follows the reading $R_{\cdot 0} = V(1, 2, [-1, 0, 1])$ of the paper's Figure 3: as
printed, $V(2, 1, -1) \cup V(2, 1, 0) \cup V(2, 1, 1)$ misses $6$, whose expansion is
$1010 \cdot 0001$, and contains $12$, whose expansion is $100000 \cdot 101001$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Proposition 3 (`integers-2024-A24-prop-3`). -/
public theorem_wanted basePhi_short_negative_prefixes (N : ℕ) (hN : 2 ≤ N) :
    (N ∈ basePhiOccurrences (-1) [0] ↔
      (N : ℤ) ∈ beattySet 1 2 (-1) ∪ beattySet 1 2 0 ∪ beattySet 1 2 1) ∧
    (N ∈ basePhiOccurrences (-1) [1] ↔ (N : ℤ) ∈ beattySet 3 1 1) ∧
    (N ∈ basePhiOccurrences (-1) [1, 0] ↔ (N : ℤ) ∈ beattySet 3 1 1) ∧
    (N ∈ basePhiOccurrences (-1) [0, 0] ↔
      (N : ℤ) ∈ beattySet 3 1 2 ∪ beattySet 3 1 3 ∪ beattySet 3 1 4) ∧
    (N ∈ basePhiOccurrences (-1) [0, 1] ↔
      (N : ℤ) ∈ beattySet₀ 4 3 2 ∪ beattySet₀ 4 3 3 ∪ beattySet₀ 4 3 4) ∧
    (N ∈ basePhiOccurrences (-1) [0, 1, 0] ↔
      (N : ℤ) ∈ beattySet₀ 4 3 2 ∪ beattySet₀ 4 3 3 ∪ beattySet₀ 4 3 4) ∧
    (N ∈ basePhiOccurrences (-1) [0, 0, 0] ↔
      (N : ℤ) ∈ beattySet 4 3 (-1) ∪ beattySet 4 3 0 ∪ beattySet 4 3 1) ∧
    (N ∈ basePhiOccurrences (-1) [0, 0, 1] ↔
      (N : ℤ) ∈ beattySet 7 4 2 ∪ beattySet 7 4 3 ∪ beattySet 7 4 4) ∧
    (N ∈ basePhiOccurrences (-1) [1, 0, 0] ↔ (N : ℤ) ∈ beattySet 4 3 (-2)) ∧
    (N ∈ basePhiOccurrences (-1) [1, 0, 1] ↔ (N : ℤ) ∈ beattySet 7 4 1)

/-- **Embedding of base phi expansions into Zeckendorf expansions.** Let $\varphi$ be the golden
ratio and let $F_j$ be the Fibonacci numbers, $F_0 = 0$, $F_1 = F_2 = 1$. For a natural number $M$
let $Z(M)$ be the set of indices $i \ge 0$ such that $F_{i+2}$ occurs in the Zeckendorf
representation of $M$, so that $M = \sum_{i \in Z(M)} F_{i+2}$. Let $N$ be a natural number, let
$S$ be a base phi expansion of $N$ (the set of positions of its digits $1$), and let $s(N)$ be the
number of integers $n$ with $1 \le n \le N$ and $3 \lfloor n \varphi \rfloor + n + 1 < N$. Then
$\{i \in S : i \ge 0\} = Z(N + s(N))$.

Since $3 \lfloor n \varphi \rfloor + n + 1 > N$ for $n \ge N$, $s(N)$ is the number of all $n \ge 1$
with $3 \lfloor n \varphi \rfloor + n + 1 < N$, that is, the number of $M < N$ whose digit at
position $-1$ is $1$, as in the paper's proof. Both formulas for $s(N)$ printed in the paper are off
by one: $\max\{k : 3 \lfloor k \varphi \rfloor + k \le N\}$ gives $s(4) = 1$, but $Z(5) = \{3\}$
while $4 = \varphi^2 + 1 + \varphi^{-2}$ has nonnegative positions $\{0, 2\}$; and
$\max\{k : 3 \lfloor k \varphi \rfloor + k + 1 \le N\} - 1$ gives $s(6) = 0$, but
$Z(6) = \{0, 3\}$ while $6 = \varphi^3 + \varphi + \varphi^{-4}$ has nonnegative positions
$\{1, 3\}$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 1 (`integers-2024-A24-thm-1`). -/
public theorem_wanted basePhi_positive_part_eq_zeckendorf (N : ℕ) (S : Finset ℤ)
    (hS : IsBasePhiExpansion N S) :
    S.filter (0 ≤ ·) =
      ((Nat.zeckendorf
          (N + ((Finset.Icc 1 N).filter (fun n => generalizedBeatty 3 1 1 n < N)).card)).map
        (fun k : ℕ => (k : ℤ) - 2)).toFinset

/-- **Recursive structure theorem for base phi expansions, part (A).** Let $n \ge 2$ and let $L_j$
be the Lucas numbers; $k$ denotes a natural number, and base phi expansions are given as sets of
positions of digits $1$.
(I) If $1 \le k \le L_{2n-2} - 1$, $T$ is a base phi expansion of $L_{2n-1} + k$ and $S$ is a base
phi expansion of $L_{2n+1} + k$, then $2n-1 \in T$, $2n-2 \notin T$, $1-2n \notin T$, $-2n \in T$
and $S = (T \setminus \{2n-1, -2n\}) \cup \{2n+1, 1-2n, -2n-2\}$.
(K) If $1 \le k \le L_{2n-2} - 1$, $T$ is a base phi expansion of $L_{2n-1} + k$ and $S$ is a base
phi expansion of $L_{2n+1} + L_{2n-1} + k$, then $2n-1 \in T$, $2n-2 \notin T$, $1-2n \notin T$,
$-2n \in T$ and $S = (T \setminus \{-2n\}) \cup \{2n+1, -2n-2\}$.
(J) If $0 \le k \le L_{2n-3}$, $T$ is a base phi expansion of $L_{2n-2} + k$ and $S$ is a base phi
expansion of $L_{2n+1} + L_{2n-2} + k$, then $2n-2 \in T$, $2n-3 \notin T$, $3-2n \notin T$,
$2-2n \in T$ and $S = (T \setminus \{2-2n\}) \cup \{2n+1, 1-2n, -2n-2\}$.

In the paper's word notation, where $\beta(M)$ is the expansion of $M$ written as a word of digits
(with $\cdot$ between positions $0$ and $-1$) and $(10)^{-1}$, $(01)^{-1}$ cancel a leading $10$
and a trailing $01$, these are
$\beta(L_{2n+1}+k) = 1000\,(10)^{-1}\,\beta(L_{2n-1}+k)\,(01)^{-1}\,1001$,
$\beta(L_{2n+1}+L_{2n-1}+k) = 1010\,(10)^{-1}\,\beta(L_{2n-1}+k)\,(01)^{-1}\,0001$ and
$\beta(L_{2n+1}+L_{2n-2}+k) = 10010\,(10)^{-1}\,\beta(L_{2n-2}+k)\,(01)^{-1}\,001001$. The
source's ranges $k \le L_{2n} - 1$ for (I) and (K) and $k \le L_{2n-1}$ for (J) are too wide: for
$n = 2$ and $k = 3$, $\beta(L_3 + 3) = \beta(7) = 10000 \cdot 0001$ has no digit $1$ at
position $3$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 2 (`integers-2024-A24-thm-2`). -/
public theorem_wanted basePhi_recursive_structure (n : ℕ) (T S : Finset ℤ) :
    (2 ≤ n → ∀ k, 1 ≤ k → k + 1 ≤ lucasNumber (2 * n - 2) →
      IsBasePhiExpansion (lucasNumber (2 * n - 1) + k) T →
      IsBasePhiExpansion (lucasNumber (2 * n + 1) + k) S →
        (2 * n - 1 : ℤ) ∈ T ∧ (2 * n - 2 : ℤ) ∉ T ∧ (1 - 2 * n : ℤ) ∉ T ∧ -(2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 1 : ℤ) (insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
            ((T.erase (2 * n - 1 : ℤ)).erase (-(2 * n : ℤ)))))) ∧
    (2 ≤ n → ∀ k, 1 ≤ k → k + 1 ≤ lucasNumber (2 * n - 2) →
      IsBasePhiExpansion (lucasNumber (2 * n - 1) + k) T →
      IsBasePhiExpansion (lucasNumber (2 * n + 1) + lucasNumber (2 * n - 1) + k) S →
        (2 * n - 1 : ℤ) ∈ T ∧ (2 * n - 2 : ℤ) ∉ T ∧ (1 - 2 * n : ℤ) ∉ T ∧ -(2 * n : ℤ) ∈ T ∧
        S = insert (2 * n + 1 : ℤ) (insert (-2 * n - 2 : ℤ) (T.erase (-(2 * n : ℤ))))) ∧
    (2 ≤ n → ∀ k, k ≤ lucasNumber (2 * n - 3) →
      IsBasePhiExpansion (lucasNumber (2 * n - 2) + k) T →
      IsBasePhiExpansion (lucasNumber (2 * n + 1) + lucasNumber (2 * n - 2) + k) S →
        (2 * n - 2 : ℤ) ∈ T ∧ (2 * n - 3 : ℤ) ∉ T ∧ (3 - 2 * n : ℤ) ∉ T ∧ (2 - 2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 1 : ℤ) (insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
            (T.erase (2 - 2 * n : ℤ)))))

/-- **Recursive structure of base phi expansions on Lucas intervals.** Let $n \ge 1$, let $L_k$ be
the Lucas numbers, and for $j \ge 0$ let $\Lambda_{2j}$ be the set of natural numbers in
$[L_{2j}, L_{2j+1}]$ and $\Lambda_{2j+1}$ the set of natural numbers in
$[L_{2j+1} + 1, L_{2j+2} - 1]$. Let $T$ be a base phi expansion of a natural number $M$ and $S$ a
base phi expansion of a natural number $N$, both given as sets of positions of digits $1$. Then:
(A)(a) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n}$, then $2n-1 \in T$, $2n-2 \notin T$,
$1-2n \notin T$, $-2n \in T$ and $S = (T \setminus \{2n-1, -2n\}) \cup \{2n+1, 1-2n, -2n-2\}$;
(A)(b) if $M \in \Lambda_{2n-2}$ and $N = M + L_{2n+1}$, then $3-2n \notin T$, $2-2n \in T$ and
$S = (T \setminus \{2-2n\}) \cup \{2n+1, 1-2n, -2n-2\}$;
(A)(c) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n+1}$, then $2n-1 \in T$, $1-2n \notin T$,
$-2n \in T$ and $S = (T \setminus \{-2n\}) \cup \{2n+1, -2n-2\}$;
(B)(a) if $M \in \Lambda_{2n}$ and $N = M + L_{2n+1}$, then $2n \in T$, $2n-1 \notin T$,
$1-2n \notin T$, $-2n \in T$ and $S = (T \setminus \{2n, -2n\}) \cup \{2n+2, -2n-2\}$;
(B)(b) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n+2}$, then $S = T \cup \{2n+2, -2n-2\}$;
(B)(c) if $M \in \Lambda_{2n}$ and $N = M + L_{2n+2}$, then $S = T \cup \{2n+2, -2n-2\}$.

In the paper's word notation, where $\beta(M)$ is the expansion of $M$ written as a word of digits
(with $\cdot$ between positions $0$ and $-1$) and $(10)^{-1}$, $(01)^{-1}$ cancel a leading $10$
and a trailing $01$, (A)(a) is
$\beta(M + L_{2n}) = 1000\,(10)^{-1}\,\beta(M)\,(01)^{-1}\,1001$ and (B)(b) is
$\beta(M + L_{2n+2}) = 100\,\beta(M)\,01$; the digit conditions on $T$ make the cancellations
$(10)^{-1}$ and $(01)^{-1}$ valid. In (B)(c) the source writes $\beta(N - L_{2n+1})$ for
$N \in \Lambda_{2n} + L_{2n+2}$; the shift $L_{2n+2}$ is used here, since as printed $n = 1$ and
$N = 10$ give $10\,\beta(6)\,01 = 101010 \cdot 000101$, which is not $\beta(10) = 10100 \cdot 0101$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 3 (`integers-2024-A24-thm-3`). -/
public theorem_wanted basePhi_recursive_structure_lucas_intervals (n : ℕ) (hn : 1 ≤ n)
    (M : ℕ) (T S : Finset ℤ) (hT : IsBasePhiExpansion M T) :
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n)) S →
        (2 * n - 1 : ℤ) ∈ T ∧ (2 * n - 2 : ℤ) ∉ T ∧ (1 - 2 * n : ℤ) ∉ T ∧ -(2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 1 : ℤ) (insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
            ((T.erase (2 * n - 1 : ℤ)).erase (-(2 * n : ℤ)))))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 2)) (lucasNumber (2 * n - 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        (3 - 2 * n : ℤ) ∉ T ∧ (2 - 2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 1 : ℤ) (insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
            (T.erase (2 - 2 * n : ℤ))))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        (2 * n - 1 : ℤ) ∈ T ∧ (1 - 2 * n : ℤ) ∉ T ∧ -(2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 1 : ℤ) (insert (-2 * n - 2 : ℤ) (T.erase (-(2 * n : ℤ))))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        (2 * n : ℤ) ∈ T ∧ (2 * n - 1 : ℤ) ∉ T ∧ (1 - 2 * n : ℤ) ∉ T ∧ -(2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 2 : ℤ) (insert (-2 * n - 2 : ℤ) ((T.erase (2 * n : ℤ)).erase (-(2 * n : ℤ))))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 2)) S →
        S = insert (2 * n + 2 : ℤ) (insert (-2 * n - 2 : ℤ) T)) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 2)) S →
        S = insert (2 * n + 2 : ℤ) (insert (-2 * n - 2 : ℤ) T))

/-- **Short end blocks.** Let $\varphi$ be the golden ratio. For integers $p, q, r$ let
$V(p, q, r)$ be the set of the integers $p \lfloor n\varphi \rfloor + qn + r$ with $n \ge 1$, and
$V_0(p, q, r)$ the same set with $n \ge 0$. Then for every natural number $N \ge 1$:
some base phi expansion of $N$ has digit $1$ at position $0$ if and only if
$N \in V_0(1, 2, 1)$; some base phi expansion of $N$ has digits $1, 0$ at positions $1, 0$ if
and only if $N \in V(1, 2, -1)$; some base phi expansion of $N$ has digits $0, 0, 0$ at
positions $1, 0, -1$ if and only if $N \in V_0(1, 2, 0)$; and some base phi expansion of $N$
has digits $0, 0, 1$ at positions $1, 0, -1$ if and only if $N \in V(3, 1, 1)$.

In the paper's notation: $R_1 = V_0(1, 2, 1)$, $R_{10} = V(1, 2, -1)$,
$R_{00 \cdot 0} = V_0(1, 2, 0)$ and $R_{00 \cdot 1} = V(3, 1, 1)$, on the numbers $N \ge 1$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 6 (`integers-2024-A24-thm-6`). -/
public theorem_wanted basePhi_short_end_blocks (N : ℕ) (hN : 1 ≤ N) :
    (N ∈ basePhiOccurrences 0 [1] ↔ (N : ℤ) ∈ beattySet₀ 1 2 1) ∧
    (N ∈ basePhiOccurrences 1 [1, 0] ↔ (N : ℤ) ∈ beattySet 1 2 (-1)) ∧
    (N ∈ basePhiOccurrences 1 [0, 0, 0] ↔ (N : ℤ) ∈ beattySet₀ 1 2 0) ∧
    (N ∈ basePhiOccurrences 1 [0, 0, 1] ↔ (N : ℤ) ∈ beattySet 3 1 1)

/-- **End blocks ending in $0$ are Lucas–Wythoff sequences.** Let $\varphi$ be the golden ratio
and $L_n$ the Lucas numbers. For integers $p, q, r$ let $V(p, q, r)$ be the set of the integers
$p \lfloor n\varphi \rfloor + qn + r$ with $n \ge 1$, and $V_0(p, q, r)$ the same set with
$n \ge 0$. For a word $w = w_{m-1} \cdots w_0$ of length $m$ over the natural numbers, let $R_w$ be
the set of natural numbers $N$ with a base phi expansion whose digit at position $i$ is $1$
exactly when $w_i = 1$, for $i = m - 1, \dots, 0$. Then:
(1) for every word $w = w_{m-1} \cdots w_0$ of length $m \ge 2$ with letters in $\{0, 1\}$, no two
consecutive letters $1$, $w_0 = 0$ and $w \ne 0^m$, there is an integer $\gamma \le 0$ such that
every natural number $N \ge 1$ lies in $R_w$ if and only if it lies in
$V(L_{m-2}, L_{m-3}, \gamma)$ when $w_{m-1} = 0$, respectively in $V(L_{m-1}, L_{m-2}, \gamma)$
when $w_{m-1} = 1$;
(2) for every $m \ge 1$ and every natural number $N \ge 1$, $N \in R_{0^{2m}}$ if and only if
$N \in V(L_{2m}, L_{2m-1}, 1) \cup V_0(L_{2m-1}, L_{2m-2}, 0)$, and $N \in R_{0^{2m+1}}$ if and
only if $N \in V_0(L_{2m+1}, L_{2m}, 0) \cup V(L_{2m}, L_{2m-1}, 1)$; moreover
$V(L_{2m}, L_{2m-1}, 1)$ and $V_0(L_{2m-1}, L_{2m-2}, 0)$ are disjoint, and
$V_0(L_{2m+1}, L_{2m}, 0)$ and $V(L_{2m}, L_{2m-1}, 1)$ are disjoint.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 7 (`integers-2024-A24-thm-7`). -/
public theorem_wanted basePhi_end_blocks_lucasWythoff :
    (∀ w : List ℕ, 2 ≤ w.length → (∀ d ∈ w, d ≤ 1) →
      List.IsChain (fun a b => ¬ (a = 1 ∧ b = 1)) w → w.getLast? = some 0 →
      w ≠ List.replicate w.length 0 →
        ∃ γ : ℤ, γ ≤ 0 ∧ ∀ N : ℕ, 1 ≤ N →
          (N ∈ basePhiOccurrences (w.length - 1) w ↔
            (N : ℤ) ∈ (if w.head? = some 0 then
              beattySet (lucasNumber (w.length - 2)) (lucasNumber (w.length - 3)) γ
            else beattySet (lucasNumber (w.length - 1)) (lucasNumber (w.length - 2)) γ))) ∧
    ∀ m : ℕ, 1 ≤ m → ∀ N : ℕ, 1 ≤ N →
      (N ∈ basePhiOccurrences (2 * m - 1) (List.replicate (2 * m) 0) ↔
        (N : ℤ) ∈ beattySet (lucasNumber (2 * m)) (lucasNumber (2 * m - 1)) 1 ∪
          beattySet₀ (lucasNumber (2 * m - 1)) (lucasNumber (2 * m - 2)) 0) ∧
      (N ∈ basePhiOccurrences (2 * m) (List.replicate (2 * m + 1) 0) ↔
        (N : ℤ) ∈ beattySet₀ (lucasNumber (2 * m + 1)) (lucasNumber (2 * m)) 0 ∪
          beattySet (lucasNumber (2 * m)) (lucasNumber (2 * m - 1)) 1) ∧
      Disjoint (beattySet (lucasNumber (2 * m)) (lucasNumber (2 * m - 1)) 1)
        (beattySet₀ (lucasNumber (2 * m - 1)) (lucasNumber (2 * m - 2)) 0) ∧
      Disjoint (beattySet₀ (lucasNumber (2 * m + 1)) (lucasNumber (2 * m)) 0)
        (beattySet (lucasNumber (2 * m)) (lucasNumber (2 * m - 1)) 1)

/-- **End blocks ending in $1$ are Lucas–Wythoff sequences.** Let $\varphi$ be the golden ratio
and $L_n$ the Lucas numbers. For integers $p, q, r$ let $V(p, q, r)$ be the set of the integers
$p \lfloor n\varphi \rfloor + qn + r$ with $n \ge 1$, and $V_0(p, q, r)$ the same set with
$n \ge 0$. For a word $w = w_{m-1} \cdots w_0$ of length $m$ over the natural numbers, let $R_w$ be
the set of natural numbers $N$ with a base phi expansion whose digit at position $i$ is $1$
exactly when $w_i = 1$, for $i = m - 1, \dots, 0$. Then:
(1) for every word $w = w_{m-1} \cdots w_0$ of length $m \ge 3$ with letters in $\{0, 1\}$, no two
consecutive letters $1$ and $w_0 = 1$, which is not of the form $0^k 1$ or $1 0^k 1$ with
$k \ge 2$, and for which $R_w$ is nonempty, there is an integer $\gamma \le 0$ such that every
natural number $N \ge 1$ lies in $R_w$ if and only if it lies in $V(L_{m-2}, L_{m-3}, \gamma)$
when $w_{m-1} = 0$, respectively in $V(L_{m-1}, L_{m-2}, \gamma)$ when $w_{m-1} = 1$;
(2) for every $m \ge 1$ and every natural number $N \ge 1$: $N \in R_{0^{2m} 1}$ if and only if
$N \in V_0(L_{2m+1}, L_{2m}, 1)$; $N \in R_{0^{2m+1} 1}$ if and only if
$N \in V_0(L_{2m+1}, L_{2m}, 1)$; $N \notin R_{1 0^{2m} 1}$; and $N \in R_{1 0^{2m+1} 1}$ if and
only if $N \in V(L_{2m+2}, L_{2m+1}, 1 - L_{2m+1})$.

The hypothesis that $R_w$ is nonempty is added to the printed statement: as printed, the
statement fails for $w = 01001$, which never occurs (its end block $1001$ is excluded), while
every $V(p, q, \gamma)$ is nonempty; the source's proof derives its description of $R_w$ only
under the assumption $R_w \ne \emptyset$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 8 (`integers-2024-A24-thm-8`). -/
public theorem_wanted basePhi_end_blocks_one_lucasWythoff :
    (∀ w : List ℕ, 3 ≤ w.length → (∀ d ∈ w, d ≤ 1) →
      List.IsChain (fun a b => ¬ (a = 1 ∧ b = 1)) w → w.getLast? = some 1 →
      (∀ k : ℕ, 2 ≤ k → w ≠ List.replicate k 0 ++ [1]) →
      (∀ k : ℕ, 2 ≤ k → w ≠ 1 :: List.replicate k 0 ++ [1]) →
      (basePhiOccurrences (w.length - 1) w).Nonempty →
        ∃ γ : ℤ, γ ≤ 0 ∧ ∀ N : ℕ, 1 ≤ N →
          (N ∈ basePhiOccurrences (w.length - 1) w ↔
            (N : ℤ) ∈ (if w.head? = some 0 then
              beattySet (lucasNumber (w.length - 2)) (lucasNumber (w.length - 3)) γ
            else beattySet (lucasNumber (w.length - 1)) (lucasNumber (w.length - 2)) γ))) ∧
    ∀ m : ℕ, 1 ≤ m → ∀ N : ℕ, 1 ≤ N →
      (N ∈ basePhiOccurrences (2 * m) (List.replicate (2 * m) 0 ++ [1]) ↔
        (N : ℤ) ∈ beattySet₀ (lucasNumber (2 * m + 1)) (lucasNumber (2 * m)) 1) ∧
      (N ∈ basePhiOccurrences (2 * m + 1) (List.replicate (2 * m + 1) 0 ++ [1]) ↔
        (N : ℤ) ∈ beattySet₀ (lucasNumber (2 * m + 1)) (lucasNumber (2 * m)) 1) ∧
      N ∉ basePhiOccurrences (2 * m + 1) (1 :: List.replicate (2 * m) 0 ++ [1]) ∧
      (N ∈ basePhiOccurrences (2 * m + 2) (1 :: List.replicate (2 * m + 1) 0 ++ [1]) ↔
        (N : ℤ) ∈ beattySet (lucasNumber (2 * m + 2)) (lucasNumber (2 * m + 1))
          (1 - (lucasNumber (2 * m + 1) : ℤ)))

/-- **Every even-length Zeckendorf word ending in $1$ is a negative part.** Let $n \ge 1$ and let
$T$ be a finite set of integers with $T \subseteq [-2n, -1]$ and $-2n \in T$ that contains no
two consecutive integers. Then there are a natural number $N$ and a base phi expansion $S$ of $N$
(the set of positions of its digits $1$) with $\{i \in S : i < 0\} = T$. In words, every
Zeckendorf word of even length $2n \ge 2$ ending in $1$ is the negative part $\beta^-(N)$ of
some $N$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 9 (`integers-2024-A24-thm-9`). -/
public theorem_wanted basePhi_negative_parts_surject (n : ℕ) (hn : 1 ≤ n) (T : Finset ℤ)
    (hT : T ⊆ Finset.Icc (-(2 * n : ℤ)) (-1)) (hlast : -(2 * n : ℤ) ∈ T)
    (hB : IsBergmanExpansion T) :
    ∃ N S, IsBasePhiExpansion N S ∧ S.filter (· < 0) = T

/-- **Recursive structure of the negative parts of base phi expansions.** Let $n \ge 1$, let $L_k$
be the Lucas numbers, and for $j \ge 0$ let $\Lambda_{2j}$ be the set of natural numbers in
$[L_{2j}, L_{2j+1}]$ and $\Lambda_{2j+1}$ the set of natural numbers in
$[L_{2j+1} + 1, L_{2j+2} - 1]$. Let $T$ be a base phi expansion of a natural number $M$ and $S$ a
base phi expansion of a natural number $N$, both given as sets of positions of digits $1$. Write
$S^- = \{i \in S : i < 0\}$ and, for an integer $a$, $T_a = \{i \in T : a \le i < 0\}$. Then:
(A)(a) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n}$, then $S^- = T_{2-2n} \cup \{1-2n, -2n-2\}$;
(A)(b) if $M \in \Lambda_{2n-2}$ and $N = M + L_{2n+1}$, then $S^- = T_{4-2n} \cup \{1-2n, -2n-2\}$;
(A)(c) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n+1}$, then $S^- = T_{2-2n} \cup \{-2n-2\}$;
(B)(a) if $M \in \Lambda_{2n}$ and $N = M + L_{2n+1}$, then $S^- = T_{2-2n} \cup \{-2n-2\}$;
(B)(b) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n+2}$, then $S^- = T_{2-2n} \cup \{-2n, -2n-2\}$;
(B)(c) if $M \in \Lambda_{2n}$ and $N = M + L_{2n+2}$, then $S^- = T_{2-2n} \cup \{-2n, -2n-2\}$.

These are the paper's identities for the words $\gamma^-(N)$, the negative part of the expansion of
$N$ with its final digits $01$ removed; for example (A)(a) is
$\gamma^-(M + L_{2n}) = \gamma^-(M)\,10$. In (B)(c) the source writes $\gamma^-(N - L_{2n+1})$ for
$N \in \Lambda_{2n} + L_{2n+2}$; the shift $L_{2n+2}$ is used here, since as printed $n = 1$ and
$N = 10$ give $\gamma^-(6)\,01 = 0001$ while $\gamma^-(10) = 01$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 10 (`integers-2024-A24-thm-10`). -/
public theorem_wanted basePhi_recursive_structure_gamma (n : ℕ) (hn : 1 ≤ n)
    (M : ℕ) (T S : Finset ℤ) (hT : IsBasePhiExpansion M T) :
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n)) S →
        S.filter (· < 0) = insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
          (T.filter (fun i => (2 - 2 * n : ℤ) ≤ i ∧ i < 0)))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 2)) (lucasNumber (2 * n - 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        S.filter (· < 0) = insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
          (T.filter (fun i => (4 - 2 * n : ℤ) ≤ i ∧ i < 0)))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        S.filter (· < 0) = insert (-2 * n - 2 : ℤ) (T.filter (fun i => (2 - 2 * n : ℤ) ≤ i ∧ i < 0))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        S.filter (· < 0) = insert (-2 * n - 2 : ℤ) (T.filter (fun i => (2 - 2 * n : ℤ) ≤ i ∧ i < 0))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 2)) S →
        S.filter (· < 0) = insert (-(2 * n : ℤ)) (insert (-2 * n - 2 : ℤ)
          (T.filter (fun i => (2 - 2 * n : ℤ) ≤ i ∧ i < 0)))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 2)) S →
        S.filter (· < 0) = insert (-(2 * n : ℤ)) (insert (-2 * n - 2 : ℤ)
          (T.filter (fun i => (2 - 2 * n : ℤ) ≤ i ∧ i < 0))))

/-- **The codes of the negative parts follow an orbit of addition modulo a Fibonacci number.**
Let $n \ge 1$, write $F_k$ for the Fibonacci numbers and $L_k$ for the Lucas numbers, and let
$c$ be a function from the natural numbers to the natural numbers such that
$c(N) = \sum_{i \in S,\, i < 0} F_{i+2n}$ (with $F_k$ read as $0$ for $k < 0$) whenever $S$ is a
base phi expansion of $N$. List the values $c(N)$ for $N = L_{2n-1} + 1, \dots, L_{2n+1}$ (the
interval $\Xi_n$) in increasing order of $N$, and merge every run of equal consecutive values
into a single entry. The resulting list is $(F_{2n} - 1 + j F_{2n-2}) \bmod F_{2n}$ for
$j = 0, 1, \dots, F_{2n} - 1$: the orbit of $F_{2n} - 1$ under addition of $F_{2n-2}$ in
$\mathbb{Z}/F_{2n}\mathbb{Z}$.

Here $c(N)$ is the paper's code $C(N)$ of the negative part $\beta^-(N)$ (the digits of $N$ at
negative positions), and the merged runs are its tridents.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 11 (`integers-2024-A24-thm-11`). -/
public theorem_wanted basePhi_negative_part_order_orbit (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ℕ)
    (hc : ∀ N S, IsBasePhiExpansion N S →
      c N = ∑ i ∈ S.filter (· < 0), Nat.fib (i + 2 * n).toNat) :
    ((List.range' (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n))).map c).destutter
        (· ≠ ·) =
      (List.range (Nat.fib (2 * n))).map
        (fun j => (Nat.fib (2 * n) - 1 + j * Nat.fib (2 * n - 2)) % Nat.fib (2 * n))


/-- **Left end of a Lucas interval.** Let $L_0 = 2$, $L_1 = 1$, $L_{j+2} = L_{j+1} + L_j$ be the
Lucas numbers, and let the Lucas intervals be $\Lambda_{2n} = [L_{2n}, L_{2n+1}]$ and
$\Lambda_{2n+1} = [L_{2n+1} + 1, L_{2n+2} - 1]$. The left end of $\Lambda_m$ is $L_m$ when $m$
is even and $L_m + 1$ when $m$ is odd.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 3 (Lucas intervals). -/
def lucasIntervalLo (m : ℕ) : ℕ := if Even m then lucasNumber m else lucasNumber m + 1

/-- **Right end of a Lucas interval.** Let $L_0 = 2$, $L_1 = 1$, $L_{j+2} = L_{j+1} + L_j$ be the
Lucas numbers, and let the Lucas intervals be $\Lambda_{2n} = [L_{2n}, L_{2n+1}]$ and
$\Lambda_{2n+1} = [L_{2n+1} + 1, L_{2n+2} - 1]$. The right end of $\Lambda_m$ is $L_{m+1}$ when
$m$ is even and $L_{m+1} - 1$ when $m$ is odd.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 3 (Lucas intervals). -/
def lucasIntervalHi (m : ℕ) : ℕ := if Even m then lucasNumber (m + 1) else lucasNumber (m + 1) - 1

/-- **Endpoints of the Lucas interval $\Lambda_3$.** The Lucas interval $\Lambda_3$ has left end
$5$ and right end $6$, that is, $\Lambda_3 = [5, 6]$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 3. -/
theorem lucasInterval_three : lucasIntervalLo 3 = 5 ∧ lucasIntervalHi 3 = 6 := by decide

/-- **Endpoints of the Lucas interval $\Lambda_4$.** The Lucas interval $\Lambda_4$ has left end
$7$ and right end $11$, that is, $\Lambda_4 = [7, 11]$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 3. -/
theorem lucasInterval_four : lucasIntervalLo 4 = 7 ∧ lucasIntervalHi 4 = 11 := by decide

/-- **Endpoints of the Lucas interval $\Lambda_5$.** The Lucas interval $\Lambda_5$ has left end
$12$ and right end $17$, that is, $\Lambda_5 = [12, 17]$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 3. -/
theorem lucasInterval_five : lucasIntervalLo 5 = 12 ∧ lucasIntervalHi 5 = 17 := by decide

/-- **Lucas tilings.** Write $\Lambda_k = [\ell_k, h_k]$ for the Lucas interval with left end
$\ell_k$ and right end $h_k$. For natural numbers $a$, $b$ and a list $P$ of pairs $(k, t)$ of
natural numbers, $P$ is a Lucas tiling of $[a, b]$ when the translated Lucas intervals
$\Lambda_k + t$, $(k, t) \in P$, taken in the order of $P$, are adjacent and their union is
$[a, b]$. Precisely, it is defined by recursion on $P$: the empty list is a Lucas tiling of
$[a, b]$ exactly when $a = b + 1$, and the list consisting of $(k, t)$ followed by $P$ is a Lucas
tiling of $[a, b]$ exactly when $\ell_k + t = a$ and $P$ is a Lucas tiling of $[h_k + t + 1, b]$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4 ("a union of adjacent translations" of Lucas intervals). -/
def IsLucasTiling : ℕ → ℕ → List (ℕ × ℕ) → Prop
  | a, b, [] => a = b + 1
  | a, b, p :: P => lucasIntervalLo p.1 + p.2 = a ∧ IsLucasTiling (lucasIntervalHi p.1 + p.2 + 1) b P

/-- **Lucas tilings by the empty list.** For all natural numbers $a$ and $b$, the empty list is a
Lucas tiling of $[a, b]$ if and only if $a = b + 1$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4. -/
theorem isLucasTiling_nil (a b : ℕ) : IsLucasTiling a b [] ↔ a = b + 1 := Iff.rfl

/-- **Lucas tilings of a list with a first interval.** Write $\Lambda_k = [\ell_k, h_k]$ for the
Lucas interval with left end $\ell_k$ and right end $h_k$. For all natural numbers $a$, $b$, $k$,
$t$ and every list $P$ of pairs of natural numbers, the list consisting of $(k, t)$ followed by
$P$ is a Lucas tiling of $[a, b]$ if and only if $\ell_k + t = a$ and $P$ is a Lucas tiling of
$[h_k + t + 1, b]$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4. -/
theorem isLucasTiling_cons (a b : ℕ) (p : ℕ × ℕ) (P : List (ℕ × ℕ)) :
    IsLucasTiling a b (p :: P) ↔
      lucasIntervalLo p.1 + p.2 = a ∧ IsLucasTiling (lucasIntervalHi p.1 + p.2 + 1) b P :=
  Iff.rfl

/-- **Canonical splitting of a Lucas interval.** Let $L_j$ be the $j$-th Lucas number
($L_0 = 2$, $L_1 = 1$, $L_{j+2} = L_{j+1} + L_j$). For a natural number $m$, the canonical
splitting of the Lucas interval $\Lambda_m$ is the list of pairs $(k, t)$ of natural numbers
defined by recursion on $m$: for $m \le 5$ it is the one-pair list $[(m, 0)]$, and for $m \ge 6$
it is the concatenation, in this order, of the canonical splitting of $\Lambda_{m-2}$ with
$L_{m-1}$ added to the second coordinate of each pair, the canonical splitting of
$\Lambda_{m-3}$ with $L_m$ added to the second coordinate of each pair, and the canonical
splitting of $\Lambda_{m-2}$ with $L_m$ added to the second coordinate of each pair.

Here $\Lambda_{2n} = [L_{2n}, L_{2n+1}]$ and $\Lambda_{2n+1} = [L_{2n+1} + 1, L_{2n+2} - 1]$, and a
pair $(k, t)$ stands for the translate $\Lambda_k + t$. The recursion follows the second
Recursive Structure Theorem
$\Lambda_m = (\Lambda_{m-2} + L_{m-1}) \cup (\Lambda_{m-3} + L_m) \cup (\Lambda_{m-2} + L_m)$
(the paper's splittings of $\Lambda_6, \Lambda_7, \Lambda_8$, "continuing in this fashion").
That for $m \ge 3$ the result splits $\Lambda_m$ into adjacent translates of $\Lambda_3$,
$\Lambda_4$ and $\Lambda_5$ is the paper's Theorem 4. Only $m \ge 3$ is used.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4 (canonical splitting). -/
def canonicalLucasSplitting : ℕ → List (ℕ × ℕ)
  | m + 6 =>
      (canonicalLucasSplitting (m + 4)).map (fun p => (p.1, p.2 + lucasNumber (m + 5))) ++
        (canonicalLucasSplitting (m + 3)).map (fun p => (p.1, p.2 + lucasNumber (m + 6))) ++
        (canonicalLucasSplitting (m + 4)).map (fun p => (p.1, p.2 + lucasNumber (m + 6)))
  | m => [(m, 0)]

/-- **Canonical splitting of a short Lucas interval.** For every natural number $m < 6$, the
canonical splitting of the Lucas interval $\Lambda_m$ is the one-pair list $[(m, 0)]$, that is,
$\Lambda_m$ itself.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4. -/
theorem canonicalLucasSplitting_of_lt_six (m : ℕ) (hm : m < 6) :
    canonicalLucasSplitting m = [(m, 0)] := by
  rcases m with _ | _ | _ | _ | _ | _ | m <;> first | rfl | omega

/-- **Recursion for the canonical splitting.** For every natural number $m$, the canonical
splitting of the Lucas interval $\Lambda_{m+6}$ is the concatenation, in this order, of the
canonical splitting of $\Lambda_{m+4}$ with $L_{m+5}$ added to the second coordinate of each
pair, the canonical splitting of $\Lambda_{m+3}$ with $L_{m+6}$ added to the second coordinate of
each pair, and the canonical splitting of $\Lambda_{m+4}$ with $L_{m+6}$ added to the second
coordinate of each pair, where $L_j$ is the $j$-th Lucas number.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4. -/
theorem canonicalLucasSplitting_add_six (m : ℕ) :
    canonicalLucasSplitting (m + 6) =
      (canonicalLucasSplitting (m + 4)).map (fun p => (p.1, p.2 + lucasNumber (m + 5))) ++
        (canonicalLucasSplitting (m + 3)).map (fun p => (p.1, p.2 + lucasNumber (m + 6))) ++
        (canonicalLucasSplitting (m + 4)).map (fun p => (p.1, p.2 + lucasNumber (m + 6))) := by
  rw [canonicalLucasSplitting]

/-- **Canonical splitting of the sixth Lucas interval.** The canonical splitting of the Lucas
interval $\Lambda_6$ is the list $[(4, 11), (3, 18), (4, 18)]$.

The pairs stand for the translates $\Lambda_4 + L_5$, $\Lambda_3 + L_6$ and $\Lambda_4 + L_6$,
where $L_5 = 11$ and $L_6 = 18$ are Lucas numbers.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4. -/
theorem canonicalLucasSplitting_six :
    canonicalLucasSplitting 6 = [(4, 11), (3, 18), (4, 18)] := by decide

/-- **Dekking's Theorem 4: the coding of the canonical splittings of Lucas intervals.** Write
$\Lambda_m = [\ell_m, h_m]$ for the Lucas interval with left end $\ell_m$ and right end $h_m$. For
every $n \ge 3$, every pair $(k, t)$ in the canonical splitting of $\Lambda_n$ has
$k \in \{3, 4, 5\}$, and the canonical splitting of $\Lambda_n$ is a Lucas tiling of
$[\ell_n, h_n]$. Let $\kappa$ be the map on finite words of natural numbers that replaces each
letter $3$ by the word $5$, each letter $4$ by $434$ and every other letter by $545$, and let
$C(\Lambda_m)$ be the word formed by the first components $k$ of the pairs $(k, t)$ of the
canonical splitting of $\Lambda_m$, in order. Then for every $n \ge 0$,
$C(\Lambda_{2n+4}) = \kappa^n(4)$ and $C(\Lambda_{2n+5}) = \kappa^n(5)$, where $\kappa^n$ is the
$n$-fold iterate of $\kappa$ applied to the one-letter word.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 4 (`integers-2024-A24-thm-4`). -/
public theorem_wanted lucasInterval_canonical_splitting_coding :
    (∀ n : ℕ, 3 ≤ n →
      (∀ p ∈ canonicalLucasSplitting n, p.1 = 3 ∨ p.1 = 4 ∨ p.1 = 5) ∧
        IsLucasTiling (lucasIntervalLo n) (lucasIntervalHi n) (canonicalLucasSplitting n)) ∧
    ∀ n : ℕ,
      (canonicalLucasSplitting (2 * n + 4)).map Prod.fst =
          (List.flatMap (fun x : ℕ => if x = 3 then [5] else if x = 4 then [4, 3, 4]
            else [5, 4, 5]))^[n] [4] ∧
        (canonicalLucasSplitting (2 * n + 5)).map Prod.fst =
          (List.flatMap (fun x : ℕ => if x = 3 then [5] else if x = 4 then [4, 3, 4]
            else [5, 4, 5]))^[n] [5]

/-- **Canonical splitting and coding of unions of two Lucas intervals.** Let $L_m$ denote the
$m$-th Lucas number and $\Lambda_m$ the Lucas interval, so $\Lambda_{2k} = [L_{2k}, L_{2k+1}]$
and $\Lambda_{2k+1} = [L_{2k+1} + 1, L_{2k+2} - 1]$. For $n \ge 2$, let $P_n$ be the canonical
splitting of $\Lambda_{2n-1}$ followed by the canonical splitting of $\Lambda_{2n}$, a list of
translations $\Lambda_k + t$. Then every index $k$ occurring in $P_n$ is $3$, $4$ or $5$, and
the intervals of $P_n$, taken in order, are adjacent with union $[L_{2n-1} + 1, L_{2n+1}]$.
Moreover, for every $n \ge 0$ the list of indices $k$ of $P_{n+2}$ (the coding $C(\Xi_{n+2})$,
where $\Xi_n = \Lambda_{2n-1} \cup \Lambda_{2n}$) equals $\delta(h^n(b))$, where $h$ is the
morphism $a \mapsto aab$, $b \mapsto ab$ on words over $\{a, b\}$ and $\delta$ is the morphism
$a \mapsto 54$, $b \mapsto 34$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 5 (`integers-2024-A24-thm-5`). -/
public theorem_wanted xi_canonical_splitting_coding :
    (∀ n : ℕ, 2 ≤ n →
      (∀ p ∈ canonicalLucasSplitting (2 * n - 1) ++ canonicalLucasSplitting (2 * n),
          p.1 = 3 ∨ p.1 = 4 ∨ p.1 = 5) ∧
        IsLucasTiling (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n + 1))
          (canonicalLucasSplitting (2 * n - 1) ++ canonicalLucasSplitting (2 * n))) ∧
    ∀ n : ℕ,
      (canonicalLucasSplitting (2 * n + 3) ++ canonicalLucasSplitting (2 * n + 4)).map Prod.fst =
        ((List.flatMap (fun c : Char => if c = 'a' then ['a', 'a', 'b'] else ['a', 'b']))^[n]
          ['b']).flatMap (fun c : Char => if c = 'a' then [5, 4] else [3, 4])

/-- **Trident splitting at an even Lucas number.** Let $n \ge 1$ and let $L_{2n}$ be the $2n$-th
Lucas number. If $S_1$, $S_2$ and $S_3$ are base phi expansions of $L_{2n} - 1$, $L_{2n}$ and
$L_{2n} + 1$ respectively, each given as the set of positions of its digits $1$, then the
negative positions $i < 0$ of $S_1$, of $S_2$ and of $S_3$ are the same.

In the paper's terms, the last number $L_{2n} - 1$ of the Lucas interval $\Lambda_{2n-1}$ and the
first two numbers $L_{2n}$, $L_{2n} + 1$ of $\Lambda_{2n}$ form a trident: three consecutive
numbers $N$, $N + 1$, $N + 2$ with $\beta^-(N) = \beta^-(N+1) = \beta^-(N+2)$, where $\beta^-$ is
the negative part of the base phi expansion.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 8 (`integers-2024-A24-lem-8`). -/
public theorem_wanted basePhi_trident_splitting (n : ℕ) (hn : 1 ≤ n) (S₁ S₂ S₃ : Finset ℤ)
    (h₁ : IsBasePhiExpansion (lucasNumber (2 * n) - 1) S₁)
    (h₂ : IsBasePhiExpansion (lucasNumber (2 * n)) S₂)
    (h₃ : IsBasePhiExpansion (lucasNumber (2 * n) + 1) S₃) :
    S₁.filter (· < 0) = S₂.filter (· < 0) ∧ S₂.filter (· < 0) = S₃.filter (· < 0)

/-- **The codes of the negative parts follow the golden rotation.** Let $n \ge 1$, write $\varphi$
for the golden ratio, $F_k$ for the Fibonacci numbers and $L_k$ for the Lucas numbers, and let
$c$ be a function from the natural numbers to the natural numbers such that
$c(N) = \sum_{i \in S,\, i < 0} F_{i+2n}$ (with $F_k$ read as $0$ for $k < 0$) whenever $S$ is a
base phi expansion of $N$. List the values $c(N)$ for $N = L_{2n-1} + 1, \dots, L_{2n+1}$ (the
interval $\Xi_n$) in increasing order of $N$, and merge every run of equal consecutive values
into a single entry. The resulting list is a permutation of $0, 1, \dots, F_{2n} - 1$, and the
fractional parts $\{(k+1)\varphi\}$ of its entries $k$ strictly decrease along it: if $k$ comes
before $k'$, then $\{(k'+1)\varphi\} < \{(k+1)\varphi\}$.

This list is the paper's permutation $\Pi^\beta_{2n}$ (the codes $C(N)$ of the negative parts
$\beta^-(N)$, tridents merged, as in Theorem 11), and the statement says it is the order in
which the first $F_{2n}$ iterates of the rotation $z \mapsto \exp(2\pi i(z - \varphi))$ occur on
the circle, the entry $k$ standing for the iterate number $k + 1$. This is the reading fixed by
the paper's worked case $n = 3$, where $\Pi^\beta_6 = 7\,2\,5\,0\,3\,6\,1\,4$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 12 (`integers-2024-A24-thm-12`). -/
public theorem_wanted basePhi_negative_part_order_rotation (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ℕ)
    (hc : ∀ N S, IsBasePhiExpansion N S →
      c N = ∑ i ∈ S.filter (· < 0), Nat.fib (i + 2 * n).toNat) :
    (((List.range' (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n))).map c).destutter
        (· ≠ ·)).Perm (List.range (Nat.fib (2 * n))) ∧
      (((List.range' (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n))).map c).destutter
        (· ≠ ·)).Pairwise
          (fun i j => Int.fract (((j : ℝ) + 1) * φ) < Int.fract (((i : ℝ) + 1) * φ))

end

end MetaMathlibExt
