/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.ZMod.Defs

/-!
# Ulam words — wishlist

Statements from Paul Adutwum, Hopper Clark, Ro Emerson, Alexandra (Sasha) Sheydvasser,
Arseniy (Senia) Sheydvasser, and Axelle Tougouma, *Distributions of Ulam Words up to Length
30*, INTEGERS 25 (2025), Article A102 (arXiv:2410.01217v2).

Words over `{0, 1}` are `List Bool` with `false = 0`, `true = 1`. Following Bade, Cui,
Labelle, and Li (as quoted in Section 1 of the paper), `0` and `1` are Ulam, and a word
`w ≠ 0, 1` is Ulam iff there is exactly one pair of Ulam words `u₁ ≠ u₂` with `w = u₁ u₂`.
The integer `π(w)` of a word is its binary value, most significant letter first, written
`Nat.ofDigits 2 (w.reverse.map Bool.toNat)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Fuel-bounded Ulam test.** For a natural number $f$ (the fuel) and a word $w$ in the letters
$0$ and $1$, the test returns false when $f = 0$. With fuel $f + 1$ it returns true when $w$ has
length $1$; otherwise it returns true exactly when there is exactly one $k$ with
$1 \le k < |w|$ such that the prefix $w_1 \cdots w_k$ and the suffix $w_{k+1} \cdots w_{|w|}$
are distinct and both pass the test with fuel $f$.

This is the Ulam recursion: with fuel at least $|w|$, the test decides whether $w$ is an Ulam
word.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(definition of Ulam words, after Bade, Cui, Labelle, and Li). -/
public def ulamWordAux : ℕ → List Bool → Bool
  | 0, _ => false
  | f + 1, w =>
    if w.length = 1 then true
    else
      ((List.range (w.length - 1)).countP fun k =>
        w.take (k + 1) != w.drop (k + 1) && ulamWordAux f (w.take (k + 1)) &&
          ulamWordAux f (w.drop (k + 1))) == 1

/-- **Ulam words.** Ulam words are finite words over the alphabet $\{0, 1\}$, defined by
recursion on the length. The empty word is not an Ulam word, and the two words $0$ and $1$ of
length $1$ are Ulam words. A word $w$ of length at least $2$ is an Ulam word if and only if there
is exactly one way to write $w = uv$ with $u$ and $v$ nonempty, distinct Ulam words.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(definition of Ulam words, after Bade, Cui, Labelle, and Li). -/
public def IsUlamWord (w : List Bool) : Prop :=
  ulamWordAux w.length w = true

/-- Ulam-ness is decidable.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1. -/
public instance : DecidablePred IsUlamWord := fun w =>
  inferInstanceAs (Decidable (ulamWordAux w.length w = true))

/-- **Ulam words of length at most three.** The empty word is not an Ulam word, and both words
$0$ and $1$ of length one are Ulam words. The Ulam words of length two are exactly $01$ and $10$,
and the Ulam words of length three are exactly $001$, $011$, $100$ and $110$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(displayed `U₁, …, U₄`). -/
public theorem isUlamWord_small :
    IsUlamWord [false] ∧ IsUlamWord [true] ∧ ¬ IsUlamWord [] ∧
      ¬ IsUlamWord [false, false] ∧ IsUlamWord [false, true] ∧ IsUlamWord [true, false] ∧
      ¬ IsUlamWord [true, true] ∧
      ¬ IsUlamWord [false, false, false] ∧ IsUlamWord [false, false, true] ∧
      ¬ IsUlamWord [false, true, false] ∧ IsUlamWord [false, true, true] ∧
      IsUlamWord [true, false, false] ∧ ¬ IsUlamWord [true, false, true] ∧
      IsUlamWord [true, true, false] ∧ ¬ IsUlamWord [true, true, true] := by
  decide

/-- **Ulam words of length four: examples.** The words $0001$ and $1011$ are Ulam words, while
$0011$ and $0110$ are not.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(displayed `U₄`). -/
public theorem isUlamWord_length_four_examples :
    IsUlamWord [false, false, false, true] ∧ ¬ IsUlamWord [false, false, true, true] ∧
      IsUlamWord [true, false, true, true] ∧ ¬ IsUlamWord [false, true, true, false] := by
  decide

/-- **Number of Ulam words of a given length.** For a natural number $n$, $\#U_n$ denotes the
number of Ulam words of length $n$, that is, of words $w_1 \cdots w_n$ of length $n$ in the
letters $0$ and $1$ that are Ulam words.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1. -/
public def ulamWordCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun v : Fin n → Bool => IsUlamWord (List.ofFn v)).card

/-- **Numbers of short Ulam words.** There are $2$, $2$, $4$ and $8$ Ulam words of length $1$,
$2$, $3$ and $4$ respectively: $\#U_1 = 2$, $\#U_2 = 2$, $\#U_3 = 4$ and $\#U_4 = 8$, where
$\#U_n$ is the number of Ulam words of length $n$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(displayed `U₁, …, U₄`). -/
public theorem ulamWordCount_small :
    ulamWordCount 1 = 2 ∧ ulamWordCount 2 = 2 ∧ ulamWordCount 3 = 4 ∧ ulamWordCount 4 = 8 := by
  decide

/-- **Ulam words in a residue class.** For natural numbers $N$ and $n$ and a residue class
$a \in \mathbb{Z}/N\mathbb{Z}$, this is the number of Ulam words $w$ of length $n$ in the letters
$0$ and $1$ whose binary value $\pi(w)$, read with the most significant letter first, lies in the
class $a$ modulo $N$. For $N = 0$, $\mathbb{Z}/0\mathbb{Z}$ is $\mathbb{Z}$ and the condition is
$\pi(w) = a$.

The paper's relative density $\rho_{a,N}(n)$ is this number divided by the number $\#U_n$ of
Ulam words of length $n$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(Conjecture 3, definition of `ρ_{a,N}(n)`). -/
public def ulamResidueCount (N n : ℕ) (a : ZMod N) : ℕ :=
  (Finset.univ.filter fun v : Fin n → Bool =>
    IsUlamWord (List.ofFn v) ∧
      ((Nat.ofDigits 2 ((List.ofFn v).reverse.map Bool.toNat) : ℕ) : ZMod N) = a).card

/-- **Residues of the Ulam words of length 2 modulo 3.** Read the Ulam words of length $2$ as
binary numerals, most significant letter first. None of their values is congruent to $0$ modulo
$3$, exactly one is congruent to $1$, and exactly one is congruent to $2$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 6. -/
public theorem ulamResidueCount_three_two :
    ulamResidueCount 3 2 0 = 0 ∧ ulamResidueCount 3 2 1 = 1 ∧ ulamResidueCount 3 2 2 = 1 := by
  decide

/-- **Sorted binary values of Ulam words.** For a natural number $n$, this is the list
$u_1 < u_2 < \dots < u_k$ of the distinct binary values $\pi(w)$, read with the most significant
letter first, of the Ulam words $w$ of length $n$, in increasing order.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(Conjecture 2, ordered elements of `π(U_n)`). -/
public def ulamValuesSorted (n : ℕ) : List ℕ :=
  ((Finset.univ.filter fun v : Fin n → Bool => IsUlamWord (List.ofFn v)).image
    fun v => Nat.ofDigits 2 ((List.ofFn v).reverse.map Bool.toNat)).sort (· ≤ ·)

/-- **Binary values of the Ulam words of length 3.** The increasing list of the distinct binary
values $\pi(w)$, read with the most significant letter first, of the Ulam words $w$ of length $3$
has exactly the entries $1, 3, 4, 6$.

These values come from the Ulam words $001$, $011$, $100$, $110$ of length $3$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1. -/
public theorem ulamValuesSorted_three :
    (ulamValuesSorted 3).toFinset = {1, 3, 4, 6} := by
  rw [ulamValuesSorted, Finset.sort_toFinset]
  decide

/-- **Mean gap of the Ulam values.** For $n \in \mathbb{N}$, read each Ulam word of length $n$
as a binary numeral, most significant letter first, and list the resulting values in increasing
order as $u_1 < u_2 < \dots < u_k$. The mean gap of these values is the rational number
$$\mu_g(n) = \frac{1}{k - 1} \sum_{i=1}^{k-1} (u_{i+1} - u_i),$$
where a quotient by $0$ is read as $0$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(Conjecture 2, `μ_g(n)` as the mean of the gap distribution `p_n`). -/
public def ulamGapMean (n : ℕ) : ℚ :=
  (((List.zipWith (fun a b : ℕ => b - a) (ulamValuesSorted n)
      (ulamValuesSorted n).tail).sum : ℕ) : ℚ) /
    (((ulamValuesSorted n).length : ℚ) - 1)

/-- **Stages of the discrete Sierpiński triangle.** The stages
$S_n \subseteq \mathbb{N} \times \mathbb{N}$ of the discrete Sierpiński triangle are defined by
$S_0 = \{(2, 1)\}$ and $S_{n+1} = S_n \cup (S_n + (2^n, 0)) \cup (S_n + (2^n, 2^n))$, where
$S + (u, v) = \{(x + u, y + v) : (x, y) \in S\}$ denotes a translate.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 4
(recursive definition of `S_n`). -/
public def discreteSierpinskiStage : ℕ → Set (ℕ × ℕ)
  | 0 => {(2, 1)}
  | n + 1 =>
    discreteSierpinskiStage n ∪ (fun p => (p.1 + 2 ^ n, p.2)) '' discreteSierpinskiStage n ∪
      (fun p => (p.1 + 2 ^ n, p.2 + 2 ^ n)) '' discreteSierpinskiStage n

/-- **The discrete Sierpiński triangle.** The discrete Sierpiński triangle is the set
$\mathcal{S} = \bigcup_{n \ge 0} S_n \subseteq \mathbb{N} \times \mathbb{N}$, the union of all the
stages $S_n$ of the discrete Sierpiński triangle.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 4. -/
public def discreteSierpinski : Set (ℕ × ℕ) :=
  ⋃ n, discreteSierpinskiStage n

/-- **The first stage of the discrete Sierpiński triangle.** The stage $S_1$ of the discrete
Sierpiński triangle is $\{(2, 1), (3, 1), (3, 2)\}$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 4. -/
public theorem discreteSierpinskiStage_one :
    discreteSierpinskiStage 1 = {(2, 1), (3, 1), (3, 2)} := by
  ext p
  simp only [discreteSierpinskiStage, Set.image_singleton, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  norm_num
  tauto

/-- **Ulam words with a block of four ones.** For natural numbers $a$ and $b$ with $a + b \ge 1$,
the binary word $0^a 1111 0^b$ ($a$ zeros, then four ones, then $b$ zeros) is an Ulam word if
and only if $a + b \equiv 1 \pmod 4$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Lemma 1. -/
public theorem_wanted isUlamWord_zeros_four_ones_zeros_iff (a b : ℕ) (hab : 1 ≤ a + b) :
    IsUlamWord (List.replicate a false ++ List.replicate 4 true ++ List.replicate b false) ↔
      (a + b) % 4 = 1

/-- **Square of the Ulam word count is at most a block sum.** For every natural number $n$,
$(\#U_n)^2 \le \sum_{i=n}^{2n} \#U_i$, where $\#U_i$ is the number of Ulam words of length $i$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Lemma 2. -/
public theorem_wanted ulamWordCount_sq_le_sum (n : ℕ) :
    ulamWordCount n ^ 2 ≤ ∑ i ∈ Finset.Icc n (2 * n), ulamWordCount i

/-- **Ulam words with three leading ones.** For every $n \ge 3$, the word $1^3 0^{n-3}$ (three
ones followed by $n - 3$ zeros) is an Ulam word if and only if $n \equiv 0 \pmod 4$ or
$n \equiv 1 \pmod 4$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Lemma 3. -/
public theorem_wanted isUlamWord_three_ones_zeros_iff (n : ℕ) (hn : 3 ≤ n) :
    IsUlamWord (List.replicate 3 true ++ List.replicate (n - 3) false) ↔
      n % 4 = 0 ∨ n % 4 = 1

/-- **Linear lower bound on the number of Ulam words.** For every natural number $n \ge 6$, the
number of Ulam words of length $n$ is at least $2n + 4$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 1. -/
public theorem_wanted two_mul_add_four_le_ulamWordCount (n : ℕ) (hn : 6 ≤ n) :
    2 * n + 4 ≤ ulamWordCount n

/-- **Exponential lower bound for Ulam word counts along a subsequence.** Let $\#U_n$ be the
number of Ulam words of length $n$ and $\alpha_0 = (\#U_{30} / (2 \cdot 31))^{1/30}$. For every
real $\alpha$ with $1 < \alpha < \alpha_0$, every real $C$ and every natural number $N$, there
is some $n \ge N$ with $C \alpha^n \le \#U_n$; that is,
$\limsup_{n \to \infty} \#U_n / \alpha^n = \infty$.

Here $\alpha_0$ is the constant from the paper's proof, with $n_1 = 30$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 2. -/
public theorem_wanted ulamWordCount_limsup_div_pow_eq_top (α : ℝ) (hα : 1 < α)
    (hα₀ : α < ((ulamWordCount 30 : ℝ) / (2 * 31)) ^ ((1 : ℝ) / 30)) (C : ℝ) (N : ℕ) :
    ∃ n ≥ N, C * α ^ n ≤ ulamWordCount n

/-- **The inverse Ulam density has the order of the mean gap.** For $n \in \mathbb{N}$ let $U_n$
be the set of Ulam words of length $n$, and let $\mu_g(n)$ be the mean gap of the binary values
of the words in $U_n$. Then $2^n / |U_n|$ (the reciprocal of the density $|U_n| / 2^n$) and
$\mu_g(n)$ have the same order of growth as $n \to \infty$: there are constants $c, C > 0$ such
that $c \, \mu_g(n) \le 2^n / |U_n| \le C \, \mu_g(n)$ for all sufficiently large $n$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 4 (first sentence). -/
public theorem_wanted ulamDensity_inv_isTheta_ulamGapMean :
    (fun n : ℕ => (2 : ℝ) ^ n / ulamWordCount n) =Θ[Filter.atTop]
      fun n => (ulamGapMean n : ℝ)

/-- **Counting Ulam words with a single one.** For every $n \ge 1$, the number of
$a \in \{0, \dots, n - 1\}$ for which the word $0^a 1 0^{n-1-a}$ ($a$ zeros, then a one, then
$n - 1 - a$ zeros) is an Ulam word equals $2^{s_2(n-1)}$, where $s_2(m)$ is the sum of the binary
digits of $m$. This number is the term $G(n - 1)$ of Gould's sequence.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 5
(Corollary 3.4 of Bade, Cui, Labelle, and Li). -/
public theorem_wanted card_ulam_zeros_one_zeros (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.range n).filter fun a =>
        IsUlamWord (List.replicate a false ++ [true] ++ List.replicate (n - 1 - a) false)).card =
      2 ^ (Nat.digits 2 (n - 1)).sum

/-- **Ulam words with a block of two ones.** For natural numbers $a$ and $b$, the binary word
$0^a 11 0^b$ ($a$ zeros, then two ones, then $b$ zeros) is an Ulam word if and only if $a + b$ is
odd.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 6
(Theorem 3.5 of Bade, Cui, Labelle, and Li). -/
public theorem_wanted isUlamWord_zeros_two_ones_zeros_iff (a b : ℕ) :
    IsUlamWord (List.replicate a false ++ List.replicate 2 true ++ List.replicate b false) ↔
      (a + b) % 2 = 1

/-- **Ulam words with one 101 block.** For natural numbers $a$ and $b$ with $a + b \ge 2$, the
binary word $0^a 101 0^b$ ($a$ zeros, then the letters $1, 0, 1$, then $b$ zeros) is an Ulam word
if and only if $a + b$ is odd.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 7
(Theorem 3.6 of Bade, Cui, Labelle, and Li). -/
public theorem_wanted isUlamWord_zeros_one_zero_one_zeros_iff (a b : ℕ) (hab : 2 ≤ a + b) :
    IsUlamWord (List.replicate a false ++ [true, false, true] ++ List.replicate b false) ↔
      (a + b) % 2 = 1

/-- **Parity criterion for Ulam words with a single one.** For natural numbers $a$ and $b$, the
binary word $0^a 1 0^b$ ($a$ zeros, then a one, then $b$ zeros) is an Ulam word if and only if
the binomial coefficient $\binom{a + b}{a}$ is odd.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 8
(Theorem 3.4 of Bade, Cui, Labelle, and Li). -/
public theorem_wanted isUlamWord_zeros_one_zeros_iff (a b : ℕ) :
    IsUlamWord (List.replicate a false ++ [true] ++ List.replicate b false) ↔
      Odd ((a + b).choose a)

/-- **Ulam words made of ones followed by zeros.** For natural numbers $x$ and $y$ with
$1 \le y \le x$, the word $1^y 0^{x-y}$ ($y$ ones followed by $x - y$ zeros) is an Ulam word if
and only if $(x, y) = (1, 1)$ or $(x, y)$ belongs to the discrete Sierpiński triangle
$\mathcal{S}$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 9
(precise form of Theorem 3). -/
public theorem_wanted isUlamWord_ones_zeros_iff_mem_discreteSierpinski (x y : ℕ) (hy : 1 ≤ y)
    (hyx : y ≤ x) :
    IsUlamWord (List.replicate y true ++ List.replicate (x - y) false) ↔
      (x, y) = (1, 1) ∨ (x, y) ∈ discreteSierpinski

/-- **Padding the word 10101 with zeros.** For natural numbers $a$ and $b$ with $a + b \ge 1$, the
word $0^a 10101 0^b$ ($a$ zeros, then $10101$, then $b$ zeros) is an Ulam word if and only if $a$
and $b$ are both even and at least one of $a$ and $b$ is zero.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 10. -/
public theorem_wanted isUlamWord_zeros_10101_zeros_iff (a b : ℕ) (hab : 1 ≤ a + b) :
    IsUlamWord (List.replicate a false ++ [true, false, true, false, true] ++
        List.replicate b false) ↔
      Even a ∧ Even b ∧ (a = 0 ∨ b = 0)

/-- **Complement symmetry of Ulam words.** For a word $w$ over $\{0, 1\}$, let $\bar w$ be its
complement (every letter swapped) and let $\pi(w)$ be the integer whose binary expansion is $w$,
most significant letter first. If $w$ is an Ulam word of length $n$, then $\bar w$ is an Ulam
word and $\pi(\bar w) + \pi(w) = 2^n - 1$. Moreover, for all natural numbers $N$ and $n$ and every
$a \in \mathbb{Z}/N\mathbb{Z}$, the number of Ulam words $w$ of length $n$ with
$\pi(w) \equiv a \pmod N$ equals the number of Ulam words $w$ of length $n$ with
$\pi(w) \equiv 2^n - 1 - a \pmod N$.

For $n \ge 1$, writing $\rho_{a,N}(n)$ for the proportion of Ulam words $w$ of length $n$ with
$\pi(w) \equiv a \pmod N$ among all Ulam words of length $n$, the second statement says
$\rho_{a,N}(n) = \rho_{2^n-1-a,N}(n)$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 11. -/
public theorem_wanted isUlamWord_map_not_and_ulamResidueCount_eq :
    (∀ w : List Bool, IsUlamWord w →
      IsUlamWord (w.map not) ∧
        Nat.ofDigits 2 ((w.map not).reverse.map Bool.toNat) +
            Nat.ofDigits 2 (w.reverse.map Bool.toNat) = 2 ^ w.length - 1) ∧
      ∀ (N n : ℕ) (a : ZMod N),
        ulamResidueCount N n a = ulamResidueCount N n (2 ^ n - 1 - a)

/-- **Residue symmetries of Ulam words modulo 2 and 3.** For natural numbers $N$ and $n$ and a
residue $a \in \mathbb{Z}/N\mathbb{Z}$, let $c_{a,N}(n)$ be the number of Ulam words of length
$n$ whose value as a binary numeral, most significant letter first, is congruent to $a$ modulo
$N$. Then for every $n \ge 1$ we have $c_{0,2}(n) = c_{1,2}(n)$, and for every
$a \in \mathbb{Z}/3\mathbb{Z}$ we have $c_{a,3}(n) = c_{-a,3}(n)$ if $n$ is even and
$c_{a,3}(n) = c_{1-a,3}(n)$ if $n$ is odd.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102,
Corollary 2. -/
public theorem_wanted ulamResidueCount_mod_two_three (n : ℕ) (hn : 1 ≤ n) :
    ulamResidueCount 2 n 0 = ulamResidueCount 2 n 1 ∧
      ∀ a : ZMod 3, ulamResidueCount 3 n a =
        if Even n then ulamResidueCount 3 n (-a) else ulamResidueCount 3 n (1 - a)

end

end MetaMathlibExt
