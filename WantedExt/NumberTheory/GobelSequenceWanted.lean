/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

namespace MetaMathlibExt

open Filter Topology Asymptotics

@[expose] public section

/-- **The (k, l)-Göbel sequence.** For natural numbers $k$ and $l$, the $(k, l)$-Göbel sequence
is the sequence of rational numbers $g_{k,l}(n)$, $n \ge 0$, given by $g_{k,l}(0) = 0$,
$g_{k,l}(1) = l$ and, for $n \ge 1$,
$$g_{k,l}(n + 1) = \frac{g_{k,l}(n) \bigl(n + g_{k,l}(n)^{k-1}\bigr)}{n + 1},$$
where $k - 1$ is truncated subtraction, so the exponent is $0$ when $k = 0$.

The paper indexes from $n = 1$ and takes $k, l \ge 2$ (Lemma 5 also admits $k, l \ge 1$); the
value at $n = 0$ is a convention and plays no role.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Definition 1. -/
public def gobelSequence (k l : ℕ) : ℕ → ℚ
  | 0 => 0
  | 1 => l
  | n + 2 => gobelSequence k l (n + 1) * ((n + 1 : ℚ) + gobelSequence k l (n + 1) ^ (k - 1))
      / (n + 2)

/-- **Initial value of the $(k, l)$-Göbel sequence.** For all natural numbers $k$ and $l$, the
$(k, l)$-Göbel sequence $g_{k,l}$ satisfies $g_{k,l}(1) = l$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Definition 1. -/
public theorem gobelSequence_one (k l : ℕ) : gobelSequence k l 1 = l := rfl

/-- **Recursion for the (k, l)-Göbel sequence.** For all natural numbers $k$, $l$ and $n \ge 1$,
the $(k, l)$-Göbel sequence $g_{k,l}$ satisfies, in $\mathbb{Q}$,
$$(n + 1)\, g_{k,l}(n + 1) = g_{k,l}(n) \bigl(n + g_{k,l}(n)^{k-1}\bigr),$$
where $k - 1$ is truncated subtraction, so the exponent is $0$ when $k = 0$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Definition 1. -/
public theorem gobelSequence_succ (k l n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℚ) * gobelSequence k l (n + 1)
      = gobelSequence k l n * ((n : ℚ) + gobelSequence k l n ^ (k - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show (↑(m + 1) + 1 : ℚ) * (gobelSequence k l (m + 1) *
      ((m + 1 : ℚ) + gobelSequence k l (m + 1) ^ (k - 1)) / (m + 2)) = _
  have h : (m + 2 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Göbel's original sequence.** The $(2, 2)$-Göbel sequence $g_{2,2}$ satisfies
$g_{2,2}(2) = 3$, $g_{2,2}(3) = 5$, $g_{2,2}(4) = 10$ and $g_{2,2}(5) = 28$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Section 1. -/
public theorem gobelSequence_two_two_small :
    gobelSequence 2 2 2 = 3 ∧ gobelSequence 2 2 3 = 5 ∧ gobelSequence 2 2 4 = 10 ∧
      gobelSequence 2 2 5 = 28 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [gobelSequence]

/-- **Integrality of the early terms of $(k, l)$-Göbel sequences.** Let $g_{k,l}$ denote the
$(k, l)$-Göbel sequence. For all natural numbers $k, l \ge 2$ and $1 \le n \le 6$, the value
$g_{k,l}(n)$ is an integer. Moreover, for all natural numbers $k, l \ge 2$, the value $g_{k,l}(7)$
is not an integer if and only if $k \equiv 2 \pmod 6$ and $l \equiv 3 \pmod 7$.

Equivalently, if $N_{k,l}$ is the first index at which $g_{k,l}$ is not an integer, then
$\min_{k,l \ge 2} N_{k,l} = 7$, and $N_{k,l} = 7$ if and only if $k \equiv 2 \pmod 6$ and
$l \equiv 3 \pmod 7$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 2 (`jis-2024-24.8.1-thm-2`). -/
public theorem_wanted gobelSequence_integral_le_six_and_seven_iff :
    (∀ k l : ℕ, 2 ≤ k → 2 ≤ l → ∀ n : ℕ, 1 ≤ n → n ≤ 6 →
        ∃ z : ℤ, gobelSequence k l n = z) ∧
      ∀ k l : ℕ, 2 ≤ k → 2 ≤ l →
        ((¬ ∃ z : ℤ, gobelSequence k l 7 = z) ↔ k % 6 = 2 ∧ l % 7 = 3)

/-- **Asymptotic expansion of the $(k, l)$-Göbel sequence.** Let $k, l \ge 2$ be natural numbers
and let $g_{k,l}$ be the $(k, l)$-Göbel sequence. There are a real number $C > 1$ and real numbers
$a_1, a_2, \dots$ such that for every natural number $R$, as $n \to \infty$,

$$g_{k,l}(n) - C^{k^n} n^{1/(k-1)} \Bigl(1 + \sum_{r=1}^{R} \frac{a_r}{n^r}\Bigr) =
O\Bigl(\frac{C^{k^n} n^{1/(k-1)}}{n^{R+1}}\Bigr).$$

In other words, $g_{k,l}(n) \sim C^{k^n} n^{1/(k-1)} \bigl(1 + \sum_{r \ge 1} a_r / n^r\bigr)$ as
an asymptotic expansion, generalizing Zagier's asymptotic for Göbel's sequence.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 4 (`jis-2024-24.8.1-thm-4`). -/
public theorem_wanted gobelSequence_asymptotic_expansion (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) :
    ∃ C : ℝ, 1 < C ∧ ∃ a : ℕ → ℝ, ∀ R : ℕ,
      (fun n : ℕ => (gobelSequence k l n : ℝ)
          - C ^ (k ^ n) * (n : ℝ) ^ ((1 : ℝ) / (k - 1))
            * (1 + ∑ r ∈ Finset.Icc 1 R, a r / (n : ℝ) ^ r))
        =O[atTop]
      (fun n : ℕ => C ^ (k ^ n) * (n : ℝ) ^ ((1 : ℝ) / (k - 1)) / (n : ℝ) ^ (R + 1))

/-- **Key $p$-adic properties of the $(k, l)$-Göbel sequences.** Let $p$ be a prime, let $N \ge 1$
be a natural number, let $r = \nu_p(N!)$, where $\nu_p$ is the $p$-adic valuation on $\mathbb{Q}$
(with $\nu_p(0) = 0$), and write $g_{k,l}$ for the $(k, l)$-Göbel sequence. Write
$\mathbb{Z}_{(p)}$ for the set of rational numbers $x$ with $\nu_p(x) \ge 0$, and for an integer
$s$ write $x \in p^s \mathbb{Z}_{(p)}$ when $x = 0$ or $\nu_p(x) \ge s$. Then:
(1) for all natural numbers $k, l \ge 1$, if $p > N$ then $g_{k,l}(N) \in \mathbb{Z}_{(p)}$;
(2) for all natural numbers $k, l \ge 1$ and $1 \le n \le N$, if
$g_{k,l}(n) \notin \mathbb{Z}_{(p)}$ then $g_{k,l}(n + 1) \notin \mathbb{Z}_{(p)}$;
(3) if $p \le N$, then for all natural numbers $k_1, k_2 \ge r$ with
$k_1 \equiv k_2 \pmod{\varphi(p^r)}$, where $\varphi$ is Euler's totient function, all $l \ge 1$
and all $1 \le n \le N$: $g_{k_1,l}(n) \in \mathbb{Z}_{(p)}$ if and only if
$g_{k_2,l}(n) \in \mathbb{Z}_{(p)}$, and in that case
$g_{k_1,l}(n) - g_{k_2,l}(n) \in p^{r - \nu_p(n!)} \mathbb{Z}_{(p)}$;
(4) if $p \le N$, then for all natural numbers $k, l_1, l_2 \ge 1$ with
$l_1 \equiv l_2 \pmod{p^r}$ and all $1 \le n \le N$: $g_{k,l_1}(n) \in \mathbb{Z}_{(p)}$ if and
only if $g_{k,l_2}(n) \in \mathbb{Z}_{(p)}$, and in that case
$g_{k,l_1}(n) - g_{k,l_2}(n) \in p^{r - \nu_p(n!)} \mathbb{Z}_{(p)}$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 5 (`jis-2024-24.8.1-lem-5`). -/
public theorem_wanted gobelSequence_padic_key_properties (p : ℕ) (hp : p.Prime)
    (N : ℕ) (hN : 1 ≤ N) :
    (∀ k l : ℕ, 1 ≤ k → 1 ≤ l → N < p → 0 ≤ padicValRat p (gobelSequence k l N)) ∧
    (∀ k l n : ℕ, 1 ≤ k → 1 ≤ l → 1 ≤ n → n ≤ N →
        padicValRat p (gobelSequence k l n) < 0 →
          padicValRat p (gobelSequence k l (n + 1)) < 0) ∧
    (∀ k₁ k₂ l n : ℕ, p ≤ N → 1 ≤ l → 1 ≤ n → n ≤ N →
        padicValNat p N.factorial ≤ k₁ → padicValNat p N.factorial ≤ k₂ →
        k₁ ≡ k₂ [MOD (p ^ padicValNat p N.factorial).totient] →
        ((0 ≤ padicValRat p (gobelSequence k₁ l n) ↔
            0 ≤ padicValRat p (gobelSequence k₂ l n)) ∧
          (0 ≤ padicValRat p (gobelSequence k₁ l n) →
            gobelSequence k₁ l n - gobelSequence k₂ l n = 0 ∨
              ((padicValNat p N.factorial : ℤ) - padicValNat p n.factorial
                ≤ padicValRat p (gobelSequence k₁ l n - gobelSequence k₂ l n))))) ∧
    (∀ k l₁ l₂ n : ℕ, p ≤ N → 1 ≤ k → 1 ≤ l₁ → 1 ≤ l₂ → 1 ≤ n → n ≤ N →
        l₁ ≡ l₂ [MOD p ^ padicValNat p N.factorial] →
        ((0 ≤ padicValRat p (gobelSequence k l₁ n) ↔
            0 ≤ padicValRat p (gobelSequence k l₂ n)) ∧
          (0 ≤ padicValRat p (gobelSequence k l₁ n) →
            gobelSequence k l₁ n - gobelSequence k l₂ n = 0 ∨
              ((padicValNat p N.factorial : ℤ) - padicValNat p n.factorial
                ≤ padicValRat p (gobelSequence k l₁ n - gobelSequence k l₂ n)))))

/-- **Integrality of Göbel sequences up to index 7 via finite $p$-adic checks.** Let $g_{k,l}$ be
the $(k, l)$-Göbel sequence. For a prime $p$, call a rational number $x$ $p$-integral if
$x \in \mathbb{Z}_{(p)}$, that is, if $x = 0$ or its $p$-adic valuation $\nu_p(x)$ is
nonnegative. The following two statements are equivalent.

(i) For all natural numbers $k, l \ge 2$, the value $g_{k,l}(n)$ is an integer for every
$1 \le n \le 6$, and $g_{k,l}(7)$ is not an integer if and only if $k \equiv 2 \pmod 6$ and
$l \equiv 3 \pmod 7$.

(ii) $g_{k,l}(7)$ is $2$-integral for all $2 \le k \le 11$ and $1 \le l \le 16$; it is
$3$-integral for all $2 \le k \le 7$ and $1 \le l \le 9$; it is $5$-integral for all
$1 \le k \le 4$ and $1 \le l \le 5$; and for all $1 \le k \le 6$ and $1 \le l \le 7$, it is not
$7$-integral if and only if $(k, l) = (2, 3)$.

Statement (i) is Theorem 2 of the source.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 6 (`jis-2024-24.8.1-lem-6`). -/
public theorem_wanted gobelSequence_seven_iff_padic_claims :
    ((∀ k l : ℕ, 2 ≤ k → 2 ≤ l → ∀ n : ℕ, 1 ≤ n → n ≤ 6 →
        ∃ z : ℤ, gobelSequence k l n = z) ∧
      ∀ k l : ℕ, 2 ≤ k → 2 ≤ l →
        ((¬ ∃ z : ℤ, gobelSequence k l 7 = z) ↔ k % 6 = 2 ∧ l % 7 = 3)) ↔
    ((∀ k ∈ Finset.Icc 2 11, ∀ l ∈ Finset.Icc 1 16,
        0 ≤ padicValRat 2 (gobelSequence k l 7)) ∧
      (∀ k ∈ Finset.Icc 2 7, ∀ l ∈ Finset.Icc 1 9,
        0 ≤ padicValRat 3 (gobelSequence k l 7)) ∧
      (∀ k ∈ Finset.Icc 1 4, ∀ l ∈ Finset.Icc 1 5,
        0 ≤ padicValRat 5 (gobelSequence k l 7)) ∧
      (∀ k ∈ Finset.Icc 1 6, ∀ l ∈ Finset.Icc 1 7,
        (padicValRat 7 (gobelSequence k l 7) < 0 ↔ k = 2 ∧ l = 3)))

/-- **Strict decrease of the normalized Göbel roots.** Let $k, l \ge 2$ be natural numbers, let
$g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $C_{k,l}(n) = g_{k,l}(n)^{1/k^n}$, a real
number. Then $C_{k,l}(n) > C_{k,l}(n + 1) > 1$ for every natural number $n \ge 1$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 7 (`jis-2024-24.8.1-lem-7`). -/
public theorem_wanted gobelSequence_root_strictAnti (k l n : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hn : 1 ≤ n) :
    (gobelSequence k l (n + 1) : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ (n + 1))
        < (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n) ∧
      1 < (gobelSequence k l (n + 1) : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ (n + 1))

/-- **Root asymptotics of Somos-type sequences.** Let $k \ge 2$ be a natural number, let
$\sigma_k = \exp\bigl(\sum_{m \ge 1} \log m / k^m\bigr)$ be the $k$-Somos constant, and let
$t : \mathbb{N} \to \mathbb{R}$ satisfy $t(n + 1) = t(n)^k / (n + 1)$ for all $n \ge 0$. If
$t(0) > \sigma_k$, then the sequence $n \mapsto t(n)^{1/k^n}$ is nonincreasing and converges to
some real number $c > 1$.

The sequence is constant from $n = 0$ to $n = 1$, so the paper's "decreases monotonically" is
read in the non-strict sense.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 8 (`jis-2024-24.8.1-lem-8`). -/
public theorem_wanted somosLike_root_antitone_tendsto (k : ℕ) (hk : 2 ≤ k) (t : ℕ → ℝ)
    (ht : ∀ n : ℕ, t (n + 1) = t n ^ k / (n + 1))
    (h0 : Real.exp (∑' m : ℕ, Real.log m / (k : ℝ) ^ m) < t 0) :
    ∃ c : ℝ, 1 < c ∧ Antitone (fun n : ℕ => t n ^ ((1 : ℝ) / (k : ℝ) ^ n)) ∧
      Tendsto (fun n : ℕ => t n ^ ((1 : ℝ) / (k : ℝ) ^ n)) atTop (𝓝 c)

/-- **Somos-type sequences lie below Göbel sequences.** Let $k, l \ge 2$ be natural numbers, let
$g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $t : \mathbb{N} \to \mathbb{R}$ satisfy
$t(n + 1) = t(n)^k / (n + 1)$ for all $n \ge 0$. If $t(0)^k \le l$, then $t(n) \le g_{k,l}(n)$
for every $n \ge 1$.

The paper also assumes $t(0) > 1$; the statement holds without it (for even $k$, $t(n) \ge 0$
for $n \ge 1$; for odd $k$, $x \mapsto x^k$ is monotone), so that hypothesis is dropped.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 9 (`jis-2024-24.8.1-lem-9`). -/
public theorem_wanted somosLike_le_gobelSequence (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (t : ℕ → ℝ) (ht : ∀ n : ℕ, t (n + 1) = t n ^ k / (n + 1)) (h0 : t 0 ^ k ≤ l)
    (n : ℕ) (hn : 1 ≤ n) :
    t n ≤ gobelSequence k l n

/-- **The normalized Göbel roots converge to a limit greater than 1.** Let $k, l \ge 2$ be natural
numbers and let $g_{k,l}$ be the $(k, l)$-Göbel sequence. There is a real number $C > 1$ such
that the real numbers $g_{k,l}(n)^{1/k^n}$ tend to $C$ as $n \to \infty$.

The paper defines $C_{k,l}$ as this limit.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Proposition 10 (`jis-2024-24.8.1-prop-10`). -/
public theorem_wanted gobelSequence_root_tendsto_gt_one (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) :
    ∃ C : ℝ, 1 < C ∧
      Tendsto (fun n : ℕ => (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n)) atTop (𝓝 C)

/-- **The Göbel error term decays faster than every power of $n$.** Let $k, l \ge 2$ be natural
numbers, let $g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $C$ be a real number such that the
real numbers $C_{k,l}(n) = g_{k,l}(n)^{1/k^n}$ tend to $C$ as $n \to \infty$. Then for every real
number $R > 0$, as $n \to \infty$,

$$\exp\Bigl(\sum_{m=1}^{\infty} \frac{\log(m + n)}{k^m}\Bigr) -
\Bigl(\frac{C_{k,l}(n)}{C}\Bigr)^{k^n} = O(n^{-R}).$$

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 11 (`jis-2024-24.8.1-thm-11`). -/
public theorem_wanted gobelSequence_error_isBigO (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (C : ℝ)
    (hC : Tendsto (fun n : ℕ => (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n))
      atTop (𝓝 C))
    (R : ℝ) (hR : 0 < R) :
    (fun n : ℕ => Real.exp (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1))
        - ((gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n) / C) ^ (k ^ n))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-R))

/-- **Series formula and bound for the Göbel error.** Let $k, l \ge 2$ be natural numbers, let
$g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $C$ be a real number such that the real numbers
$C_{k,l}(n) = g_{k,l}(n)^{1/k^n}$ tend to $C$ as $n \to \infty$. Then for every natural number
$n \ge 1$ the error

$$\varepsilon_{k,l}(n) = \sum_{m=1}^{\infty} \frac{\log(m + n)}{k^m} -
k^n \bigl(\log C_{k,l}(n) - \log C\bigr)$$

satisfies

$$\varepsilon_{k,l}(n) = \sum_{m=1}^{\infty} \frac{1}{k^m}
\log\Bigl(1 + \frac{m + n - 1}{g_{k,l}(m + n - 1)^{k-1}}\Bigr) \le \frac{2n}{C^{(k-1) k^n}}.$$

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 12 (`jis-2024-24.8.1-lem-12`). -/
public theorem_wanted gobelSequence_error_eq_tsum_le (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (C : ℝ)
    (hC : Tendsto (fun n : ℕ => (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n))
      atTop (𝓝 C))
    (n : ℕ) (hn : 1 ≤ n) :
    (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1))
        - (k : ℝ) ^ n * (Real.log ((gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n))
          - Real.log C)
      = ∑' m : ℕ, Real.log (1 + ((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1))
          / (k : ℝ) ^ (m + 1) ∧
    ∑' m : ℕ, Real.log (1 + ((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1))
          / (k : ℝ) ^ (m + 1)
      ≤ 2 * n / C ^ ((k - 1) * k ^ n)

/-- **Sondow–Hadjicostas asymptotic expansion.** Let $k \ge 2$ be a natural number. For $j \ge 1$
put $S_j = \sum_{i \ge 1} i^j / k^i$ and $b_j = (-1)^{j-1} S_j / j$, and for $r \ge 0$ let
$$a_r = \sum_{m_1 + 2 m_2 + \dots + r m_r = r} \ \prod_{j=1}^{r} \frac{b_j^{m_j}}{m_j!},$$
where the sum runs over the tuples $(m_1, \dots, m_r)$ of natural numbers satisfying the
constraint. For $n \in \mathbb{N}$ let $E(n) = \exp\bigl(\sum_{s \ge 1} \log(s + n) / k^s\bigr)$
and, for a natural number $R$, let $P_R(n) = 1 + \sum_{r=1}^{R} a_r / n^r$. Then for every
natural number $R$,
$$E(n) - n^{1/(k-1)} P_R(n) = O\bigl(n^{1/(k-1)} / n^{R+1}\bigr)$$
as $n \to \infty$ through the natural numbers.

In the paper $S_j$ appears as $A_j(k) / (k - 1)^{j+1}$, with $A_j$ the Eulerian polynomial.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 15, quoting Sondow and Hadjicostas (2007), Theorem 9 and
Lemma 1 (`jis-2024-24.8.1-thm-15`). -/
public theorem_wanted somos_tsum_asymptotic_expansion (k : ℕ) (hk : 2 ≤ k) (a : ℕ → ℝ)
    (ha : ∀ r : ℕ, a r =
      ∑ m ∈ (Fintype.piFinset fun _ : Fin r => Finset.range (r + 1)).filter
          (fun m => ∑ j : Fin r, ((j : ℕ) + 1) * m j = r),
        ∏ j : Fin r, (1 / ((m j).factorial : ℝ)) *
          ((-1 : ℝ) ^ (j : ℕ) / ((j : ℕ) + 1) *
            ∑' i : ℕ, (i : ℝ) ^ ((j : ℕ) + 1) / (k : ℝ) ^ i) ^ (m j))
    (R : ℕ) :
    (fun n : ℕ => Real.exp (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1))
        - (n : ℝ) ^ ((1 : ℝ) / (k - 1)) * (1 + ∑ r ∈ Finset.Icc 1 R, a r / (n : ℝ) ^ r))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (k - 1)) / (n : ℝ) ^ (R + 1))

/-- **Residue of a rational number modulo an integer.** For a natural number $m$ and a rational
number $x = a/b$ in lowest terms with $b > 0$, the residue of $x$ modulo $m$ is the element
$a \cdot b^{-1}$ of $\mathbb{Z}/m\mathbb{Z}$. When $b$ is prime to $m$, $b^{-1}$ is the inverse
of $b$ modulo $m$, so the residue is the class $c$ with $b c \equiv a \pmod m$; for other $x$
the inverse, and hence the residue, is a conventional value with no arithmetic meaning.

For a prime $p$ and a natural number $r$, it is used to read congruences modulo $p^r$ in the
ring $\mathbb{Z}_{(p)}$ of rational numbers whose denominator is prime to $p$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Section 4 (residues of `g_{k,l}(n)` modulo `p^r` in `ℤ_(p)`). -/
public def ratResidue (m : ℕ) (x : ℚ) : ZMod m :=
  (x.num : ZMod m) * (x.den : ZMod m)⁻¹

/-- **Residue of an integer.** For every natural number $m$ and every integer $z$, the residue
modulo $m$ of $z$, viewed as a rational number, is the image of $z$ in $\mathbb{Z}/m\mathbb{Z}$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Section 4. -/
public theorem ratResidue_intCast (m : ℕ) (z : ℤ) : ratResidue m z = (z : ZMod m) := by
  simp [ratResidue]

/-- **Residues of the $(k, l)$-Göbel sequence modulo $p^r$.** Let $p$ be a prime, let
$k, l, r \ge 2$ be natural numbers, and let $g_{k,l}$ be the $(k, l)$-Göbel sequence. Let $I$ be
the set of natural numbers $n$ with $1 \le n < p$ such that $g_{k,l}(n) = 0$ or
$\nu_p(g_{k,l}(n)) \ge r - 1$, where $\nu_p$ is the $p$-adic valuation on $\mathbb{Q}$; that is,
$g_{k,l}(n) \equiv 0 \pmod{p^{r-1}}$ in $\mathbb{Z}_{(p)}$. Let $G$ be the set of residues of the
numbers $g_{k,l}(n)$, $n \in I$, in $\mathbb{Z}/p^r\mathbb{Z}$, the residue of a rational number
being its numerator times the inverse of its denominator. Then $G = \{0\}$ or $G$ has exactly as
many elements as $I$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 18 (`jis-2024-24.8.1-thm-18`). -/
public theorem_wanted gobelSequence_residues_singleton_or_injective (p : ℕ) (hp : p.Prime)
    (k l r : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (hr : 2 ≤ r) :
    ((Finset.Ico 1 p).filter (fun n => gobelSequence k l n = 0 ∨
          ((r : ℤ) - 1 ≤ padicValRat p (gobelSequence k l n)))).image
        (fun n => ratResidue (p ^ r) (gobelSequence k l n)) = {0} ∨
      (((Finset.Ico 1 p).filter (fun n => gobelSequence k l n = 0 ∨
          ((r : ℤ) - 1 ≤ padicValRat p (gobelSequence k l n)))).image
        (fun n => ratResidue (p ^ r) (gobelSequence k l n))).card =
      ((Finset.Ico 1 p).filter (fun n => gobelSequence k l n = 0 ∨
          ((r : ℤ) - 1 ≤ padicValRat p (gobelSequence k l n)))).card

/-- **Propagation of a congruence along the $(k, l)$-Göbel sequence.** Let $p$ be a prime, let
$k, l, r \ge 2$ be natural numbers, let $g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $a, b$ be
natural numbers with $1 \le a < p$ and $b < p$. For rational numbers $x, y$ write
$x \equiv y \pmod{p^r}$ when $x = y$ or $\nu_p(x - y) \ge r$, where $\nu_p$ is the $p$-adic
valuation on $\mathbb{Q}$. If $g_{k,l}(a) \equiv b p^{r-1} \pmod{p^r}$, then
$n \, g_{k,l}(n) \equiv a b p^{r-1} \pmod{p^r}$ for every natural number $n$ with $a \le n < p$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 20 (`jis-2024-24.8.1-lem-20`). -/
public theorem_wanted gobelSequence_mul_index_congr (p : ℕ) (hp : p.Prime) (k l r a b : ℕ)
    (hk : 2 ≤ k) (hl : 2 ≤ l) (hr : 2 ≤ r) (ha₁ : 1 ≤ a) (hap : a < p) (hbp : b < p)
    (hg : gobelSequence k l a - b * (p : ℚ) ^ (r - 1) = 0 ∨
      (r : ℤ) ≤ padicValRat p (gobelSequence k l a - b * (p : ℚ) ^ (r - 1)))
    (n : ℕ) (han : a ≤ n) (hnp : n < p) :
    n * gobelSequence k l n - a * b * (p : ℚ) ^ (r - 1) = 0 ∨
      (r : ℤ) ≤ padicValRat p (n * gobelSequence k l n - a * b * (p : ℚ) ^ (r - 1))

end

end MetaMathlibExt
