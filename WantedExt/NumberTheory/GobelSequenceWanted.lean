/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.GobelSequence
public import MathlibExt.NumberTheory.GobelSequenceError
public import MathlibExt.NumberTheory.GobelSequenceRoots
public import MathlibExt.NumberTheory.GobelSequenceSomosBound
public import MathlibExt.NumberTheory.SomosLikeRoots
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.GobelSequenceGobelSequenceErrorEqTsumLe

namespace MetaMathlibExt

open Filter Topology Asymptotics

@[expose] public section

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

end

end MetaMathlibExt
