/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import MathlibExt.NumberTheory.WieferichPrime
public import MathlibExt.NumberTheory.FiniteMultipleZetaLevelColoredFiniteMZVOneEqPowMulSumProd
public import MathlibExt.NumberTheory.FiniteMultipleZetaLevelExistsBoundBernoulliIffFiniteIInter

/-!
# Regular primes, non-Wieferich primes and finite multiple zeta values of level `N`

Statements from Shin-ichiro Seki, *Regular Primes, Non-Wieferich Primes, and Finite
Multiple Zeta Values of Level N*, INTEGERS 24 (2024), Article A22 (arXiv:2310.06809).
The statement `exists_bound_bernoulli_iff_finite_iInter` is proved in
`MathlibExt.NumberTheory.FiniteMultipleZetaLevelExistsBoundBernoulliIffFiniteIInter`.

The paper works in `𝒜 = (∏_p ℤ/pℤ) / (⊕_p ℤ/pℤ)`. An identity "holds in `𝒜`" exactly
when it holds modulo `p` for all but finitely many primes `p`; it is stated here as
`∀ᶠ p in atTop, p.Prime → …` in `ZMod p`. A rational number `a/b` is reduced modulo `p`
as `(a : ZMod p) * (b : ZMod p)⁻¹`. The Bernoulli–Seki numbers (`B₁ = +1/2`) are
Mathlib's `bernoulli'`; only even indices `≥ 2` occur below.

For an index `k = (k₁, …, k_r)` (here `k : Fin r → ℕ`) and colors
`α ∈ (ℤ/Nℤ)^r`, `ζ^α_{p,N}(k) = ∑ 1/(m₁^{k₁} ⋯ m_r^{k_r})` over `0 < m₁ < ⋯ < m_r < p`
with `mᵢ ≡ αᵢ (mod N)` (`coloredFiniteMZV`). The color map `[j]` sends the class of `p`
to `(-j p, …, -j p)`, so `ζ^{[j]}_{𝒜,N}(k)` has `p`-component
`ζ^{(-jp, …, -jp)}_{p,N}(k)`.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- **Colored finite multiple harmonic sum of the empty index.** For all natural numbers $p$
and $N$, the colored finite multiple harmonic sum $\zeta^{\varnothing}_{p,N}(\varnothing)$ of the
empty index, with the empty tuple of colors, equals $1$ in $\mathbb{Z}/p\mathbb{Z}$.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Section 2.2 (`ζ^∅_{p,N}(∅) = 1`). -/
theorem coloredFiniteMZV_zero (p N : ℕ) (k : Fin 0 → ℕ) (α : Fin 0 → ZMod N) :
    coloredFiniteMZV p N k α = 1 := by
  classical
  rw [coloredFiniteMZV, Finset.filter_true_of_mem fun m _ =>
    ⟨fun a => Fin.elim0 a, fun i => Fin.elim0 i⟩]
  simp

/-- **Sums over a subinterval of $(0, p)$ as colored finite multiple zeta values.** Let
$N \ge 1$, $0 \le j < N$, and let $k = (k_1, \dots, k_r)$ be a tuple of natural numbers of weight
$w = k_1 + \dots + k_r$. For a prime $p$ and $\alpha \in (\mathbb{Z}/N\mathbb{Z})^r$ let
$\zeta^{\alpha}_{p,N}(k) \in \mathbb{Z}/p\mathbb{Z}$ be the colored finite multiple harmonic sum,
the sum of $1/(m_1^{k_1} \cdots m_r^{k_r})$ over the integers $0 < m_1 < \dots < m_r < p$ with
$m_i \equiv \alpha_i \pmod{N}$ for all $i$. Then for all but finitely many primes $p$, with
$\alpha = (-jp, \dots, -jp) \in (\mathbb{Z}/N\mathbb{Z})^r$,
$\sum 1/(m_1^{k_1} \cdots m_r^{k_r}) = N^w \zeta^{\alpha}_{p,N}(k)$ in $\mathbb{Z}/p\mathbb{Z}$,
where the sum is over the integers $m_1, \dots, m_r$ with
$jp/N < m_1 < \dots < m_r < (j+1)p/N$.

The entries of $k$ may be $0$; the paper's indices have positive entries.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Lemma 1 (`integers-2024-A22-lem-1`). -/
public theorem_wanted sum_Ioo_eq_pow_mul_coloredFiniteMZV {N j r : ℕ} (hN : 0 < N) (hj : j < N)
    (k : Fin r → ℕ) :
    ∀ᶠ p in atTop, p.Prime →
      (∑ m ∈ (Finset.univ : Finset (Fin r → Fin p)).filter
          (fun m : Fin r → Fin p => StrictMono m ∧
            ∀ i, j * p < N * (m i : ℕ) ∧ N * (m i : ℕ) < (j + 1) * p),
        ∏ i, (((m i : ℕ) : ZMod p)⁻¹) ^ k i) =
        (N : ZMod p) ^ (∑ i, k i) * coloredFiniteMZV p N k fun _ => -(j : ZMod N) * p

/-- **Level-$12$ colored finite zeta values and Bernoulli numbers.** Let $k \ge 3$ be odd. For a
prime $p > k$ write $Z_p(k) = B_{p-k}/k \in \mathbb{Z}/p\mathbb{Z}$, where $B_n$ is the $n$-th
Bernoulli number, and for $\alpha \in \mathbb{Z}/12\mathbb{Z}$ let
$\zeta^{\alpha}_{p,12}(k) \in \mathbb{Z}/p\mathbb{Z}$ be the sum of $m^{-k}$ over $0 < m < p$ with
$m \equiv \alpha \pmod{12}$. Then for all but finitely many primes $p$, in $\mathbb{Z}/p\mathbb{Z}$,
$2\zeta^{-2p}_{p,12}(k) = (2^{-k} - 3^{-k} - 4^{-k} + 12^{-k}) Z_p(k)$ and
$2\zeta^{-3p}_{p,12}(k) = (3^{-k} - 4^{-k} - 6^{-k} + 12^{-k}) Z_p(k)$.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Proposition 3 (`integers-2024-A22-prop-3`). -/
public theorem_wanted two_mul_coloredFiniteMZV_twelve {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k) :
    ∀ᶠ p in atTop, p.Prime →
      let Z : ZMod p := ((bernoulli' (p - k)).num : ZMod p) *
        ((bernoulli' (p - k)).den : ZMod p)⁻¹ * (k : ZMod p)⁻¹
      2 * coloredFiniteMZV p 12 ![k] ![-(2 : ZMod 12) * p] =
          (((2 : ZMod p) ^ k)⁻¹ - ((3 : ZMod p) ^ k)⁻¹ - ((4 : ZMod p) ^ k)⁻¹ +
            ((12 : ZMod p) ^ k)⁻¹) * Z ∧
        2 * coloredFiniteMZV p 12 ![k] ![-(3 : ZMod 12) * p] =
          (((3 : ZMod p) ^ k)⁻¹ - ((4 : ZMod p) ^ k)⁻¹ - ((6 : ZMod p) ^ k)⁻¹ +
            ((12 : ZMod p) ^ k)⁻¹) * Z

/-- **Wieferich's criterion for the first case of Fermat's Last Theorem.** Let $p$ be a prime
that is not a Wieferich prime, that is, $p^2 \nmid 2^{p-1} - 1$. Then there are no integers
$x, y, z$ with $p \nmid xyz$ and $x^p + y^p = z^p$.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Theorem 2 (`integers-2024-A22-thm-2`). -/
public theorem_wanted fermat_first_case_of_not_isWieferichPrime {p : ℕ} (hp : p.Prime)
    (hW : ¬ p.IsWieferichPrime) (x y z : ℤ) (hxyz : ¬ (p : ℤ) ∣ x * y * z) :
    x ^ p + y ^ p ≠ z ^ p

/-- **Skula–Dobson–Ichimura congruence for the Fermat quotient of $2$.** Let $p$ be an odd prime
and $N$ a positive integer with $p \nmid N$. Write $q_p(2) = (2^{p-1} - 1)/p$ for the Fermat
quotient of $2$, and for integers $i \ge 0$ and $M \ge 1$ let $s_p(i, M) \in \mathbb{Z}/p\mathbb{Z}$
be the sum of $m^{-1}$ over the integers $m$ with $0 < m < p$ and $ip/M < m < (i+1)p/M$. Then
$(N + 1)\, q_p(2) \equiv -\sum_{0 \le j < N/2} s_p(2j, 2N) \pmod{p}$.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Theorem 3 (`integers-2024-A22-thm-3`). -/
public theorem_wanted fermatQuotient_two_mul_eq_neg_sum {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : 0 < N) (hpN : ¬ p ∣ N) :
    ((N + 1 : ℕ) : ZMod p) * (((2 ^ (p - 1) - 1) / p : ℕ) : ZMod p) =
      -∑ j ∈ (Finset.range N).filter (fun j => 2 * j < N),
        ∑ m ∈ (Finset.Ioo 0 p).filter
            (fun m => 2 * j * p < 2 * N * m ∧ 2 * N * m < (2 * j + 1) * p),
          ((m : ZMod p)⁻¹)

/-- **A small odd $k$ with $p \nmid B_{p-k}$.** For every prime $p \ge 11$ there is an odd
integer $k \ge 3$ such that $p$ does not divide the numerator of the Bernoulli number $B_{p-k}$
and $k \le (p-3)/2$ if $p \equiv 1 \pmod 4$, while $k \le (p-5)/2$ if
$p \equiv 3 \pmod 4$.

Equivalently, the least such odd $k$ is at most this bound. Since $p - k$ is even and at least
$2$, the convention for $B_1$ does not matter.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Proposition 5 (`integers-2024-A22-prop-5`). -/
public theorem_wanted exists_odd_not_dvd_bernoulli_num_le {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ∃ k, Odd k ∧ 3 ≤ k ∧ ¬ (p : ℤ) ∣ (bernoulli' (p - k)).num ∧
      k ≤ if p % 4 = 1 then (p - 3) / 2 else (p - 5) / 2

/-- **Reversal for finite multiple zeta values of level $N$.** Let $N \ge 1$, let
$k = (k_1, \dots, k_r)$ be a tuple of natural numbers of weight $w = k_1 + \dots + k_r$, and let
$c$ be a color map, which sends each $a \in \mathbb{Z}/N\mathbb{Z}$ either to $\emptyset$ or to a
tuple in $(\mathbb{Z}/N\mathbb{Z})^r$. Write $k^{\leftarrow} = (k_r, \dots, k_1)$, and let
$c^{\leftarrow}$ be the color map with $c^{\leftarrow}(a) = (a - \alpha_r, \dots, a - \alpha_1)$
when $c(a) = (\alpha_1, \dots, \alpha_r)$ and $c^{\leftarrow}(a) = \emptyset$ when
$c(a) = \emptyset$. Then for all but finitely many primes $p$, the $p$-components of the finite
multiple zeta values of level $N$ with these color maps satisfy
$\zeta^{c}_{\mathcal{A},N}(k)_p = (-1)^w \zeta^{c^{\leftarrow}}_{\mathcal{A},N}(k^{\leftarrow})_p$
in $\mathbb{Z}/p\mathbb{Z}$.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Proposition 1 (`integers-2024-A22-prop-1`). -/
public theorem_wanted finiteMZVColored_eq_neg_one_pow_mul_reverse {N r : ℕ} (hN : 0 < N)
    (k : Fin r → ℕ) (c : ZMod N → Option (Fin r → ZMod N)) :
    ∀ᶠ p in atTop, p.Prime →
      finiteMZVColored p N k c = (-1) ^ (∑ i, k i) *
        finiteMZVColored p N (k ∘ Fin.rev) (fun a => (c a).map fun β i => a - β (Fin.rev i))

/-- **Criterion for a uniform bound on the least non-Wieferich base.** The following are
equivalent:
(a) there is a natural number $M$ such that for every odd prime $p$ there is an integer $N$ with
$1 \le N \le M$, $p \nmid N$ and $p^2 \nmid N^{p-1} - 1$;
(b) there is a natural number $M \ge 3$ such that only finitely many primes $p$ satisfy
$p^2 \mid N^{p-1} - 1$ for every integer $N$ with $2 \le N \le M$.

For $p \nmid N$ the condition $p^2 \nmid N^{p-1} - 1$ says that $p$ does not divide the Fermat
quotient $q_p(N) = (N^{p-1} - 1)/p$, so (a) bounds, uniformly in $p$, the least such base $N$;
(b) says that $\bigcap_{N=2}^{M} W(N)$ is finite, where $W(N)$ is the set of primes $p$ with
$N^{p-1} \equiv 1 \pmod{p^2}$.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Lemma 3 (`integers-2024-A22-lem-3`). -/
public theorem_wanted exists_bound_fermatQuotient_iff_finite_iInter :
    (∃ M : ℕ, ∀ p : ℕ, p.Prime → p ≠ 2 →
        ∃ N, 1 ≤ N ∧ N ≤ M ∧ ¬ p ∣ N ∧ ¬ p ^ 2 ∣ N ^ (p - 1) - 1) ↔
      ∃ M : ℕ, 3 ≤ M ∧
        {p : ℕ | p.Prime ∧ ∀ N ∈ Finset.Icc 2 M, p ^ 2 ∣ N ^ (p - 1) - 1}.Finite

/-- **Regular and non-Wieferich primes give non-vanishing finite multiple zeta values.**
(i) Suppose that infinitely many odd primes $p$ are regular, in the sense that $p$ does not
divide the class number of any $p$-th cyclotomic field over $\mathbb{Q}$. Then for every
natural number $w \notin \{1, 2, 4\}$ there is an index $k = (k_1, \dots, k_r)$ of positive
integers with $k_1 + \dots + k_r = w$ such that
$\zeta_p(k) = \sum_{0 < m_1 < \dots < m_r < p} m_1^{-k_1} \cdots m_r^{-k_r}$ is non-zero in
$\mathbb{Z}/p\mathbb{Z}$ for infinitely many primes $p$.
(ii) Suppose that infinitely many primes are not Wieferich primes. Then for every even $N > 0$
and every natural number $w$ there are an index $k = (k_1, \dots, k_r)$ of positive integers with
$k_1 + \dots + k_r = w$ and a color map $c$ from $\mathbb{Z}/N\mathbb{Z}$ to
$(\mathbb{Z}/N\mathbb{Z})^r \cup \{\varnothing\}$ such that the $p$-component
$\zeta^{c}_{p,N}(k)$ of the finite multiple zeta value of level $N$ with color map $c$ is
non-zero in $\mathbb{Z}/p\mathbb{Z}$ for infinitely many primes $p$.

The weight $w = 0$ is allowed (the empty index has value $1$); the paper takes $w$ positive.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Proposition 2 (`integers-2024-A22-prop-2`). -/
public theorem_wanted exists_finiteMZV_ne_zero_of_conjectures :
    ({p : ℕ | p.Prime ∧ p ≠ 2 ∧ ∀ (K : Type) [Field K] [NumberField K]
        [IsCyclotomicExtension {p} ℚ K], ¬ p ∣ NumberField.classNumber K}.Infinite →
      ∀ w : ℕ, w ≠ 1 → w ≠ 2 → w ≠ 4 →
        ∃ (r : ℕ) (k : Fin r → ℕ), (∀ i, 0 < k i) ∧ ∑ i, k i = w ∧
          {p : ℕ | p.Prime ∧ coloredFiniteMZV p 1 k 0 ≠ 0}.Infinite) ∧
    ({p : ℕ | p.Prime ∧ ¬ p.IsWieferichPrime}.Infinite →
      ∀ N w : ℕ, 0 < N → Even N →
        ∃ (r : ℕ) (k : Fin r → ℕ) (c : ZMod N → Option (Fin r → ZMod N)),
          (∀ i, 0 < k i) ∧ ∑ i, k i = w ∧
            {p : ℕ | p.Prime ∧ finiteMZVColored p N k c ≠ 0}.Infinite)

end

end MetaMathlibExt
