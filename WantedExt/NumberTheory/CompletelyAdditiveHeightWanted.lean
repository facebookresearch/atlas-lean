/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Completely additive height functions

Statements from Hartosh Singh Bal, *Completely Additive Height Functions: Profile
Laws, Matula Bounds, and Inverse Growth*, INTEGERS 26 (2026), Article A116.

A height function is a completely additive `H : ℕ → ℕ` (on positive integers) with `H(p) ≥ 1`
for every prime `p` and only finitely many primes at each height `n ≥ 1`. Primes are indexed
from one: `p₁ = 2, p₂ = 3, …`, so `pᵢ = Nat.nth Nat.Prime (i - 1)`, and the index of a prime `p`
is `Nat.count Nat.Prime p + 1`. Iteratively defined height functions (Matula's
`H(pᵢ) = H(i) + 1`) are stated for every completely additive `H` satisfying the defining
equations, which determine `H` uniquely by strong induction.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- **Completely additive functions on the positive integers.** A function
$H : \mathbb{N} \to \mathbb{N}$ is completely additive on the positive integers if
$H(ab) = H(a) + H(b)$ for all integers $a, b \ge 1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (definition of a height
function). -/
public def IsCompletelyAdditiveNat (H : ℕ → ℕ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → H (a * b) = H a + H b

/-- **A completely additive function vanishes at one.** If $H : \mathbb{N} \to \mathbb{N}$ is
completely additive on the positive integers, that is, $H(ab) = H(a) + H(b)$ for all $a, b \ge 1$,
then $H(1) = 0$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (definition of a height
function). -/
public theorem IsCompletelyAdditiveNat.map_one {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H) :
    H 1 = 0 := by
  have := hH 1 1 one_pos one_pos
  simp at this
  omega

/-- **Height functions.** A function $H : \mathbb{N} \to \mathbb{N}$ is a height function if it is
completely additive on the positive integers, that is $H(ab) = H(a) + H(b)$ for all integers
$a, b \ge 1$; if $H(p) \ge 1$ for every prime $p$; and if for every $n \ge 1$ only finitely many
primes $p$ have $H(p) = n$.

Complete additivity forces $H(1) = 0$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (definition of a height
function). -/
public structure IsHeightFunction (H : ℕ → ℕ) : Prop where
  additive : IsCompletelyAdditiveNat H
  prime_pos : ∀ p : ℕ, p.Prime → 1 ≤ H p
  finite_primes : ∀ n : ℕ, 1 ≤ n → {p : ℕ | p.Prime ∧ H p = n}.Finite

/-- **The $i$-th prime.** For a natural number $i \ge 1$, $p_i$ denotes the $i$-th prime in
increasing order, so that $p_1 = 2$. For $i = 0$ the definition also gives $p_0 = 2$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (notation `pᵢ`). -/
public noncomputable def nthPrimeOne (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime (i - 1)

/-- **The first three primes.** With primes indexed from one, the first three primes are
$p_1 = 2$, $p_2 = 3$ and $p_3 = 5$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (notation `pᵢ`). -/
public theorem nthPrimeOne_one_two_three :
    nthPrimeOne 1 = 2 ∧ nthPrimeOne 2 = 3 ∧ nthPrimeOne 3 = 5 :=
  ⟨Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five⟩

/-- **Completely additive function with prescribed prime values.** Given a function
$v : \mathbb{N} \to \mathbb{N}$, this is the function $\mathbb{N} \to \mathbb{N}$ that sends each
$m \ge 1$ with prime factorization $m = \prod_p p^{a_p}$ to $\sum_p a_p\, v(p)$, and sends $0$
to $0$. Only the values of $v$ at primes matter.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public noncomputable def additiveOfPrimeValues (v : ℕ → ℕ) (m : ℕ) : ℕ :=
  m.factorization.sum fun p a => a * v p

/-- **The completely additive extension vanishes at one.** For every function
$v : \mathbb{N} \to \mathbb{N}$, the completely additive function with prime values $v$ (which
sends $m = \prod_p p^{a_p}$ to $\sum_p a_p\, v(p)$) takes the value $0$ at $1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public theorem additiveOfPrimeValues_one (v : ℕ → ℕ) : additiveOfPrimeValues v 1 = 0 := by
  simp [additiveOfPrimeValues]

/-- **The completely additive extension at a prime.** For every function
$v : \mathbb{N} \to \mathbb{N}$ and every prime $p$, the completely additive function with prime
values $v$ (which sends $m = \prod_q q^{a_q}$ to $\sum_q a_q\, v(q)$) takes the value $v(p)$
at $p$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public theorem additiveOfPrimeValues_prime (v : ℕ → ℕ) {p : ℕ} (hp : p.Prime) :
    additiveOfPrimeValues v p = v p := by
  simp [additiveOfPrimeValues, hp.factorization]

/-- **The extension from prime values is completely additive.** For every function
$v : \mathbb{N} \to \mathbb{N}$, let $H_v$ be the function with $H_v(m) = \sum_p a_p v(p)$ for
$m = \prod_p p^{a_p}$. Then $H_v$ is completely additive on the positive integers:
$H_v(ab) = H_v(a) + H_v(b)$ for all integers $a, b \ge 1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public theorem isCompletelyAdditiveNat_additiveOfPrimeValues (v : ℕ → ℕ) :
    IsCompletelyAdditiveNat (additiveOfPrimeValues v) := by
  intro a b ha hb
  unfold additiveOfPrimeValues
  rw [Nat.factorization_mul ha.ne' hb.ne']
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/-- **Level construction for a height function.** Let $H$ be a height function and let $n \ge 1$,
and for $k \ge 0$ write $\mathcal{H}_k = \{m \ge 1 : H(m) = k\}$. Then $\mathcal{H}_n$ is the union
of two sets: the set of products $p m'$, where $p$ is a prime with $H(p) = \ell$ for some integer
$\ell$ with $1 \le \ell \le \lfloor n/2 \rfloor$ and $m' \in \mathcal{H}_{n - \ell}$; and the set
of primes $p$ with $H(p) = n$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 1 (`integers-2026-A116-thm-1`). -/
public theorem_wanted heightLevel_eq_products_union_primes {H : ℕ → ℕ} (hH : IsHeightFunction H)
    {n : ℕ} (hn : 1 ≤ n) :
    {m : ℕ | 0 < m ∧ H m = n} =
      {m : ℕ | ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ n / 2 ∧ ∃ p m', p.Prime ∧ H p = ℓ ∧ 0 < m' ∧ H m' = n - ℓ ∧
        m = p * m'} ∪ {p : ℕ | p.Prime ∧ H p = n}

/-- **Height levels are counted by coloured partitions.** Let $H$ be a height function and, for
$\ell \ge 1$, let $\pi_\ell$ be the number of primes $p$ with $H(p) = \ell$. For every $n \ge 0$,
the number of positive integers $m$ with $H(m) = n$ equals the number of families
$(\alpha_{\ell,j})$ of nonnegative integers indexed by $1 \le \ell \le n$ and $0 \le j < \pi_\ell$
with $\sum_{\ell,j} \ell\, \alpha_{\ell,j} = n$, that is, the number of partitions of $n$ in which
a part of size $\ell$ comes in $\pi_\ell$ colours.

This is the level-by-level form of the statement that $H$ induces a height-preserving bijection
between the positive integers and such coloured partitions.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 1
(`integers-2026-A116-prop-1`). -/
public theorem_wanted heightLevel_card_eq_multipartitions {H : ℕ → ℕ} (hH : IsHeightFunction H)
    (n : ℕ) :
    Nat.card {m : ℕ // 0 < m ∧ H m = n} =
      Nat.card {α : (Σ ℓ : Fin n, Fin {p : ℕ | p.Prime ∧ H p = ℓ.1 + 1}.ncard) → ℕ //
        ∑ x, (x.1.1 + 1) * α x = n}

/-- **Realizing a prescribed profile.** Let $(\pi_k)_{k \ge 1}$ be nonnegative integers with
$\pi_k \ne 0$ for infinitely many $k$ (equivalently, $\sum_k \pi_k = \infty$). Then there is a
height function $H$ such that for every $k \ge 1$ exactly $\pi_k$ primes $p$ satisfy $H(p) = k$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 2
(`integers-2026-A116-prop-2`). -/
public theorem_wanted exists_heightFunction_with_profile (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) :
    ∃ H : ℕ → ℕ, IsHeightFunction H ∧ ∀ k, 1 ≤ k → {p : ℕ | p.Prime ∧ H p = k}.ncard = π k

/-- **Height functions with prescribed values at the primes.** Let $f : \mathbb{N} \to \mathbb{N}$
satisfy $f(i) \ge 1$ for every $i \ge 1$, and suppose that for every $t \ge 1$ only finitely many
$i \ge 1$ have $f(i) = t$. Let $H$ be the completely additive function on the positive integers
with $H(p) = f(i)$ when $p$ is the $i$-th prime (so $H(2) = f(1)$). Then $H$ is a height function,
and for every $n \ge 1$ the number of primes $p$ with $H(p) = n$ equals the number of integers
$i \ge 1$ with $f(i) = n$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3
(`integers-2026-A116-prop-3`). -/
public theorem_wanted isHeightFunction_of_finite_fibers (f : ℕ → ℕ)
    (hpos : ∀ i, 1 ≤ i → 1 ≤ f i) (hfin : ∀ t, 1 ≤ t → {i : ℕ | 1 ≤ i ∧ f i = t}.Finite) :
    let H := additiveOfPrimeValues fun p => f (Nat.count Nat.Prime p + 1)
    IsHeightFunction H ∧
      ∀ n, 1 ≤ n → {p : ℕ | p.Prime ∧ H p = n}.ncard = {i : ℕ | 1 ≤ i ∧ f i = n}.ncard

/-- **The largest integer at each height for the prime-index height.** Let $H$ be the completely
additive function on the positive integers with $H(p) = i$ when $p$ is the $i$-th prime, so that
$H(2) = 1$, $H(3) = 2$ and $H(5) = 3$. For every natural number $n$, $2^n$ is the largest integer
$m \ge 1$ with $H(m) = n$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 4
(`integers-2026-A116-prop-4`). -/
public theorem_wanted isGreatest_primeIndexHeight_level (n : ℕ) :
    IsGreatest
      {m : ℕ | 0 < m ∧ additiveOfPrimeValues (fun p => Nat.count Nat.Prime p + 1) m = n} (2 ^ n)

/-- **Gutman–Ivić maximal Matula numbers.** Write $p_i$ for the $i$-th prime, indexed from one
($p_1 = 2$). For a natural number $n$, $P(n)$ is the result of applying $i \mapsto p_i$ to $8$
exactly $n - 3$ times, so $P(4) = p_8$ and $P(n) = p_{P(n-1)}$ for $n \ge 5$. For $n \le 3$ there
are no applications and $P(n) = 8$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 3.2 (definition of `P(n)`). -/
public noncomputable def matulaMax (n : ℕ) : ℕ :=
  nthPrimeOne^[n - 3] 8

/-- **The first maximal Matula number.** The Gutman–Ivić maximal Matula number $P(4)$ equals
$p_8$, the eighth prime.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 3.2 (definition of `P(n)`). -/
public theorem matulaMax_four : matulaMax 4 = nthPrimeOne 8 :=
  rfl

/-- **Recursion for the maximal Matula numbers.** Write $p_i$ for the $i$-th prime, indexed from
one ($p_1 = 2$). For every $n \ge 4$ the Gutman–Ivić maximal Matula numbers satisfy
$P(n + 1) = p_{P(n)}$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 3.2 (definition of `P(n)`). -/
public theorem matulaMax_succ {n : ℕ} (hn : 4 ≤ n) :
    matulaMax (n + 1) = nthPrimeOne (matulaMax n) := by
  unfold matulaMax
  rw [show n + 1 - 3 = (n - 3) + 1 by omega, Function.iterate_succ_apply']

/-- **Largest number at a given Matula height.** Write $p_i$ for the $i$-th prime, indexed from
one ($p_1 = 2$), and let $H$ be a function from the natural numbers to themselves that is
completely additive on the positive integers and satisfies $H(p_i) = H(i) + 1$ for every $i \ge 1$
(Matula's height function). Then for every $n \ge 4$ the largest positive integer $m$ with
$H(m) = n$ is the Gutman–Ivić maximal Matula number $P(n)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 5
(`integers-2026-A116-prop-5`). -/
public theorem_wanted matula_isGreatest_level {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    (hM : ∀ i, 1 ≤ i → H (nthPrimeOne i) = H i + 1) {n : ℕ} (hn : 4 ≤ n) :
    IsGreatest {m : ℕ | 0 < m ∧ H m = n} (matulaMax n)

/-- **Smallest number at a given Matula height.** Write $p_i$ for the $i$-th prime, indexed from
one ($p_1 = 2$), and let $H$ be a function from the natural numbers to themselves that is
completely additive on the positive integers and satisfies $H(p_i) = H(i) + 1$ for every $i \ge 1$
(Matula's height function). Then for every $n > 1$ the smallest positive integer $m$ with
$H(m) = n$ is $3 \cdot 5^{(n-2)/3}$ if $n \equiv 2 \pmod 3$, $5^{n/3}$ if $n \equiv 0 \pmod 3$, and
$9 \cdot 5^{(n-4)/3}$ if $n \equiv 1 \pmod 3$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 6
(`integers-2026-A116-prop-6`). -/
public theorem_wanted matula_isLeast_level {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    (hM : ∀ i, 1 ≤ i → H (nthPrimeOne i) = H i + 1) {n : ℕ} (hn : 1 < n) :
    IsLeast {m : ℕ | 0 < m ∧ H m = n}
      (if n % 3 = 2 then 3 * 5 ^ ((n - 2) / 3)
        else if n % 3 = 0 then 5 ^ (n / 3) else 9 * 5 ^ ((n - 4) / 3))

/-- **Rosser–Schoenfeld bounds for the $k$-th prime.** Write $p_k$ for the $k$-th prime, indexed
from one ($p_1 = 2$). There is a natural number $k_0$ such that every $k \ge k_0$ satisfies
$k (\log k + \log \log k - 1) \le p_k \le k (\log k + \log \log k)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 1 (`integers-2026-A116-lem-1`),
quoting Rosser and Schoenfeld. -/
public theorem_wanted nthPrimeOne_rosser_schoenfeld :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (k : ℝ) * (Real.log k + Real.log (Real.log k) - 1) ≤ nthPrimeOne k ∧
        (nthPrimeOne k : ℝ) ≤ k * (Real.log k + Real.log (Real.log k))

/-- **The $k$-th prime exceeds $2k$ for $k \ge 6$.** For every natural number $k \ge 6$, the
$k$-th prime $p_k$, indexed from one so that $p_1 = 2$, satisfies $p_k > 2k$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 2 (`integers-2026-A116-lem-2`). -/
public theorem_wanted two_mul_lt_nthPrimeOne {k : ℕ} (hk : 6 ≤ k) : 2 * k < nthPrimeOne k

/-- **Prime-power decomposition of summatory heights.** Let $H : \mathbb{N} \to \mathbb{N}$ be
completely additive on the positive integers, and let $x \ge 2$ be a natural number. Then
$$\sum_{m=1}^{x} H(m) = \sum_{p \le x} \sum_{\alpha \ge 1,\ p^\alpha \le x} H(p)
\left\lfloor \frac{x}{p^\alpha} \right\rfloor,$$
where $p$ runs over the primes $p \le x$.

The paper states this for real $x \ge 2$; both sides depend on $x$ only through $\lfloor x \rfloor$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 7
(`integers-2026-A116-prop-7`), Equation (6). -/
public theorem_wanted sum_height_eq_sum_prime_powers {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    {x : ℕ} (hx : 2 ≤ x) :
    ∑ m ∈ Finset.Icc 1 x, H m =
      ∑ p ∈ (Finset.Iic x).filter Nat.Prime,
        ∑ α ∈ (Finset.Icc 1 x).filter (fun α => p ^ α ≤ x), H p * (x / p ^ α)

/-- **Prime reduction for summatory heights.** Let $H : \mathbb{N} \to \mathbb{N}$ be completely
additive on the positive integers, and for real $x$ let $F(x) = \sum_{1 \le m \le x} H(m)$. Then
there is a real constant $C$ such that for every real $x \ge 2$,
$$\Bigl| F(x) - x \sum_{p \le x} \frac{H(p)}{p - 1} \Bigr| \le C \log x \sum_{p \le x} H(p),$$
where both sums run over the primes $p \le x$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 7
(`integers-2026-A116-prop-7`), "In particular" display. -/
public theorem_wanted sum_height_asymptotic {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (H m : ℝ)) -
          x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (H p : ℝ) / ((p : ℝ) - 1)| ≤
        C * Real.log x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (H p : ℝ)

/-- **Iteratively defined height functions.** Write $p_i$ for the $i$-th prime, so $p_1 = 2$. Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) = 1$; suppose that for all integers $i, r \ge 1$, if
$p_r$ divides $f(i)$ then $r < i$ (this forces $f(i) \ge 1$ for $i \ge 1$); and suppose that for
every $t \ge 1$ only finitely many $i \ge 1$ have $f(i) = t$. Let $j \ge 1$. Then there is a
function $H : \mathbb{N} \to \mathbb{N}$ that is completely additive on the positive integers and
satisfies $H(p_i) = H(f(i)) + j$ for every $i \ge 1$, and every such $H$ is a height function.

The case $i = 1$ gives $H(2) = j$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 2 (`integers-2026-A116-thm-2`). -/
public theorem_wanted isHeightFunction_of_iterative (f : ℕ → ℕ) (hf1 : f 1 = 1)
    (hdiv : ∀ i r, 1 ≤ i → 1 ≤ r → nthPrimeOne r ∣ f i → r < i)
    (hfin : ∀ t, 1 ≤ t → {i : ℕ | 1 ≤ i ∧ f i = t}.Finite) {j : ℕ} (hj : 1 ≤ j) :
    (∃ H : ℕ → ℕ, IsCompletelyAdditiveNat H ∧ ∀ i, 1 ≤ i → H (nthPrimeOne i) = H (f i) + j) ∧
      ∀ H : ℕ → ℕ, IsCompletelyAdditiveNat H → (∀ i, 1 ≤ i → H (nthPrimeOne i) = H (f i) + j) →
        IsHeightFunction H

/-- **Weighted partition coefficients.** Given real weights $(b_k)_{k \ge 0}$, the coefficients
$a_n$ of the weighted partition product $\prod_{k \ge 1} (1 - q^k)^{-b_k}$ are defined by $a_0 = 1$
and, for $n \ge 1$, the logarithmic-derivative recurrence
$n a_n = \sum_{m=1}^{n} \big(\sum_{k \mid m} k b_k\big) a_{n-m}$ (valid for real exponents $b_k$).
The value $b_0$ is unused.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (weighted partitions
`F(q) = ∑ aₙ qⁿ`). -/
public noncomputable def weightedPartitionCoeff (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (∑ m : Fin (n + 1), (∑ k ∈ (m.1 + 1).divisors, (k : ℝ) * b k) *
      weightedPartitionCoeff b (n - m.1)) / (n + 1)
decreasing_by omega

/-- **Zeroth weighted partition coefficient.** For every sequence of real weights $(b_k)$, the
weighted partition coefficient $a_0$ attached to $(b_k)$ equals $1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (weighted partitions
`F(q) = ∑ aₙ qⁿ`). -/
public theorem weightedPartitionCoeff_zero (b : ℕ → ℝ) : weightedPartitionCoeff b 0 = 1 := by
  simp [weightedPartitionCoeff]

/-- **First weighted partition coefficient.** For every sequence of real weights $(b_k)$, the
weighted partition coefficient $a_1$ attached to $(b_k)$ equals $b_1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (weighted partitions
`F(q) = ∑ aₙ qⁿ`). -/
public theorem weightedPartitionCoeff_one (b : ℕ → ℝ) : weightedPartitionCoeff b 1 = b 1 := by
  simp [weightedPartitionCoeff]

/-- **Meinardus' hypotheses.** Let $b_1, b_2, \dots$ be real weights (the value $b_0$ is unused),
let $\alpha$ and $A$ be reals and let $G : \mathbb{C} \to \mathbb{C}$. The weights satisfy
Meinardus' hypotheses (M1)–(M3) with exponent $\alpha$, residue $A$ and continuation $G$ if there
is $C_0$ with $0 < C_0 < 1$ such that: (M1) for $\operatorname{Re} s > \alpha$ the Dirichlet series
$B(s) = \sum_{k \ge 1} b_k k^{-s}$ converges absolutely and equals $G(s)$, and there is a function
$R : \mathbb{C} \to \mathbb{C}$ that is complex differentiable at every point of the closed
half-plane $\{s : \operatorname{Re} s \ge -C_0\}$ relative to that half-plane, with
$G(s) = A/(s - \alpha) + R(s)$ for all $s \ne \alpha$ with $\operatorname{Re} s \ge -C_0$; (M2)
there are $c > 0$ and reals $K$, $T$ with $|G(s)| \le K (1 + |\operatorname{Im} s|)^c$ whenever
$\operatorname{Re} s \ge -C_0$ and $|\operatorname{Im} s| \ge T$; (M3) there are
$\varepsilon > 0$, $C_3 > 0$ and $y_0 > 0$ such that, with
$g(\tau) = \sum_{k \ge 1} b_k e^{-k\tau}$, the inequality
$\operatorname{Re} g(y + 2\pi i x) - g(y) \le -C_3 y^{-\varepsilon}$ holds for all reals
$x$, $y$ with $0 < y < y_0$ and $y^{1 + \varepsilon/2} \le |x| \le 1/2$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (hypotheses of Theorem 3). -/
public def MeinardusHypotheses (b : ℕ → ℝ) (α A : ℝ) (G : ℂ → ℂ) : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ C₀ < 1 ∧
    (∀ s : ℂ, α < s.re →
      LSeriesSummable (fun k => (b k : ℂ)) s ∧ LSeries (fun k => (b k : ℂ)) s = G s) ∧
    (∃ R : ℂ → ℂ, DifferentiableOn ℂ R {s | -C₀ ≤ s.re} ∧
      ∀ s : ℂ, -C₀ ≤ s.re → s ≠ α → G s = A / (s - α) + R s) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ K T : ℝ, ∀ s : ℂ, -C₀ ≤ s.re → T ≤ |s.im| →
      ‖G s‖ ≤ K * (1 + |s.im|) ^ c) ∧
    (∃ ε C₃ y₀ : ℝ, 0 < ε ∧ 0 < C₃ ∧ 0 < y₀ ∧ ∀ y x : ℝ, 0 < y → y < y₀ →
      y ^ (1 + ε / 2) ≤ |x| → |x| ≤ 1 / 2 →
      (∑' k : ℕ, (b (k + 1) : ℂ) *
          Complex.exp (-((k : ℂ) + 1) * ((y : ℂ) + 2 * Real.pi * Complex.I * x))).re -
        ∑' k : ℕ, b (k + 1) * Real.exp (-((k : ℝ) + 1) * y) ≤ -C₃ * y ^ (-ε))

/-- **Meinardus' theorem.** Let $b_0, b_1, b_2, \dots$ be nonnegative reals with $b_k \ne 0$ for
some $k \ge 1$, and let $a_n$ be the coefficients of the weighted partition product
$\prod_{k \ge 1} (1 - q^k)^{-b_k}$. Suppose that the weights satisfy Meinardus' hypotheses
(M1)–(M3) with exponent $\alpha > 0$, residue $A > 0$ and continuation $G$, and put
$\kappa = (\operatorname{Re} G(0) - 1 - \alpha/2)/(\alpha + 1)$ and
$C_2 = (1 + 1/\alpha)\,(A\,\Gamma(\alpha + 1)\,\zeta(\alpha + 1))^{1/(\alpha + 1)}$. Then there is
$C_1 > 0$ with $a_n \sim C_1 n^{\kappa} \exp(C_2 n^{\alpha/(\alpha + 1)})$ as $n \to \infty$, and
$\log a_n \sim C_2 n^{\alpha/(\alpha + 1)}$ as $n \to \infty$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 3 (`integers-2026-A116-thm-3`),
quoting Meinardus. -/
public theorem_wanted meinardus_asymptotic {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hb0 : ∃ k, 1 ≤ k ∧ b k ≠ 0) {α A : ℝ} (hα : 0 < α) (hA : 0 < A) {G : ℂ → ℂ}
    (hM : MeinardusHypotheses b α A G) :
    let κ := ((G 0).re - 1 - α / 2) / (α + 1)
    let C₂ := (1 + 1 / α) *
      (A * Real.Gamma (α + 1) * (riemannZeta (α + 1)).re) ^ (1 / (α + 1))
    (∃ C₁ : ℝ, 0 < C₁ ∧ Asymptotics.IsEquivalent atTop (fun n : ℕ => weightedPartitionCoeff b n)
      (fun n : ℕ => C₁ * (n : ℝ) ^ κ * Real.exp (C₂ * (n : ℝ) ^ (α / (α + 1))))) ∧
      Asymptotics.IsEquivalent atTop (fun n : ℕ => Real.log (weightedPartitionCoeff b n))
        (fun n : ℕ => C₂ * (n : ℝ) ^ (α / (α + 1)))

/-- **A simple pole of a Dirichlet series from the growth of its partial sums.** Let
$(\pi_k)_{k \ge 0}$ be nonnegative real numbers and let $C$, $\alpha$, $\eta$ be positive reals.
Suppose there is a constant $K$ with
$\bigl|\sum_{k=1}^{\lfloor x \rfloor} \pi_k - (C/\alpha) x^{\alpha}\bigr| \le K x^{\alpha - \eta}$
for every real $x \ge 1$. Then the Dirichlet series $B(s) = \sum_{k \ge 1} \pi_k k^{-s}$ converges
absolutely for $\operatorname{Re} s > \alpha$, and there is a function $R$, holomorphic on the
half-plane $\operatorname{Re} s > \alpha - \eta$, with $B(s) = C/(s - \alpha) + R(s)$ for
$\operatorname{Re} s > \alpha$. Moreover, for every $\delta$ with $0 < \delta < \eta$ there is a
constant $K'$ with $|C/(s - \alpha) + R(s)| \le K'(1 + |\operatorname{Im} s|)$ for all complex $s$
with $\operatorname{Re} s \ge \alpha - \eta + \delta$ and $|\operatorname{Im} s| \ge 1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 3 (`integers-2026-A116-lem-3`). -/
public theorem_wanted lseries_profile_simple_pole {π : ℕ → ℝ} (hπ : ∀ k, 0 ≤ π k) {C α η : ℝ}
    (hC : 0 < C) (hα : 0 < α) (hη : 0 < η)
    (hcum : ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x →
      |∑ k ∈ Finset.Icc 1 ⌊x⌋₊, π k - C / α * x ^ α| ≤ K * x ^ (α - η)) :
    (∀ s : ℂ, α < s.re → LSeriesSummable (fun k => (π k : ℂ)) s) ∧
      ∃ R : ℂ → ℂ, DifferentiableOn ℂ R {s | α - η < s.re} ∧
        (∀ s : ℂ, α < s.re → LSeries (fun k => (π k : ℂ)) s = C / (s - α) + R s) ∧
        ∀ δ : ℝ, 0 < δ → δ < η → ∃ K : ℝ, ∀ s : ℂ, α - η + δ ≤ s.re → 1 ≤ |s.im| →
          ‖C / (s - α) + R s‖ ≤ K * (1 + |s.im|)

/-- **Meinardus asymptotics for the levels of a height function.** Let $H$ be a height function,
for $k \ge 0$ let $\pi_k$ be the number of primes $p$ with $H(p) = k$, and for $n \ge 0$ let $N_n$
be the number of integers $m \ge 1$ with $H(m) = n$. Let $\alpha > 0$ and $C > 0$ be real numbers
and suppose that the weights $(\pi_k)$ satisfy Meinardus' hypotheses with exponent $\alpha$,
residue $C$ and some continuation $G$. Put
$C_2 = (1 + 1/\alpha)\bigl(C\,\Gamma(\alpha + 1)\,\zeta(\alpha + 1)\bigr)^{1/(\alpha+1)}$. Then
there are real numbers $C_1 > 0$ and $\kappa$ with
$N_n \sim C_1 n^{\kappa} \exp\bigl(C_2 n^{\alpha/(\alpha+1)}\bigr)$ as $n \to \infty$, and
$\log N_n \sim C_2 n^{\alpha/(\alpha+1)}$ as $n \to \infty$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 4 (`integers-2026-A116-thm-4`). -/
public theorem_wanted heightLevel_card_meinardus {H : ℕ → ℕ} (hH : IsHeightFunction H)
    {α C : ℝ} (hα : 0 < α) (hC : 0 < C) {G : ℂ → ℂ}
    (hM : MeinardusHypotheses (fun k => ({p : ℕ | p.Prime ∧ H p = k}.ncard : ℝ)) α C G) :
    let C₂ := (1 + 1 / α) *
      (C * Real.Gamma (α + 1) * (riemannZeta (α + 1)).re) ^ (1 / (α + 1))
    (∃ C₁ κ : ℝ, 0 < C₁ ∧ Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (Nat.card {m : ℕ // 0 < m ∧ H m = n} : ℝ))
      (fun n : ℕ => C₁ * (n : ℝ) ^ κ * Real.exp (C₂ * (n : ℝ) ^ (α / (α + 1))))) ∧
      Asymptotics.IsEquivalent atTop
        (fun n : ℕ => Real.log (Nat.card {m : ℕ // 0 < m ∧ H m = n} : ℝ))
        (fun n : ℕ => C₂ * (n : ℝ) ^ (α / (α + 1)))

/-- **Identifying the profile from the growth of the levels.** Let $H$ be a height function, for
$k \ge 0$ let $\pi_k$ be the number of primes $p$ with $H(p) = k$, and for $n \ge 0$ let $N_n$ be
the number of integers $m \ge 1$ with $H(m) = n$. Let $r > 0$ and $A > 0$ be real numbers and
suppose that the weights $(\pi_k)$ satisfy Meinardus' hypotheses with exponent $r$, residue $A$
and some continuation $G$. Suppose further that $N_n \sim C_1 n^{\kappa} \exp(C_2 n^{\beta})$ as
$n \to \infty$ for real numbers $C_1 > 0$, $C_2 > 0$, $\kappa$ and $\beta$ with $0 < \beta < 1$.
Then $\beta = r/(r + 1)$, $r = \beta/(1 - \beta)$,
$C_2 = (1 + 1/r)\bigl(A\,\Gamma(r + 1)\,\zeta(r + 1)\bigr)^{1/(r+1)}$, and
$\sum_{k=1}^{\lfloor x \rfloor} \pi_k \sim (A/r)\, x^r$ as the real number $x$ tends to $\infty$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 1 (`integers-2026-A116-cor-1`). -/
public theorem_wanted heightProfile_identification {H : ℕ → ℕ} (hH : IsHeightFunction H)
    {r A : ℝ} (hr : 0 < r) (hA : 0 < A) {G : ℂ → ℂ}
    (hM : MeinardusHypotheses (fun k => ({p : ℕ | p.Prime ∧ H p = k}.ncard : ℝ)) r A G)
    {C₁ C₂ κ β : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hN : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (Nat.card {m : ℕ // 0 < m ∧ H m = n} : ℝ))
      (fun n : ℕ => C₁ * (n : ℝ) ^ κ * Real.exp (C₂ * (n : ℝ) ^ β))) :
    β = r / (r + 1) ∧ r = β / (1 - β) ∧
      C₂ = (1 + 1 / r) * (A * Real.Gamma (r + 1) * (riemannZeta (r + 1)).re) ^ (1 / (r + 1)) ∧
      Asymptotics.IsEquivalent atTop
        (fun x : ℝ => (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, {p : ℕ | p.Prime ∧ H p = k}.ncard : ℝ))
        (fun x : ℝ => A / r * x ^ r)

/-- **Cumulative profile.** For a sequence $\pi : \mathbb{N} \to \mathbb{N}$ and a natural number
$k$, the cumulative profile is $\Pi_k = \sum_{j=1}^{k} \pi_j$. The value $\pi_0$ is not used, and
$\Pi_0 = 0$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public def profilePartialSum (π : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 k, π j

/-- **Recursion for the cumulative profile.** For every sequence $\pi : \mathbb{N} \to \mathbb{N}$
with cumulative profile $\Pi_k = \sum_{j=1}^{k} \pi_j$ and every natural number $k$,
$\Pi_{k+1} = \Pi_k + \pi_{k+1}$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public theorem profilePartialSum_succ (π : ℕ → ℕ) (k : ℕ) :
    profilePartialSum π (k + 1) = profilePartialSum π k + π (k + 1) := by
  simp [profilePartialSum, Finset.sum_Icc_succ_top]

/-- **Block index of a profile.** Let $\pi : \mathbb{N} \to \mathbb{N}$ be a sequence with
cumulative profile $\Pi_k = \sum_{j=1}^{k} \pi_j$. For a natural number $i$, the block index $k(i)$
is the least natural number $k$ with $i \le \Pi_k$, and $k(i) = 0$ if there is no such $k$. When
$i \ge 1$ and $\Pi$ is unbounded, $k(i)$ is the unique $k$ with $\Pi_{k-1} < i \le \Pi_k$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public noncomputable def seqHeightIndex (π : ℕ → ℕ) (i : ℕ) : ℕ :=
  sInf {k | i ≤ profilePartialSum π k}

/-- **Block index of the constant profile.** For the constant profile $\pi_k = 1$, whose cumulative
profile is $\Pi_k = \sum_{j=1}^{k} \pi_j = k$, the block index $k(i)$, the least $k$ with
$i \le \Pi_k$, equals $i$ for every natural number $i$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public theorem seqHeightIndex_const_one (i : ℕ) : seqHeightIndex (fun _ => 1) i = i := by
  have h : ∀ k, profilePartialSum (fun _ => 1) k = k := fun k => by simp [profilePartialSum]
  simp only [seqHeightIndex, h]
  exact le_antisymm (Nat.sInf_le (show i ≤ i from le_rfl))
    (le_csInf ⟨i, show i ≤ i from le_rfl⟩ fun k hk => hk)

/-- **Canonical sequential realization of a profile.** Let $(\pi_k)_{k \ge 1}$ be a sequence of
nonnegative integers with partial sums $\Pi_k = \sum_{1 \le j \le k} \pi_j$. For $i \ge 1$ let
$k(i)$ be the least $k \ge 0$ with $i \le \Pi_k$, or $0$ if there is none, and let
$p_1 = 2, p_2 = 3, \dots$ be the primes in increasing order. The canonical sequential realization
$H_{\mathrm{seq}}$ of $\pi$ is the function $\mathbb{N} \to \mathbb{N}$ that sends $m \ge 1$ to
$\sum_{i \ge 1} a_i\, k(i)$, where $a_i$ is the exponent of $p_i$ in $m$, and sends $0$ to $0$;
thus $H_{\mathrm{seq}}$ is completely additive with $H_{\mathrm{seq}}(p_i) = k(i)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Definition 2 (canonical sequential
realization, Section 7.2). -/
public noncomputable def canonicalSeqHeight (π : ℕ → ℕ) : ℕ → ℕ :=
  additiveOfPrimeValues fun p => seqHeightIndex π (Nat.count Nat.Prime p + 1)

/-- **Inverting a polynomial profile.** Let $\pi : \mathbb{N} \to \mathbb{N}$ be a sequence with
cumulative profile $\Pi_k = \sum_{j=1}^{k} \pi_j$, let $k(i)$ be its block index (the least $k$
with $i \le \Pi_k$, and $0$ if there is none), let $H_{\mathrm{seq}}$ be its canonical sequential
realization, and write $p_i$ for the $i$-th prime, indexed from one. Let $C > 0$ and $\alpha > 0$
be real numbers with $\Pi_k \sim C k^\alpha$ as $k \to \infty$. Then $k(i) \sim (i/C)^{1/\alpha}$
as $i \to \infty$, and $H_{\mathrm{seq}}(p_i) = k(i)$ for every $i \ge 1$.

The paper also assumes that $\Pi_k$ is eventually strictly increasing; that hypothesis is dropped
here, since $\Pi$ is nondecreasing, which suffices.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 4 (`integers-2026-A116-lem-4`). -/
public theorem_wanted seqHeightIndex_isEquivalent {π : ℕ → ℕ} {C α : ℝ} (hC : 0 < C)
    (hα : 0 < α)
    (hcum : Asymptotics.IsEquivalent atTop (fun k : ℕ => (profilePartialSum π k : ℝ))
      (fun k : ℕ => C * (k : ℝ) ^ α)) :
    Asymptotics.IsEquivalent atTop (fun i : ℕ => (seqHeightIndex π i : ℝ))
        (fun i : ℕ => ((i : ℝ) / C) ^ (1 / α)) ∧
      ∀ i, 1 ≤ i → canonicalSeqHeight π (nthPrimeOne i) = seqHeightIndex π i

/-- **A logarithmic-integral sum.** For every real $\beta > 0$,
$$\sum_{i=2}^{m} \frac{i^{\beta - 1}}{\log i} \sim \frac{m^\beta}{\beta \log m}$$
as $m \to \infty$ through the natural numbers.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 5 (`integers-2026-A116-lem-5`). -/
public theorem_wanted sum_rpow_div_log_isEquivalent {β : ℝ} (hβ : 0 < β) :
    Asymptotics.IsEquivalent atTop
      (fun m : ℕ => ∑ i ∈ Finset.Icc 2 m, (i : ℝ) ^ (β - 1) / Real.log i)
      (fun m : ℕ => (m : ℝ) ^ β / (β * Real.log m))

/-- **Prime-harmonic growth of the canonical sequential realization.** Let $(\pi_k)_{k \ge 1}$ be
a sequence of nonnegative integers with partial sums $\Pi_k = \sum_{1 \le j \le k} \pi_j$, let
$H_{\mathrm{seq}}$ be its canonical sequential realization, and suppose that $C > 0$ and
$\alpha > 0$ are real numbers with $\Pi_k \sim C k^\alpha$ as $k \to \infty$. Write
$S(x) = \sum_{p \le x} H_{\mathrm{seq}}(p)/p$, the sum over primes $p \le x$, and let $m(x)$ be
the number of primes $p \le x$. Then, as $x \to \infty$ over the reals,
$S(x) \sim \frac{\alpha}{C^{1/\alpha}} \cdot \frac{m(x)^{1/\alpha}}{\log m(x)}$ and
$S(x) = \Theta\bigl(x^{1/\alpha} / (\log x)^{1+1/\alpha}\bigr)$, where $f = \Theta(g)$ means
$f = O(g)$ and $g = O(f)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 5 (`integers-2026-A116-thm-5`). -/
public theorem_wanted canonicalSeq_primeHarmonicSum {π : ℕ → ℕ} {C α : ℝ} (hC : 0 < C)
    (hα : 0 < α)
    (hcum : Asymptotics.IsEquivalent atTop (fun k : ℕ => (profilePartialSum π k : ℝ))
      (fun k : ℕ => C * (k : ℝ) ^ α)) :
    Asymptotics.IsEquivalent atTop
        (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight π p : ℝ) / p)
        (fun x : ℝ => α / C ^ (1 / α) *
          ((Nat.primeCounting ⌊x⌋₊ : ℝ) ^ (1 / α) / Real.log (Nat.primeCounting ⌊x⌋₊))) ∧
      (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight π p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x ^ (1 / α) / Real.log x ^ (1 + 1 / α))

/-- **Average order of the canonical sequential realization.** Let $(\pi_k)_{k \ge 1}$ be a
sequence of nonnegative integers with partial sums $\Pi_k = \sum_{1 \le j \le k} \pi_j$, let
$H_{\mathrm{seq}}$ be its canonical sequential realization, and suppose that $C > 0$ and
$\alpha > 0$ are real numbers with $\Pi_k \sim C k^\alpha$ as $k \to \infty$. Then, as
$x \to \infty$ over the reals, each of the three functions
$x \sum_{p \le x} H_{\mathrm{seq}}(p)/p$, $\sum_{p \le x} H_{\mathrm{seq}}(p) \log x / \log p$
(both sums over primes $p \le x$) and $\sum_{1 \le n \le x} H_{\mathrm{seq}}(n)$ is
$\Theta\bigl(x^{1+1/\alpha} / (\log x)^{1+1/\alpha}\bigr)$, where $f = \Theta(g)$ means
$f = O(g)$ and $g = O(f)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 2 (`integers-2026-A116-cor-2`),
statement read from the journal PDF (the corpus record carries the prose of Section 7.6 that
follows it). -/
public theorem_wanted canonicalSeq_averageOrder {π : ℕ → ℕ} {C α : ℝ} (hC : 0 < C)
    (hα : 0 < α)
    (hcum : Asymptotics.IsEquivalent atTop (fun k : ℕ => (profilePartialSum π k : ℝ))
      (fun k : ℕ => C * (k : ℝ) ^ α)) :
    (fun x : ℝ => x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        (canonicalSeqHeight π p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x ^ (1 + 1 / α) / Real.log x ^ (1 + 1 / α)) ∧
      (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        (canonicalSeqHeight π p : ℝ) * (Real.log x / Real.log p)) =Θ[atTop]
        (fun x : ℝ => x ^ (1 + 1 / α) / Real.log x ^ (1 + 1 / α)) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight π n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x ^ (1 + 1 / α) / Real.log x ^ (1 + 1 / α))

/-- **Growth for the ordinary partition profile.** Let $H_{\mathrm{seq}}$ be the canonical
sequential realization of the constant profile $\pi_k = 1$ for all $k \ge 1$ (so
$H_{\mathrm{seq}}(p_i) = i$ for the $i$-th prime $p_i$). Then, as $x \to \infty$ over the reals,
$\sum_{p \le x} H_{\mathrm{seq}}(p)/p = \Theta\bigl(x / (\log x)^2\bigr)$, the sum running over
primes $p \le x$, and
$\sum_{1 \le n \le x} H_{\mathrm{seq}}(n) = \Theta\bigl(x^2 / (\log x)^2\bigr)$, where
$f = \Theta(g)$ means $f = O(g)$ and $g = O(f)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 3 (`integers-2026-A116-cor-3`). -/
public theorem_wanted canonicalSeq_partitionProfile_growth :
    (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        (canonicalSeqHeight (fun _ => 1) p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x / Real.log x ^ 2) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight (fun _ => 1) n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x ^ 2 / Real.log x ^ 2)

/-- **Growth for the plane partition profile.** Let $H_{\mathrm{seq}}$ be the canonical
sequential realization of the profile $\pi_k = k$ for $k \ge 1$, let
$S(x) = \sum_{p \le x} H_{\mathrm{seq}}(p)/p$ (the sum over primes $p \le x$) and
$F(x) = \sum_{1 \le n \le x} H_{\mathrm{seq}}(n)$, and let $m(x)$ be the number of primes
$p \le x$. Then, as $x \to \infty$ over the reals,
$S(x) \sim 2\sqrt{2}\, \sqrt{m(x)} / \log m(x)$,
$S(x) = \Theta\bigl(x^{1/2} / (\log x)^{3/2}\bigr)$, $F(x) = \Theta\bigl(x\, S(x)\bigr)$ and
$F(x) = \Theta\bigl(x^{3/2} / (\log x)^{3/2}\bigr)$, where $f = \Theta(g)$ means $f = O(g)$ and
$g = O(f)$.

Here the partial sums are $k(k+1)/2 \sim k^2/2$, so this is the case $\alpha = 2$, $C = 1/2$ of
the general growth laws.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 4 (`integers-2026-A116-cor-4`). -/
public theorem_wanted canonicalSeq_planePartitionProfile_growth :
    Asymptotics.IsEquivalent atTop
        (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight (fun k => k) p : ℝ) / p)
        (fun x : ℝ => 2 * Real.sqrt 2 *
          (Real.sqrt (Nat.primeCounting ⌊x⌋₊) / Real.log (Nat.primeCounting ⌊x⌋₊))) ∧
      (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight (fun k => k) p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x ^ (1 / 2 : ℝ) / Real.log x ^ (3 / 2 : ℝ)) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight (fun k => k) n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight (fun k => k) p : ℝ) / p) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight (fun k => k) n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x ^ (3 / 2 : ℝ) / Real.log x ^ (3 / 2 : ℝ))

end

end MetaMathlibExt
