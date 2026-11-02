/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli

namespace MetaMathlibExt

open Filter Finset Topology

@[expose] public section

/-- **The $q$-analogue of a real number.** For real numbers $q$ and $x$, the $q$-analogue of $x$
is
$$[x]_q = \frac{q^x - 1}{q - 1},$$
where $q^x$ is the real power; we write $[x]$ when $q$ is fixed. When $q = 1$ the denominator is
$0$ and the quotient is taken to be $0$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 1. -/
public noncomputable def qBracket (q x : ℝ) : ℝ :=
  (q ^ x - 1) / (q - 1)

/-- **Carlitz-type sequences.** For real $q$, a sequence of functions
$T_n : \mathbb{R} \to \mathbb{R}$, $n \ge 0$, is Carlitz-type with associated real sequence
$(a_k)_{k \ge 0}$ if for every natural number $n$ and every real $x$,
$T_n(x) = (q - 1)^{-n} \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} a_k q^{kx}$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Definition in
Section 2.1. -/
public def IsCarlitzTypeWith (q : ℝ) (T : ℕ → ℝ → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ n x, T n x = ((q - 1) ^ n)⁻¹ *
    ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * a k * q ^ ((k : ℝ) * x)

/-- **Carlitz $q$-polynomials $\eta_n$.** For real $q$, write $[y] = (q^y - 1)/(q - 1)$ and let
$a_0 = 1$ and $a_k = k/[k]$ for $k \ge 1$. For natural $n$ and real $x$, Carlitz's $q$-polynomial
is $\eta_n(x) = (q - 1)^{-n} \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} a_k q^{kx}$; that is,
$(\eta_n)$ is the Carlitz-type sequence with associated sequence $(a_k)$. Its values at $0$ are
written $\eta_n = \eta_n(0)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1
(examples after Theorem 2.1); after L. Carlitz (1948). -/
public noncomputable def carlitzEtaPoly (q : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((q - 1) ^ n)⁻¹ * ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) *
    (if k = 0 then 1 else (k : ℝ) / qBracket q k) * q ^ ((k : ℝ) * x)

/-- **Carlitz $q$-Bernoulli polynomials.** For real $q$, write $[y] = (q^y - 1)/(q - 1)$. For
natural $n$ and real $x$, Carlitz's $q$-Bernoulli polynomial is
$\beta_n(x) = (q - 1)^{-n} \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} \frac{k + 1}{[k + 1]} q^{kx}$;
that is, $(\beta_n)$ is the Carlitz-type sequence with associated sequence
$a_k = (k + 1)/[k + 1]$. The Carlitz $q$-Bernoulli numbers are $\beta_n = \beta_n(0)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1
(examples after Theorem 2.1); after L. Carlitz (1948). -/
public noncomputable def carlitzBetaPoly (q : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((q - 1) ^ n)⁻¹ * ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) *
    (((k : ℝ) + 1) / qBracket q ((k : ℝ) + 1)) * q ^ ((k : ℝ) * x)

/-- **The $q$-analogue of $0$ is $0$.** For every real number $q$, $[0]_q = 0$, where
$[x]_q = (q^x - 1)/(q - 1)$ is the $q$-analogue of a real number $x$, taken to be $0$ when
$q = 1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 1. -/
public theorem qBracket_zero (q : ℝ) : qBracket q 0 = 0 := by
  simp [qBracket]

/-- **The $q$-number of $1$.** For real $q \ne 1$, the $q$-analogue $[x] = (q^x - 1)/(q - 1)$
satisfies $[1] = 1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 1. -/
public theorem qBracket_one {q : ℝ} (hq : q ≠ 1) : qBracket q 1 = 1 := by
  rw [qBracket, Real.rpow_one, div_self (sub_ne_zero.mpr hq)]

/-- **The zeroth term of a Carlitz-type sequence.** Let $q$ be a real number. If $(T_n)$ is a
Carlitz-type $q$-polynomial sequence with associated real sequence $(a_k)$, then $T_0(x) = a_0$
for every real $x$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Definition in
Section 2.1. -/
public theorem IsCarlitzTypeWith.apply_zero {q : ℝ} {T : ℕ → ℝ → ℝ} {a : ℕ → ℝ}
    (h : IsCarlitzTypeWith q T a) (x : ℝ) : T 0 x = a 0 := by
  simp [h 0 x]

/-- **The zeroth Carlitz $q$-polynomial.** For all real $q$ and $x$, Carlitz's $q$-polynomial
$\eta_0(x)$ equals $1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1. -/
public theorem carlitzEtaPoly_zero (q x : ℝ) : carlitzEtaPoly q 0 x = 1 := by
  simp [carlitzEtaPoly]

/-- **Carlitz's initial value $\eta_1 = 0$.** For real $q \ne 1$, the value $\eta_1 = \eta_1(0)$ of
Carlitz's $q$-polynomial $\eta_1$ at $0$ equals $0$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Sections 1
and 2.1. -/
public theorem carlitzEtaPoly_one_zero {q : ℝ} (hq : q ≠ 1) : carlitzEtaPoly q 1 0 = 0 := by
  simp [carlitzEtaPoly, Finset.sum_range_succ, qBracket_one hq]

/-- **The zeroth Carlitz $q$-Bernoulli polynomial.** For real $q \ne 1$ and every real $x$, the
Carlitz $q$-Bernoulli polynomial $\beta_0(x)$ equals $1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1. -/
public theorem carlitzBetaPoly_zero {q : ℝ} (hq : q ≠ 1) (x : ℝ) : carlitzBetaPoly q 0 x = 1 := by
  simp [carlitzBetaPoly, qBracket_one hq]

/-- **Characterization of Carlitz-type sequences.** Let $q > 0$ with $q \ne 1$ be real and write
$[x] = (q^x - 1)/(q - 1)$. A sequence of functions $T_n : \mathbb{R} \to \mathbb{R}$ is
Carlitz-type with some associated real sequence $(a_k)$ if and only if for every natural $n$ and
every real $x$, $T_n(x) = \sum_{k=0}^{n} \binom{n}{k} T_k(0) q^{kx} [x]^{n-k}$.

This is a $q$-analogue of the characterization of Appell sequences.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.1
(`integers-2026-A85-thm-2-1`). -/
public theorem_wanted isCarlitzType_iff_sum_choose (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (T : ℕ → ℝ → ℝ) :
    (∃ a, IsCarlitzTypeWith q T a) ↔
      ∀ n x, T n x = ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * T k 0 * q ^ ((k : ℝ) * x) * qBracket q x ^ (n - k)

/-- **Binomial inversion.** For real sequences $(u_n)$ and $(v_n)$, the identities
$u_n = \sum_{k=0}^{n} \binom{n}{k} v_k$ hold for all natural numbers $n$ if and only if the
identities $v_n = \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} u_k$ hold for all natural numbers $n$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Lemma 2.2
(`integers-2026-A85-lem-2-2`). -/
public theorem_wanted binomial_inversion_iff (u v : ℕ → ℝ) :
    (∀ n, u n = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * v k) ↔
      ∀ n, v n = ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * u k

/-- **Sums of $q^{rk} [k]^n$ via Carlitz-type sequences.** Let $q > 0$ with $q \ne 1$, let
$[x] = (q^x - 1)/(q - 1)$, and let $r \ge 1$ be a natural number. Let $S_m(x)$
($m \in \mathbb{N}$, $x \in \mathbb{R}$) be the Carlitz-type sequence with associated sequence
$a_k = 1/((q - 1)[k + r])$, that is,
$$S_m(x) = (q - 1)^{-m} \sum_{k=0}^{m} (-1)^{m-k} \binom{m}{k} a_k q^{kx}$$
for all $m$ and all real $x$. Then for all natural numbers $n$ and $N$,
$$\sum_{k=0}^{N-1} q^{rk} [k]^n = q^{rN} S_n(N) - S_n(0),$$
where $0^0 = 1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.3
(`integers-2026-A85-thm-2-3`). -/
public theorem_wanted sum_qpow_mul_qBracket_pow (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r n N : ℕ) (hr : 0 < r) (S : ℕ → ℝ → ℝ)
    (hS : IsCarlitzTypeWith q S fun k => 1 / ((q - 1) * qBracket q ((k + r : ℕ) : ℝ))) :
    ∑ k ∈ range N, q ^ (r * k) * qBracket q k ^ n = q ^ (r * N) * S n N - S n 0

/-- **Sums of $q^{rk} [k]^{n-d}$ via Carlitz-type sequences.** Let $q > 0$ with $q \ne 1$, let
$[x] = (q^x - 1)/(q - 1)$, and let $r$, $d$ and $n$ be natural numbers with $r \ge 1$, $d \le r$
and $d \le n$. Write $(k)_d = k(k-1)\cdots(k-d+1)$ for the falling factorial (with $(k)_0 = 1$).
Let $T_m(x)$ ($m \in \mathbb{N}$, $x \in \mathbb{R}$) be the Carlitz-type sequence with associated
sequence $a_k = (q - 1)^{d-1} (k)_d / [k + r - d]$, that is,
$$T_m(x) = (q - 1)^{-m} \sum_{k=0}^{m} (-1)^{m-k} \binom{m}{k} a_k q^{kx}$$
for all $m$ and all real $x$. Then for every natural number $N$,
$$\sum_{k=0}^{N-1} q^{rk} [k]^{n-d} = \frac{q^{(r-d)N} T_n(N) - T_n(0)}{(n)_d},$$
where $0^0 = 1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.4
(`integers-2026-A85-thm-2-4`). -/
public theorem_wanted sum_qpow_mul_qBracket_pow_sub (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r d n N : ℕ) (hr : 0 < r) (hdr : d ≤ r) (hdn : d ≤ n) (T : ℕ → ℝ → ℝ)
    (hT : IsCarlitzTypeWith q T fun k =>
      (q - 1) ^ ((d : ℤ) - 1) * (k.descFactorial d : ℝ) / qBracket q ((k + r - d : ℕ) : ℝ)) :
    ∑ k ∈ range N, q ^ (r * k) * qBracket q k ^ (n - d) =
      (q ^ ((r - d) * N) * T n N - T n 0) / (n.descFactorial d : ℝ)

/-- **Symbolic recurrence for Carlitz-type sequences.** Let $q > 0$ with $q \ne 1$, write
$[x] = (q^x - 1)/(q - 1)$, let $r$ be a natural number, let $P$ be a real polynomial and let
$(a_k)$ be a real sequence with $[k + r]\, a_k = P(k)$ for every natural number $k$. If $(T_n)$ is
a Carlitz-type sequence with associated sequence $(a_k)$ and $t_n = T_n(0)$, then for every natural
number $n$ greater than the degree of $P$ (taken to be $0$ when $P = 0$),
$q^r \sum_{j=0}^{n} \binom{n}{j} q^j t_j = t_n$, which in umbral notation reads
$q^r (q t + 1)^n = t^n$.

The hypothesis $[k + r]\, a_k = P(k)$ encodes $a_k = P(k)/[k + r]$; for $r = 0$ it forces
$P(0) = 0$ and leaves $a_0$ free.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.5
(`integers-2026-A85-thm-2-5`). -/
public theorem_wanted carlitzType_symbolic_recurrence (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r : ℕ) (P : Polynomial ℝ) (a : ℕ → ℝ)
    (ha : ∀ k : ℕ, qBracket q ((k + r : ℕ) : ℝ) * a k = P.eval (k : ℝ))
    (T : ℕ → ℝ → ℝ) (hT : IsCarlitzTypeWith q T a) (n : ℕ) (hn : P.natDegree < n) :
    q ^ r * ∑ j ∈ range (n + 1), (n.choose j : ℝ) * q ^ j * T j 0 = T n 0

/-- **Closure properties of Carlitz-type sequences.** Let $q > 0$ with $q \ne 1$ be real, and let
$(T_n)$ be a Carlitz-type sequence of functions $\mathbb{R} \to \mathbb{R}$ with associated real
sequence $(a_k)$. Then:
(i) $n q^x T_{n-1}(x)$ is Carlitz-type with associated sequence $(q - 1) k a_{k-1}$;
(ii) if $a_0 = 0$, then $q^{-x} T_{n+1}(x)/(n + 1)$ is Carlitz-type with associated sequence
$a_{k+1}/((q - 1)(k + 1))$;
(iii) $q^{-x} (T_n(x) + (q - 1) T_{n+1}(x))$ is Carlitz-type with associated sequence $a_{k+1}$;
(iv) $n (T_{n-1}(x) + (q - 1) T_n(x))$ is Carlitz-type with associated sequence $(q - 1) k a_k$.
At $n = 0$ the functions in (i) and (iv) are $0$, and at $k = 0$ the associated sequence in (i)
is $0$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.6
(`integers-2026-A85-prop-2-6`). -/
public theorem_wanted isCarlitzTypeWith_closure (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (T : ℕ → ℝ → ℝ) (a : ℕ → ℝ) (hT : IsCarlitzTypeWith q T a) :
    IsCarlitzTypeWith q (fun n x => q ^ x * n * T (n - 1) x)
        (fun k => (q - 1) * k * a (k - 1)) ∧
      (a 0 = 0 → IsCarlitzTypeWith q (fun n x => q ^ (-x) * T (n + 1) x / (n + 1))
        (fun k => a (k + 1) / ((q - 1) * (k + 1)))) ∧
      IsCarlitzTypeWith q (fun n x => q ^ (-x) * (T n x + (q - 1) * T (n + 1) x))
        (fun k => a (k + 1)) ∧
      IsCarlitzTypeWith q (fun n x => n * (T (n - 1) x + (q - 1) * T n x))
        (fun k => (q - 1) * k * a k)

/-- **Sums of $q^k [k]^{n-1}$ via Carlitz's $q$-polynomials $\eta_n$.** Let $q > 0$ with $q \ne 1$,
let $[x] = (q^x - 1)/(q - 1)$, and let $\eta_n(x)$ be Carlitz's $q$-polynomials, with
$\eta_n = \eta_n(0)$. Then for every natural number $n \ge 1$ and every natural number $N$,
$$\sum_{k=0}^{N-1} q^k [k]^{n-1} = \frac{\eta_n(N) - \eta_n}{n},$$
where $0^0 = 1$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.7
(`integers-2026-A85-cor-2-7`). -/
public theorem_wanted sum_qpow_mul_qBracket_pow_eq_carlitzEta (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) (n N : ℕ) (hn : 0 < n) :
    ∑ k ∈ range N, q ^ k * qBracket q k ^ (n - 1) =
      (carlitzEtaPoly q n N - carlitzEtaPoly q n 0) / n

/-- **Weighted $q$-power sums via Carlitz's $q$-Bernoulli polynomials.** Let $q > 0$ with
$q \ne 1$, let $[x] = (q^x - 1)/(q - 1)$, and let $\beta_n(x)$ be Carlitz's $q$-Bernoulli
polynomials, with $\beta_n = \beta_n(0)$. Then for all natural numbers $n$ and $N$,
$$n \sum_{k=0}^{N-1} q^{2k} [k]^{n-1} + (q - 1) \sum_{k=0}^{N-1} q^k [k]^n =
q^N \beta_n(N) - \beta_n,$$
where $0^0 = 1$, and the first term is $0$ when $n = 0$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.8
(`integers-2026-A85-cor-2-8`). -/
public theorem_wanted sum_qpow_mul_qBracket_pow_eq_carlitzBeta (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) (n N : ℕ) :
    n * ∑ k ∈ range N, q ^ (2 * k) * qBracket q k ^ (n - 1) +
        (q - 1) * ∑ k ∈ range N, q ^ k * qBracket q k ^ n =
      q ^ N * carlitzBetaPoly q n N - carlitzBetaPoly q n 0

/-- **Extended Carlitz $q$-Bernoulli polynomials.** For real $q$, the extended Carlitz
$q$-Bernoulli polynomials $\beta_n^{(r)}(x)$, indexed by natural numbers $r$ and $n$ and evaluated
at real $x$, are defined by recursion on $r$: $\beta_n^{(0)}(x) = \eta_n(x)$ is Carlitz's
$q$-polynomial, and
$\beta_n^{(r+1)}(x) = q^{-x} \bigl(\beta_n^{(r)}(x) + (q - 1) \beta_{n+1}^{(r)}(x)\bigr)$.
The extended Carlitz $q$-Bernoulli numbers are $\beta_n^{(r)} = \beta_n^{(r)}(0)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.2
(definition of the extended family). -/
public noncomputable def extendedCarlitzBetaPoly (q : ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, n, x => carlitzEtaPoly q n x
  | r + 1, n, x => q ^ (-x) *
      (extendedCarlitzBetaPoly q r n x + (q - 1) * extendedCarlitzBetaPoly q r (n + 1) x)

/-- **Extended Carlitz $q$-Bernoulli polynomials of order zero.** For every real $q$, natural number
$n$ and real $x$, the extended Carlitz $q$-Bernoulli polynomial $\beta_n^{(0)}(x)$ equals Carlitz's
$q$-polynomial $\eta_n(x)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.2. -/
public theorem extendedCarlitzBetaPoly_zero (q : ℝ) (n : ℕ) (x : ℝ) :
    extendedCarlitzBetaPoly q 0 n x = carlitzEtaPoly q n x := by
  simp [extendedCarlitzBetaPoly]

/-- **Recurrence for the extended Carlitz $q$-Bernoulli polynomials.** For every real $q$, natural
numbers $r$ and $n$, and real $x$, the extended Carlitz $q$-Bernoulli polynomials satisfy
$\beta_n^{(r+1)}(x) = q^{-x} \bigl(\beta_n^{(r)}(x) + (q - 1) \beta_{n+1}^{(r)}(x)\bigr)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.2. -/
public theorem extendedCarlitzBetaPoly_succ (q : ℝ) (r n : ℕ) (x : ℝ) :
    extendedCarlitzBetaPoly q (r + 1) n x = q ^ (-x) *
      (extendedCarlitzBetaPoly q r n x + (q - 1) * extendedCarlitzBetaPoly q r (n + 1) x) := by
  simp [extendedCarlitzBetaPoly]

/-- **Closed forms for the extended Carlitz $q$-Bernoulli polynomials.** Let $q > 0$ with
$q \ne 1$ be real, write $[x] = (q^x - 1)/(q - 1)$, let $r$ be a natural number, and let
$\beta_n^{(r)}(x)$ be the extended Carlitz $q$-Bernoulli polynomials. Put $a_k = (k + r)/[k + r]$
for natural $k$ with $k + r \ne 0$, and $a_0 = 1$ if $r = 0$. Then:
(i) for every natural $n$ and real $x$,
$\beta_n^{(r)}(x) = (q - 1)^{-n} \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} a_k q^{kx}$;
(ii) for every natural $n$ and real $x$,
$\beta_n^{(r)}(x) = \sum_{k=0}^{n} \binom{n}{k} \beta_k^{(r)}(0) q^{kx} [x]^{n-k}$;
(iii) for every natural $n \ge 2$,
$q^r \sum_{j=0}^{n} \binom{n}{j} q^j \beta_j^{(r)}(0) = \beta_n^{(r)}(0)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.9
(`integers-2026-A85-prop-2-9`). -/
public theorem_wanted extendedCarlitzBetaPoly_closed_forms (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r : ℕ) :
    (∀ n x, extendedCarlitzBetaPoly q r n x = ((q - 1) ^ n)⁻¹ *
        ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) *
          (if k + r = 0 then 1 else ((k + r : ℕ) : ℝ) / qBracket q ((k + r : ℕ) : ℝ)) *
            q ^ ((k : ℝ) * x)) ∧
      (∀ n x, extendedCarlitzBetaPoly q r n x = ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * extendedCarlitzBetaPoly q r k 0 * q ^ ((k : ℝ) * x) *
          qBracket q x ^ (n - k)) ∧
      ∀ n, 2 ≤ n → q ^ r * ∑ j ∈ range (n + 1),
        (n.choose j : ℝ) * q ^ j * extendedCarlitzBetaPoly q r j 0 =
          extendedCarlitzBetaPoly q r n 0

/-- **Weighted $q$-power sums via the extended Carlitz $q$-Bernoulli polynomials.** Let $q > 0$
with $q \ne 1$, let $[x] = (q^x - 1)/(q - 1)$, and let $\beta_n^{(r)}(x)$ be the extended Carlitz
$q$-Bernoulli polynomials, with $\beta_n^{(r)} = \beta_n^{(r)}(0)$. Then for all natural numbers
$r$, $n$ and $N$,
$$n \sum_{k=0}^{N-1} q^{(r+1)k} [k]^{n-1} + (q - 1) r \sum_{k=0}^{N-1} q^{rk} [k]^n =
q^{rN} \beta_n^{(r)}(N) - \beta_n^{(r)},$$
where $0^0 = 1$, and the first term is $0$ when $n = 0$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.10
(`integers-2026-A85-thm-2-10`). -/
public theorem_wanted sum_qpow_mul_qBracket_pow_eq_extendedCarlitzBeta (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) (r n N : ℕ) :
    n * ∑ k ∈ range N, q ^ ((r + 1) * k) * qBracket q k ^ (n - 1) +
        (q - 1) * r * ∑ k ∈ range N, q ^ (r * k) * qBracket q k ^ n =
      q ^ (r * N) * extendedCarlitzBetaPoly q r n N - extendedCarlitzBetaPoly q r n 0

/-- **Series for the extended Carlitz $q$-Bernoulli numbers.** Let $0 < q < 1$, write
$[x] = (q^x - 1)/(q - 1)$, and let $\beta_n^{(r)} = \beta_n^{(r)}(0)$ be the extended Carlitz
$q$-Bernoulli numbers. For every natural number $n \ge 1$,
$\beta_n^{(0)} = -n \sum_{k=0}^{\infty} q^k [k]^{n-1} + (1 - q)^{-n}$, and for every natural number
$r \ge 1$,
$$
\beta_n^{(r)} = -n \sum_{k=0}^{\infty} q^{(r+1)k} [k]^{n-1} +
r (1 - q) \sum_{k=0}^{\infty} q^{rk} [k]^n.
$$

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.11
(`integers-2026-A85-thm-2-11`). -/
public theorem_wanted extendedCarlitzBeta_eq_tsum (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (r n : ℕ) (hn : 0 < n) :
    extendedCarlitzBetaPoly q r n 0 =
      if r = 0 then -n * ∑' k : ℕ, q ^ k * qBracket q k ^ (n - 1) + ((1 - q) ^ n)⁻¹
      else -n * ∑' k : ℕ, q ^ ((r + 1) * k) * qBracket q k ^ (n - 1) +
        r * (1 - q) * ∑' k : ℕ, q ^ (r * k) * qBracket q k ^ n

/-- **Bernoulli numbers as a limit as $q \to 1^-$.** Let $r \ge 1$ and $n \ge 1$ be integers and,
for real $q$ and $x$, write $[x] = (q^x - 1)/(q - 1)$. Then, as $q$ tends to $1$ from below,
$$\sum_{k=0}^{\infty} \left(r q^{rk} - (n + r) q^{(r+1)k}\right) [k]^{n-1} \to B_n,$$
where $B_n$ is the $n$-th Bernoulli number, with the convention $B_1 = -1/2$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.12
(`integers-2026-A85-cor-2-12`). -/
public theorem_wanted tendsto_tsum_qBracket_bernoulli (r n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    Tendsto (fun q : ℝ => ∑' k : ℕ,
        ((r : ℝ) * q ^ (r * k) - ((n : ℝ) + r) * q ^ ((r + 1) * k)) * qBracket q k ^ (n - 1))
      (𝓝[<] 1) (𝓝 (bernoulli n : ℝ))

/-- **Sums of $q^{ir}$ times $q$-falling factorials.** Let $q > 0$ with $q \ne 1$, let
$[x] = (q^x - 1)/(q - 1)$, and write $[x]_m = [x][x-1]\cdots[x-m+1]$ for the $q$-falling factorial
(with $[x]_0 = 1$). Then for all natural numbers $r \ge 1$, $k$ and $N$,
$$\sum_{i=0}^{N-1} q^{ir} [i]_k = \left(\sum_{\ell=0}^{r-1}
\frac{q^{(r-\ell-1)N + (\ell+1)k} \, [r-1]_\ell}{[k+r]_{\ell+1}}\right) [N]_{k+1}.$$

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.14
(`integers-2026-A85-prop-2-14`). -/
public theorem_wanted sum_qpow_mul_qFalling (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1) (r k N : ℕ)
    (hr : 0 < r) :
    ∑ i ∈ range N, q ^ (i * r) * ∏ j ∈ range k, qBracket q ((i : ℝ) - j) =
      (∑ l ∈ range r, q ^ ((r - l - 1) * N + (l + 1) * k) *
          (∏ j ∈ range l, qBracket q ((r : ℝ) - 1 - j)) /
            ∏ j ∈ range (l + 1), qBracket q (((k + r : ℕ) : ℝ) - j)) *
        ∏ j ∈ range (k + 1), qBracket q ((N : ℝ) - j)

/-- **Limit of the $q$-power-sum interpolant at $0$: first closed form.** Let $q > 0$ with
$q \ne 1$, let $r \ge 1$ and $k \ge 0$ be integers, and for real $x$ write
$[x] = (q^x - 1)/(q - 1)$, $[x]_m = [x][x-1]\cdots[x-m+1]$ (with $[x]_0 = 1$) and
$[k]! = [1][2]\cdots[k]$. Let $P$ be a real polynomial such that
$P(q^N) = q^{k(k-1)/2} \sum_{i=0}^{N-1} q^{ir} [i]_k$ for every positive integer $N$. Then
$P(q^x)/[x]$ tends, as $x \to 0$ with $x \ne 0$, to
$$(-1)^k [k]! \sum_{i=0}^{r-1} \frac{q^{ik} [r-1]_i}{[k+r]_{i+1}}.$$

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.15
(`integers-2026-A85-cor-2-15`). -/
public theorem_wanted tendsto_qInterpolant_div_qBracket (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r k : ℕ) (hr : 0 < r) (P : Polynomial ℝ)
    (hP : ∀ N : ℕ, 0 < N → P.eval (q ^ N) = q ^ (k * (k - 1) / 2) *
      ∑ i ∈ range N, q ^ (i * r) * ∏ j ∈ range k, qBracket q ((i : ℝ) - j)) :
    Tendsto (fun x : ℝ => P.eval (q ^ x) / qBracket q x) (𝓝[≠] 0)
      (𝓝 ((-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) *
        ∑ i ∈ range r, q ^ (i * k) * (∏ j ∈ range i, qBracket q ((r : ℝ) - 1 - j)) /
          ∏ j ∈ range (i + 1), qBracket q (((k + r : ℕ) : ℝ) - j)))

/-- **Partial fraction decomposition of $q^{kx}$ over a $q$-falling factorial.** Let $q > 0$ with
$q \ne 1$, let $[x] = (q^x - 1)/(q - 1)$, write $[m]! = [1][2]\cdots[m]$ (with $[0]! = 1$) and
$\binom{k}{i}_q = [k]!/([i]!\,[k-i]!)$. Then for every natural number $k$ and every real number
$x \notin \{0, 1, \dots, k\}$,
$$\frac{q^{kx}}{[x][x-1]\cdots[x-k]} = \frac{1}{[k]!} \sum_{i=0}^{k} (-1)^{k-i} \binom{k}{i}_q
\frac{q^{(k^2+k)/2 + (i^2-i)/2}}{[x-i]}.$$

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.16
(`integers-2026-A85-prop-2-16`). -/
public theorem_wanted qpow_div_qFalling_partial_fractions (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (k : ℕ) (x : ℝ) (hx : ∀ i : ℕ, i ≤ k → x ≠ i) :
    q ^ ((k : ℝ) * x) / ∏ j ∈ range (k + 1), qBracket q (x - j) =
      (∏ j ∈ range k, qBracket q ((j : ℝ) + 1))⁻¹ * ∑ i ∈ range (k + 1),
        (-1 : ℝ) ^ (k - i) *
          ((∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) /
            ((∏ j ∈ range i, qBracket q ((j : ℝ) + 1)) *
              ∏ j ∈ range (k - i), qBracket q ((j : ℝ) + 1))) *
          q ^ ((k ^ 2 + k) / 2 + (i ^ 2 - i) / 2) / qBracket q (x - i)

/-- **Second closed form of a limit of $q$-interpolated falling-factorial sums.** Let $q > 0$
with $q \ne 1$, let $[x] = (q^x - 1)/(q - 1)$, write $[x]_m = [x][x-1]\cdots[x-m+1]$ and
$[m]! = [1][2]\cdots[m]$ (both equal to $1$ when $m = 0$), and let $r \ge 1$ and $k$ be natural
numbers. Let $P$ be a real polynomial such that
$$P(q^N) = q^{k(k-1)/2} \sum_{i=0}^{N-1} q^{ir} [i]_k$$
for every integer $N \ge 1$. Then, as $x \to 0$ through real numbers $x \ne 0$, $P(q^x)/[x]$
tends to
$$g_r(q, k) = (-1)^k [k]! \, [r-1]! \, q^{1-r} \sum_{i=0}^{r-1}
\frac{(q-1)^i \, q^{i(i+1)/2 - i(r-1)}}{[r-1-i]! \, [k+i+1]}.$$

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.17
(`integers-2026-A85-prop-2-17`). -/
public theorem_wanted tendsto_qInterpolant_div_qBracket' (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r k : ℕ) (hr : 0 < r) (P : Polynomial ℝ)
    (hP : ∀ N : ℕ, 0 < N → P.eval (q ^ N) = q ^ (k * (k - 1) / 2) *
      ∑ i ∈ range N, q ^ (i * r) * ∏ j ∈ range k, qBracket q ((i : ℝ) - j)) :
    Tendsto (fun x : ℝ => P.eval (q ^ x) / qBracket q x) (𝓝[≠] 0)
      (𝓝 ((-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) *
        (∏ j ∈ range (r - 1), qBracket q ((j : ℝ) + 1)) * q ^ (1 - (r : ℝ)) *
        ∑ i ∈ range r, (q - 1) ^ i *
          q ^ (((i * (i + 1) / 2 : ℕ) : ℝ) - ((i * (r - 1) : ℕ) : ℝ)) /
            ((∏ j ∈ range (r - 1 - i), qBracket q ((j : ℝ) + 1)) *
              qBracket q ((k + i + 1 : ℕ) : ℝ))))


/-- **Extended Carlitz $q$-Bernoulli numbers via $q$-Stirling numbers.** Let $q > 0$ with
$q \ne 1$ be real, write $[x] = (q^x - 1)/(q - 1)$ for real $x$, $[x]_m = [x][x-1] \cdots [x-m+1]$
(with $[x]_0 = 1$) and $[m]! = [1][2] \cdots [m]$ (with $[0]! = 1$), and let $\beta_n^{(r)}(x)$
be the extended Carlitz $q$-Bernoulli polynomials, with numbers $\beta_n^{(r)} = \beta_n^{(r)}(0)$.
Let $r \ge 1$ and $n$ be natural numbers, and let $S(m, k)$ be real numbers such that
$[x]^m = \sum_{k=0}^{m} q^{k(k-1)/2} S(m, k) [x]_k$ for every natural number $m$ and every real
$x$ (the defining identity of Carlitz's $q$-Stirling numbers of the second kind). For natural $k$
put $\varphi_r(q, k) = (-1)^k [k]! \sum_{i=0}^{r-1} q^{ik} [r-1]_i / [k+r]_{i+1}$. Then
$$\beta_n^{(r)} = \sum_{k=0}^{n} \varphi_r(q, k) S(n, k),$$
and for every natural number $k$,
$$
\varphi_r(q, k) = (-1)^k [k]! \, [r-1]! \, q^{1-r} \sum_{i=0}^{r-1}
\frac{(q-1)^i q^{i(i+1)/2 - i(r-1)}}{[r-1-i]! \, [k+i+1]}.
$$

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.13
(`integers-2026-A85-thm-2-13`). -/
public theorem_wanted extendedCarlitzBeta_eq_sum_qStirling (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r n : ℕ) (hr : 0 < r) (S : ℕ → ℕ → ℝ)
    (hS : ∀ (m : ℕ) (x : ℝ), qBracket q x ^ m = ∑ k ∈ range (m + 1),
      q ^ (k * (k - 1) / 2) * S m k * ∏ j ∈ range k, qBracket q (x - j)) :
    extendedCarlitzBetaPoly q r n 0 = ∑ k ∈ range (n + 1),
        (-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) *
          (∑ i ∈ range r, q ^ (i * k) * (∏ j ∈ range i, qBracket q ((r : ℝ) - 1 - j)) /
            ∏ j ∈ range (i + 1), qBracket q (((k + r : ℕ) : ℝ) - j)) * S n k ∧
      ∀ k : ℕ, (-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) *
          (∑ i ∈ range r, q ^ (i * k) * (∏ j ∈ range i, qBracket q ((r : ℝ) - 1 - j)) /
            ∏ j ∈ range (i + 1), qBracket q (((k + r : ℕ) : ℝ) - j)) =
        (-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) *
          (∏ j ∈ range (r - 1), qBracket q ((j : ℝ) + 1)) * q ^ (1 - (r : ℝ)) *
          ∑ i ∈ range r, (q - 1) ^ i *
            q ^ (((i * (i + 1) / 2 : ℕ) : ℝ) - ((i * (r - 1) : ℕ) : ℝ)) /
              ((∏ j ∈ range (r - 1 - i), qBracket q ((j : ℝ) + 1)) *
                qBracket q ((k + i + 1 : ℕ) : ℝ))

/-- **Carlitz $q$-Bernoulli numbers via $q$-Stirling numbers.** Let $q > 0$ with $q \ne 1$, write
$[x] = (q^x - 1)/(q - 1)$, $[x]_k = [x][x - 1] \cdots [x - k + 1]$ and $[k]! = [1][2] \cdots [k]$
(empty products are $1$), and let $\beta_n = \beta_n(0)$ be Carlitz's $q$-Bernoulli numbers. If
real numbers $S_q(m,k)$ satisfy $[x]^m = \sum_{k=0}^{m} q^{k(k-1)/2} S_q(m,k) [x]_k$ for every
natural number $m$ and every real $x$ (this is the defining identity of Carlitz's $q$-Stirling
numbers of the second kind), then for every natural number $n$,
$\beta_n + q \beta_{n+1} = \sum_{k=0}^{n} (-1)^k \frac{[k]!}{[k+2]} S_q(n,k)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.18
(`integers-2026-A85-cor-2-18`). -/
public theorem_wanted carlitzBeta_add_mul_succ_eq_sum_qStirling (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) (n : ℕ) (S : ℕ → ℕ → ℝ)
    (hS : ∀ (m : ℕ) (x : ℝ), qBracket q x ^ m = ∑ k ∈ range (m + 1),
      q ^ (k * (k - 1) / 2) * S m k * ∏ j ∈ range k, qBracket q (x - j)) :
    carlitzBetaPoly q n 0 + q * carlitzBetaPoly q (n + 1) 0 = ∑ k ∈ range (n + 1),
      (-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) / qBracket q ((k : ℝ) + 2) * S n k

/-- **Sum of consecutive Bernoulli numbers via Stirling numbers.** For every natural number $n$,
$B_n + B_{n+1} = \sum_{k=0}^{n} (-1)^k \frac{k!}{k+2} S(n,k)$, where $B_n$ are the Bernoulli numbers
with $B_1 = -1/2$ (generating function $t/(e^t - 1)$, the paper's convention) and $S(n,k)$ are the
Stirling numbers of the second kind.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.19
(`integers-2026-A85-cor-2-19`). -/
public theorem_wanted bernoulli_add_bernoulli_succ_eq_sum_stirlingSecond (n : ℕ) :
    bernoulli n + bernoulli (n + 1) = ∑ k ∈ range (n + 1),
      (-1 : ℚ) ^ k * (k.factorial : ℚ) / ((k : ℚ) + 2) * (Nat.stirlingSecond n k : ℚ)

end

end MetaMathlibExt
