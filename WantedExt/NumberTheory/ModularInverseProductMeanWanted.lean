/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

namespace MetaMathlibExt

@[expose] public section

open Complex Finset

/-- **The modular product sum $S_k(n, m)$.** For natural numbers $k$, $n$ and $m$, the modular
product sum $S_k(n, m)$ is the natural number
$$S_k(n, m) = \sum a_1 a_2 \cdots a_k,$$
the sum running over all $k$-tuples $(a_1, \dots, a_k) \in \{1, \dots, n\}^k$ such that every
$a_j$ is coprime to $n$ and $a_1 a_2 \cdots a_k \equiv m \pmod n$. For $k = 2$ and $m = 1$ this is
the sum of the products $a \bar{a}$, where $a$ runs over the numbers in $\{1, \dots, n\}$ coprime
to $n$ and $\bar{a} \in \{1, \dots, n\}$ is the inverse of $a$ modulo $n$.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, equation (2). -/
public def modularProductSum (k n m : ℕ) : ℕ :=
  ∑ a ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 n) with
      (∀ j, Nat.Coprime (a j) n) ∧ (∏ j, a j) ≡ m [MOD n],
    ∏ j, a j

/-- **The modular product sum $S_2(3, 1)$.** The modular product sum satisfies $S_2(3, 1) = 5$:
the pairs $(a_1, a_2) \in \{1, 2, 3\}^2$ of numbers coprime to $3$ with $a_1 a_2 \equiv 1 \pmod 3$
are $(1, 1)$ and $(2, 2)$, and $1 \cdot 1 + 2 \cdot 2 = 5$.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, equation (2). -/
public theorem modularProductSum_two_three_one : modularProductSum 2 3 1 = 5 := by
  decide

/-- **The modular product sum $S_1(5, 3)$.** The modular product sum satisfies $S_1(5, 3) = 3$:
the only $a \in \{1, \dots, 5\}$ coprime to $5$ with $a \equiv 3 \pmod 5$ is $a = 3$.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, equation (2). -/
public theorem modularProductSum_one_five_three : modularProductSum 1 5 3 = 3 := by
  decide

/-- **Xu–Zhang constant.** For a natural number $q$, the Xu–Zhang constant $C_q$ is the product
over the prime factors $p$ of $q$, with $p^\alpha$ the exact power of $p$ dividing $q$,
$$C_q = \prod_{p^\alpha \parallel q} \left(1 + \frac{2p^3 + p^2 - 1}{(p^2 + 1)(p^2 + p + 1)} -
\frac{1}{p^{3(\alpha - 1)} (p^2 + p + 1)}\right).$$
For $q = 1$, and by convention for $q = 0$, there are no prime factors, so $C_0 = C_1 = 1$.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, equation (4), quoting Z. Xu and W. Zhang, *Fourth
power mean of character sums*, Acta Arith. 135 (2008), Lemma 9. -/
public noncomputable def xuZhangConstant (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors,
    (1 + (2 * (p : ℝ) ^ 3 + (p : ℝ) ^ 2 - 1) / (((p : ℝ) ^ 2 + 1) * ((p : ℝ) ^ 2 + p + 1)) -
      1 / ((p : ℝ) ^ (3 * (q.factorization p - 1)) * ((p : ℝ) ^ 2 + p + 1)))

/-- **Xu–Zhang constant at a prime.** For every prime $p$, the Xu–Zhang constant of $p$ is
$$C_p = 1 + \frac{2p^3 + p^2 - 1}{(p^2 + 1)(p^2 + p + 1)} - \frac{1}{p^2 + p + 1}.$$

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, equation (4). -/
public theorem xuZhangConstant_prime {p : ℕ} (hp : p.Prime) :
    xuZhangConstant p =
      1 + (2 * (p : ℝ) ^ 3 + (p : ℝ) ^ 2 - 1) / (((p : ℝ) ^ 2 + 1) * ((p : ℝ) ^ 2 + p + 1)) -
        1 / ((p : ℝ) ^ 2 + p + 1) := by
  simp [xuZhangConstant, hp.primeFactors, hp.factorization_self]

/-- **Explicit estimate for the modular product sum $S_k(n, m)$.** Let $\varphi$ be Euler's
totient function and $S_k(n, m)$ the modular product sum. For all natural numbers $k \ge 3$,
$n \ge 2$ and $m$ with $\gcd(m, n) = 1$,

$$\left| S_k(n, m) - \frac{n^k \varphi(n)^{k-1}}{2^k} \right| \le
(2\sqrt{3})^k \, n^{3k/2} (\log n)^k.$$

The paper also assumes $m \ge 1$, which follows from $\gcd(m, n) = 1$ and $n \ge 2$.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Theorem 1. -/
public theorem_wanted modularProductSum_explicit_estimate {k n m : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n)
    (hmn : Nat.Coprime m n) :
    |(modularProductSum k n m : ℝ) - (n : ℝ) ^ k * (n.totient : ℝ) ^ (k - 1) / 2 ^ k| ≤
      (2 * Real.sqrt 3) ^ k * (n : ℝ) ^ ((3 * k : ℝ) / 2) * Real.log n ^ k

/-- **Estimate for the modular product sum $S_k(n, m)$ at odd moduli.** Let $\varphi$ be Euler's
totient function and $S_k(n, m)$ the modular product sum. For every natural number $k \ge 4$
there is a real constant $C_k$ such that for every odd natural number $n \ge 3$ and every natural
number $m$ with $\gcd(m, n) = 1$,

$$\left| S_k(n, m) - \frac{n^k \varphi(n)^{k-1}}{2^k} \right| \le
C_k \, n^{3(k-2)/2} \varphi(n)^3 (\log n)^{k-4} (\log \log n)^2.$$

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Theorem 2. -/
public theorem_wanted modularProductSum_odd_estimate {k : ℕ} (hk : 4 ≤ k) :
    ∃ C : ℝ, ∀ n m : ℕ, 3 ≤ n → Odd n → Nat.Coprime m n →
      |(modularProductSum k n m : ℝ) - (n : ℝ) ^ k * (n.totient : ℝ) ^ (k - 1) / 2 ^ k| ≤
        C * (n : ℝ) ^ ((3 * ((k : ℝ) - 2)) / 2) * (n.totient : ℝ) ^ 3 *
          Real.log n ^ (k - 4) * Real.log (Real.log n) ^ 2

/-- **Explicit estimate for the modular product sum $S_2(n, m)$.** Let $\varphi$ be Euler's
totient function, $\tau(n)$ the number of divisors of $n$,
$\sigma_{1/2}(n) = \sum_{d \mid n} \sqrt{d}$ and $S_2(n, m)$ the modular product sum. For all
natural numbers $n \ge 2$ and $m$ with $\gcd(m, n) = 1$,

$$\left| S_2(n, m) - \frac{n^2 \varphi(n)}{4} \right| \le
n^2 \sigma_{1/2}(n) \bigl(\tau(n) \log(en)\bigr)^2 + \frac{n \varphi(n)}{4}.$$

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Theorem 3. -/
public theorem_wanted modularProductSum_two_explicit_estimate {n m : ℕ} (hn : 2 ≤ n)
    (hmn : Nat.Coprime m n) :
    |(modularProductSum 2 n m : ℝ) - (n : ℝ) ^ 2 * n.totient / 4| ≤
      (n : ℝ) ^ 2 * (∑ d ∈ n.divisors, Real.sqrt d) *
          ((n.divisors.card : ℝ) * Real.log (Real.exp 1 * n)) ^ 2 +
        n * n.totient / 4

/-- **Mean square of the error in the modular product sum $S_2(n, m)$.** Let $\varphi$ be Euler's
totient function, $S_2(n, m)$ the modular product sum and $C_n$ the Xu–Zhang constant of $n$.
For every real $\varepsilon > 0$ there is a real constant $C$ such that for every odd natural
number $n \ge 3$,

$$\left| \sum_{1 \le m \le n,\ \gcd(m, n) = 1}
\left( S_2(n, m) - \frac{n^2 \varphi(n)}{4} \right)^2 -
\frac{5 C_n}{144} \bigl(n \varphi(n)\bigr)^3 \right| \le C n^{5 + \varepsilon}.$$

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Theorem 4. -/
public theorem_wanted modularProductSum_two_mean_square {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → Odd n →
      |(∑ m ∈ Icc 1 n with Nat.Coprime m n,
            ((modularProductSum 2 n m : ℝ) - (n : ℝ) ^ 2 * n.totient / 4) ^ 2) -
          5 * xuZhangConstant n / 144 * ((n : ℝ) * n.totient) ^ 3| ≤
        C * (n : ℝ) ^ (5 + ε)

/-- **Large values of the error in the modular product sum $S_2(n, m)$.** Let $\varphi$ be Euler's
totient function and $S_2(n, m)$ the modular product sum. There are a real number $c > 0$ and a
natural number $N$ such that every odd natural number $n \ge N$ admits a natural number $m$ with
$1 \le m \le n$ and $\gcd(m, n) = 1$ for which

$$\left| S_2(n, m) - \frac{n^2 \varphi(n)}{4} \right| \ge c \, n^{3/2} \varphi(n).$$

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Theorem 4. -/
public theorem_wanted modularProductSum_two_error_large :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n →
      ∃ m ∈ Icc 1 n, Nat.Coprime m n ∧
        c * (n : ℝ) ^ ((3 : ℝ) / 2) * n.totient ≤
          |(modularProductSum 2 n m : ℝ) - (n : ℝ) ^ 2 * n.totient / 4|

open Classical in
/-- **Xu–Zhang twisted fourth moment of weighted character sums.** Let $\varphi$ be Euler's totient
function and $C_q$ the Xu–Zhang constant of $q$. For every natural number $\ell$ and every real
$\varepsilon > 0$ there is a real constant $C$ such that for every odd natural number $q \ge 3$,

$$\left| \sum_{\chi \bmod q,\ \chi(-1) = -1} \overline{\chi(2^\ell)}
\left| \sum_{a=1}^{q} a \, \chi(a) \right|^4 -
\frac{C_q (3\ell + 5) q^3 \varphi(q)^4}{72 \cdot 2^{\ell + 1}} \right| \le C q^{6 + \varepsilon},$$

where $\chi$ runs over the complex Dirichlet characters modulo $q$ with $\chi(-1) = -1$.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 1 (`integers-2024-A33-lem-1`, journal PDF
p. 4), quoting Z. Xu and W. Zhang, *Fourth power mean of character sums*, Acta Arith. 135
(2008), Lemma 9. -/
public theorem_wanted odd_character_twisted_weighted_sum_fourth_moment (ℓ : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ q : ℕ, 3 ≤ q → Odd q →
      ‖∑ χ : DirichletCharacter ℂ q with χ.Odd,
          starRingEnd ℂ (χ (2 ^ ℓ)) * (‖∑ a ∈ Icc 1 q, (a : ℂ) * χ a‖ ^ 4 : ℝ) -
        (xuZhangConstant q * (3 * ℓ + 5) * (q : ℝ) ^ 3 * (q.totient : ℝ) ^ 4 /
          (72 * 2 ^ (ℓ + 1)) : ℝ)‖ ≤ C * (q : ℝ) ^ (6 + ε)

open Classical in
/-- **Fourth moment of weighted odd character sums.** There is a real constant $C$ such that for
every odd integer $n \ge 3$,
$$\sum_{\chi \text{ odd}} \Bigl|\sum_{a=1}^{n} a\, \chi(a)\Bigr|^4 \le
C\, n^3 \varphi(n)^4 (\log\log n)^2,$$
where $\chi$ runs over the odd Dirichlet characters modulo $n$ (those with $\chi(-1) = -1$) and
$\varphi$ is Euler's totient function.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Corollary 1. -/
public theorem_wanted odd_character_weighted_sum_fourth_moment :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → Odd n →
      ∑ χ : DirichletCharacter ℂ n with χ.Odd, ‖∑ a ∈ Icc 1 n, (a : ℂ) * χ a‖ ^ 4 ≤
        C * (n : ℝ) ^ 3 * (n.totient : ℝ) ^ 4 * Real.log (Real.log n) ^ 2

/-- **Bound for a weighted Kloosterman-type sum.** Let $n \ge 1$ and $k \ge 1$ be integers and let
$m$ be a natural number coprime to $n$. Write $e_n(x) = e^{2\pi i x / n}$, and for $a$ coprime to
$n$ let $\bar a \in \{0, \dots, n - 1\}$ be the inverse of $a$ modulo $n$. Then
$$\Bigl|\sum_{1 \le a \le n,\ \gcd(a, n) = 1} a\, e_n(k m \bar a)\Bigr| \le
2 n^{3/2} \tau(n) \sqrt{\gcd(n, k)} \log(e n),$$
where $\tau(n)$ is the number of positive divisors of $n$.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 2. -/
public theorem_wanted weighted_kloosterman_sum_bound {n k m : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hmn : Nat.Coprime m n) :
    ‖∑ a ∈ Icc 1 n with Nat.Coprime a n,
        (a : ℂ) * exp (2 * Real.pi * I * (k * m * ((a : ZMod n)⁻¹).val : ℕ) / n)‖ ≤
      2 * (n : ℝ) ^ ((3 : ℝ) / 2) * n.divisors.card * Real.sqrt (Nat.gcd n k) *
        Real.log (Real.exp 1 * n)

/-- **Weighted sum of an additive character.** Let $q \ge 2$, let $k$ be a natural number not
divisible by $q$, and write $e_q(x) = e^{2\pi i x / q}$. Then
$$\sum_{b=1}^{q-1} b\, e_q(-kb) = -\frac{q}{1 - e_q(-k)}.$$

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 3. -/
public theorem_wanted sum_mul_additive_character {q k : ℕ} (hq : 2 ≤ q) (hk : ¬ q ∣ k) :
    ∑ b ∈ Icc 1 (q - 1), (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / q) =
      -q / (1 - exp (2 * Real.pi * I * (-(k : ℂ)) / q))

/-- **Weighted additive character sum over reduced residues.** For a positive integer $r$ and an
integer $x$ write $e_r(x) = \exp(2\pi i x / r)$, and let $\mu$ be the Möbius function. For all
natural numbers $n \ge 2$ and $k \ge 1$,

$$\sum_{1 \le b \le n,\ \gcd(b, n) = 1} b \, e_n(-kb)
= -n \sum_{d \mid n,\ (n/d) \nmid k} \frac{\mu(d)}{1 - e_{n/d}(-k)} +
\frac{n}{2} \sum_{d \mid n,\ d < n,\ (n/d) \mid k} \mu(d) \left(\frac{n}{d} - 1\right).$$

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 4. -/
public theorem_wanted coprime_sum_mul_additive_character {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ∑ b ∈ Icc 1 n with Nat.Coprime b n, (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / n) =
      -n * ∑ d ∈ n.divisors with ¬ (n / d) ∣ k,
          (ArithmeticFunction.moebius d : ℂ) /
            (1 - exp (2 * Real.pi * I * (-(k : ℂ)) / (n / d : ℕ))) +
        n / 2 * ∑ d ∈ n.divisors with d < n ∧ (n / d) ∣ k,
          (ArithmeticFunction.moebius d : ℂ) * ((n / d : ℕ) - 1)

/-- **Splitting a sum by greatest common divisor.** For every function
$f : \mathbb{N} \to \mathbb{C}$ and every natural number $n$,
$$\sum_{k=1}^{n} f(k) = \sum_{d \mid n} \sum_{1 \le h \le n/d,\ \gcd(n/d, h) = 1} f(hd).$$

Here $d$ runs over the positive divisors of $n$, and $0$ is taken to have none, so for $n = 0$
both sides are empty sums.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 5. -/
public theorem_wanted sum_Icc_eq_sum_divisors_coprime (f : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k =
      ∑ d ∈ n.divisors, ∑ h ∈ Icc 1 (n / d) with Nat.Coprime (n / d) h, f (h * d)

/-- **Sum of reciprocal distances from roots of unity to 1.** Let $q \ge 2$ and $\ell \ge 1$ be
integers, let $s \in \{1, -1\}$, and write $e_q(x) = e^{2\pi i x / q}$. Then
$$\sum_{0 \le a < q,\ q \nmid a\ell} \frac{1}{|1 - e_q(s a \ell)|} \le
\frac{q}{2} \log \frac{e q}{2 \gcd(\ell, q)} < \frac{q}{2} \log(e q).$$

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 6. -/
public theorem_wanted sum_inv_norm_one_sub_additive_character {q ℓ : ℕ} (hq : 2 ≤ q)
    (hℓ : 1 ≤ ℓ) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∑ a ∈ range q with ¬ q ∣ a * ℓ,
        1 / ‖1 - exp (2 * Real.pi * I * ((s * (a * ℓ : ℕ) : ℤ) : ℂ) / q)‖ ≤
      q / 2 * Real.log (Real.exp 1 * q / (2 * Nat.gcd ℓ q)) ∧
    q / 2 * Real.log (Real.exp 1 * q / (2 * Nat.gcd ℓ q)) < q / 2 * Real.log (Real.exp 1 * q)

/-- **Gcd-weighted sum of reciprocal distances from roots of unity to 1.** Let $n \ge 2$, let $d$
be a divisor of $n$, and write $e_m(x) = e^{2\pi i x / m}$. Then
$$\sum_{1 \le k \le n-1,\ (n/d) \nmid k} \frac{\sqrt{\gcd(n, k)}}{|1 - e_{n/d}(-k)|} \le
\frac{1}{2} \sqrt{n}\, \sigma_{1/2}(n) \log(e n),$$
where $\sigma_{1/2}(n) = \sum_{\delta \mid n} \sqrt{\delta}$.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 7. -/
public theorem_wanted sum_sqrt_gcd_div_norm_one_sub_additive_character {n d : ℕ} (hn : 2 ≤ n)
    (hd : d ∣ n) :
    ∑ k ∈ Icc 1 (n - 1) with ¬ (n / d) ∣ k,
        Real.sqrt (Nat.gcd n k) / ‖1 - exp (2 * Real.pi * I * (-(k : ℂ)) / (n / d : ℕ))‖ ≤
      1 / 2 * Real.sqrt n * (∑ δ ∈ n.divisors, Real.sqrt δ) * Real.log (Real.exp 1 * n)

end

end MetaMathlibExt
