/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MetaMathlibExt

@[expose] public section

open Filter Topology Asymptotics

/-- **Squarefree part.** For a natural number $n \ge 1$ with prime factorization
$n = \prod_p p^{e_p}$, its squarefree part is $u(n) = \prod_p p^{e_p \bmod 2}$, the product of the
primes dividing $n$ to an odd power. By convention $u(0) = 1$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2
(`n = u(n) v(n)²`, Theorems 2 and 3). -/
public def squareSplitU (n : ℕ) : ℕ :=
  n.factorization.prod fun p e => p ^ (e % 2)

/-- **The square-root part of a natural number.** For $n \ge 1$ with prime factorization
$n = \prod_p p^{e_p}$, the square-root part of $n$ is $v(n) = \prod_p p^{\lfloor e_p/2 \rfloor}$;
by convention $v(0) = 1$. For $n \ge 1$, $v(n)^2$ is the largest square dividing $n$, and
$n = u(n)\, v(n)^2$ where $u(n) = n / v(n)^2$ is squarefree.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2. -/
public def squareSplitV (n : ℕ) : ℕ :=
  n.factorization.prod fun p e => p ^ (e / 2)

/-- **Squarefree part of one.** We have $u(1) = 1$, where $u(n)$ is the product of the primes
dividing $n$ to an odd power.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2. -/
public theorem squareSplitU_one : squareSplitU 1 = 1 := by
  simp [squareSplitU]

/-- **The square-root part of $1$ is $1$.** We have $v(1) = 1$, where for $n \ge 1$ the
square-root part $v(n)$ is the product of $p^{\lfloor e/2 \rfloor}$ over the prime powers $p^e$
exactly dividing $n$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2. -/
public theorem squareSplitV_one : squareSplitV 1 = 1 := by
  simp [squareSplitV]

/-- **Square-splitting decomposition.** For every natural number $n \ne 0$ with prime
factorization $n = \prod_p p^{e_p}$, we have $n = u(n)\,v(n)^2$, where
$u(n) = \prod_p p^{e_p \bmod 2}$ and $v(n) = \prod_p p^{\lfloor e_p/2 \rfloor}$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2. -/
public theorem squareSplitU_mul_squareSplitV_sq {n : ℕ} (hn : n ≠ 0) :
    squareSplitU n * squareSplitV n ^ 2 = n := by
  unfold squareSplitU squareSplitV
  rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

/-- **Square-splitting divisors.** For a natural number $n \ge 1$ with prime factorization
$n = \prod_p p^{e_p}$, let $u(n) = \prod_p p^{e_p \bmod 2}$ and
$v(n) = \prod_p p^{\lfloor e_p/2 \rfloor}$, and let $u(0) = v(0) = 1$. The set of
square-splitting divisors of $n$ is $A(n) = \{u_1 v_1^2 : u_1 \mid u(n),\ v_1 \mid v(n)\}$, where
$u_1$ and $v_1$ range over the positive divisors of $u(n)$ and $v(n)$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 1. -/
public def squareSplitDivisors (n : ℕ) : Finset ℕ :=
  ((squareSplitU n).divisors ×ˢ (squareSplitV n).divisors).image fun x => x.1 * x.2 ^ 2

/-- **The square-splitting divisor set of $1$.** Let
$A(n) = \{u_1 v_1^2 : u_1 \mid u(n),\ v_1 \mid v(n)\}$ be the square-splitting divisor set of
$n \ge 1$, where $u(n)$ is the squarefree part of $n$ and $v(n)$ is the positive integer with
$n = u(n) v(n)^2$. Then $A(1) = \{1\}$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 1. -/
public theorem squareSplitDivisors_one : squareSplitDivisors 1 = {1} := by
  simp [squareSplitDivisors, squareSplitU_one, squareSplitV_one]

/-- **Square-splitting convolution.** For complex arithmetic functions $f$ and $g$, the
square-splitting $A$-convolution of Narkiewicz type is the arithmetic function $f \star g$ given by
$(f \star g)(n) = \sum_{d \in A(n)} f(d)\, g(n/d)$ for $n \ge 1$ and $(f \star g)(0) = 0$. Here
$A(n) = \{u_1 v_1^2 : u_1 \mid u(n),\ v_1 \mid v(n)\}$ is the square-splitting divisor set of $n$,
where $u(n)$ is the squarefree part of $n$ and $n = u(n) v(n)^2$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2
and Theorem 4 (`F = 1 ⋆ f` means `F(n) = ∑_{d ∈ A(n)} f(d)`). -/
public noncomputable def squareSplitConv (f g : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else ∑ d ∈ squareSplitDivisors n, f d * g (n / d), by simp⟩

/-- **Value of the square-splitting convolution at a positive integer.** For complex arithmetic
functions $f$ and $g$ and every natural number $n \ne 0$, the square-splitting convolution of $f$
and $g$ takes the value $(f \star g)(n) = \sum_{d \in A(n)} f(d)\, g(n/d)$ at $n$, where $A(n)$ is
the square-splitting divisor set of $n$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2. -/
public theorem squareSplitConv_apply (f g : ArithmeticFunction ℂ) {n : ℕ} (hn : n ≠ 0) :
    squareSplitConv f g n = ∑ d ∈ squareSplitDivisors n, f d * g (n / d) := by
  simp [squareSplitConv, hn]

/-- **The square-splitting convolution preserves multiplicativity.** If $f$ and $g$ are
multiplicative complex arithmetic functions, then their square-splitting convolution $f \star g$
is multiplicative. Here an arithmetic function $h$ is multiplicative when $h(1) = 1$ and
$h(mn) = h(m)\, h(n)$ for all coprime $m$ and $n$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Corollary 1
(`integers-2026-A56-cor-1`). -/
public theorem_wanted squareSplitConv_isMultiplicative {f g : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) :
    (squareSplitConv f g).IsMultiplicative

/-- **Basic properties of the square-splitting divisor sets.** Let
$A(n) = \{u_1 v_1^2 : u_1 \mid u(n),\ v_1 \mid v(n)\}$ be the square-splitting divisor set of
$n$, where $u(n)$ is the squarefree part of $n$ and $n = u(n) v(n)^2$ for $n \ge 1$. Then
(i) for every $n \ge 1$, both $1$ and $n$ belong to $A(n)$, and every element of $A(n)$ divides
$n$; (ii) for all coprime natural numbers $m$ and $n$, $A(mn) = \{ab : a \in A(m),\ b \in A(n)\}$;
and (iii) for every $n \ge 1$, $|A(n)| = d(u(n))\, d(v(n))$ and $|A(n)| = 2^{\omega(u(n))} d(v(n))$,
where $d(k)$ is the number of divisors of $k$ and $\omega(k)$ is the number of distinct prime
factors of $k$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 1
(`integers-2026-A56-thm-1`). -/
public theorem_wanted squareSplitDivisors_properties :
    (∀ n ≠ 0, 1 ∈ squareSplitDivisors n ∧ n ∈ squareSplitDivisors n ∧
      ∀ d ∈ squareSplitDivisors n, d ∣ n) ∧
    (∀ m n, Nat.Coprime m n → squareSplitDivisors (m * n) =
      (squareSplitDivisors m ×ˢ squareSplitDivisors n).image fun x => x.1 * x.2) ∧
    (∀ n ≠ 0, (squareSplitDivisors n).card =
        (squareSplitU n).divisors.card * (squareSplitV n).divisors.card ∧
      (squareSplitDivisors n).card =
        2 ^ ArithmeticFunction.cardDistinctFactors (squareSplitU n) *
          (squareSplitV n).divisors.card)

/-- **Ring axioms for the square-splitting convolution.** For all complex arithmetic functions
$f$, $g$ and $h$, the square-splitting convolution $\star$ satisfies $f \star g = g \star f$,
$(f \star g) \star h = f \star (g \star h)$, $f \star (g + h) = f \star g + f \star h$ and
$\varepsilon \star f = f$, where $\varepsilon$ is the arithmetic function with $\varepsilon(1) = 1$
and $\varepsilon(n) = 0$ for $n \ne 1$.

With pointwise addition, these identities make the complex arithmetic functions a commutative ring
under $\star$ with identity $\varepsilon$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 2
(`integers-2026-A56-thm-2`). -/
public theorem_wanted squareSplitConv_commRing_axioms (f g h : ArithmeticFunction ℂ) :
    squareSplitConv f g = squareSplitConv g f ∧
      squareSplitConv (squareSplitConv f g) h = squareSplitConv f (squareSplitConv g h) ∧
      squareSplitConv f (g + h) = squareSplitConv f g + squareSplitConv f h ∧
      squareSplitConv 1 f = f

/-- **Square-splitting convolution as a bivariate Dirichlet convolution.** Let $\star$ be the
square-splitting convolution. For all complex arithmetic functions $f$ and $g$, every squarefree
natural number $u$ and every natural number $v \ge 1$,
$$(f \star g)(u v^2) = \sum_{u_1 \mid u} \sum_{v_1 \mid v} f(u_1 v_1^2)\, g((u/u_1)(v/v_1)^2).$$
Moreover, for every function $F : \mathbb{N} \times \mathbb{N} \to \mathbb{C}$ there is exactly
one complex arithmetic function $f$ with $f(u v^2) = F(u, v)$ for every squarefree $u$ and every
$v \ge 1$.

Thus $f \mapsto \big((u, v) \mapsto f(u v^2)\big)$ is a bijection from complex arithmetic functions
onto functions on $\{(u, v) : u \text{ squarefree},\ v \ge 1\}$, and it turns $\star$ into the
bivariate Dirichlet convolution
$(\Phi \odot \Psi)(u, v) = \sum_{u_1 \mid u} \sum_{v_1 \mid v} \Phi(u_1, v_1)\, \Psi(u/u_1, v/v_1)$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 2
(`integers-2026-A56-thm-2`). -/
public theorem_wanted squareSplitConv_bivariate_iso :
    (∀ (f g : ArithmeticFunction ℂ) (u v : ℕ), Squarefree u → 0 < v →
      squareSplitConv f g (u * v ^ 2) =
        ∑ u₁ ∈ u.divisors, ∑ v₁ ∈ v.divisors,
          f (u₁ * v₁ ^ 2) * g ((u / u₁) * (v / v₁) ^ 2)) ∧
    ∀ F : ℕ → ℕ → ℂ, ∃! f : ArithmeticFunction ℂ,
      ∀ u v, Squarefree u → 0 < v → f (u * v ^ 2) = F u v

/-- **Möbius function of the square-splitting convolution.** Let $\star$ be the square-splitting
convolution, $\mathbf{1}$ the constant function $1$ on the positive integers, $\varepsilon$ the
identity element ($\varepsilon(1) = 1$ and $\varepsilon(n) = 0$ for $n \ne 1$), and let $\mu_\star$
be any complex-valued arithmetic function with $\mathbf{1} \star \mu_\star = \varepsilon$. Then
$\mu_\star(n) = \mu(u(n))\,\mu(v(n))$ for every $n \ge 1$, where $\mu$ is the Möbius function,
$u(n)$ is the product of the primes dividing $n$ to an odd power and $v(n)$ is the positive
integer with $n = u(n)\,v(n)^2$. For every prime $p$, $\mu_\star(p) = \mu_\star(p^2) = -1$,
$\mu_\star(p^3) = 1$ and $\mu_\star(p^k) = 0$ for every $k \ge 4$. For every complex $s$ with
$\operatorname{Re} s > 1$,
$$\sum_{n \ge 1} \frac{\mu_\star(n)}{n^s} = \prod_p \left(1 - p^{-s} - p^{-2s} + p^{-3s}\right)
= \frac{1}{\zeta(s)\,\zeta(2s)}.$$

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 3
(`integers-2026-A56-thm-3`). -/
public theorem_wanted squareSplitMoebius_formula (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    (∀ n ≠ 0, m n = (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
      ArithmeticFunction.moebius (squareSplitV n)) ∧
    (∀ p : ℕ, p.Prime → m p = -1 ∧ m (p ^ 2) = -1 ∧ m (p ^ 3) = 1 ∧
      ∀ k, 4 ≤ k → m (p ^ k) = 0) ∧
    ∀ s : ℂ, 1 < s.re →
      LSeries (fun n => m n) s = ∏' p : Nat.Primes,
        (1 - ((p : ℕ) : ℂ) ^ (-s) - ((p : ℕ) : ℂ) ^ (-(2 * s)) + ((p : ℕ) : ℂ) ^ (-(3 * s))) ∧
      LSeries (fun n => m n) s = 1 / (riemannZeta s * riemannZeta (2 * s))

/-- **Möbius inversion for the square-splitting convolution.** Let $\star$ be the
square-splitting convolution, $\mathbf{1}$ the constant function $1$ on the positive integers,
$\varepsilon$ the identity element ($\varepsilon(1) = 1$ and $\varepsilon(n) = 0$ for $n \ne 1$),
and let $\mu_\star$ be any complex-valued arithmetic function with
$\mathbf{1} \star \mu_\star = \varepsilon$. Then for all complex-valued arithmetic functions $f$
and $F$, $F = \mathbf{1} \star f$ if and only if $f = \mu_\star \star F$; that is,
$F(n) = \sum_{d \in A(n)} f(d)$ for every $n \ge 1$ if and only if
$f(n) = \sum_{d \in A(n)} \mu_\star(d)\,F(n/d)$ for every $n \ge 1$, where $A(n)$ is the set of
square-splitting divisors of $n$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 4
(`integers-2026-A56-thm-4`). -/
public theorem_wanted squareSplit_moebius_inversion (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1)
    (f F : ArithmeticFunction ℂ) :
    F = squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) f ↔
      f = squareSplitConv m F

/-- **Inverse of a multiplicative function under the square-splitting convolution.** Let $f$ be a
multiplicative complex arithmetic function (an arithmetic function $h$ is multiplicative when
$h(1) = 1$ and $h(mn) = h(m)\, h(n)$ for coprime $m$ and $n$), let $\star$ be the square-splitting
convolution, and let $\varepsilon$ be the arithmetic function with $\varepsilon(1) = 1$ and
$\varepsilon(n) = 0$ for $n \ne 1$. Then there is a complex arithmetic function $g$ with
$f \star g = \varepsilon$ such that every complex arithmetic function $g'$ with
$f \star g' = \varepsilon$ equals $g$. Moreover, $g$ is multiplicative; for every prime $p$ and
every $k \ge 1$, $\sum_{j=0}^{\lfloor k/2 \rfloor} f(p^{2j})\, g(p^{k-2j}) = 0$ if $k$ is even and
$\sum_{j=0}^{\lfloor k/2 \rfloor} (f(p^{2j}) g(p^{k-2j}) + f(p^{2j+1}) g(p^{k-2j-1})) = 0$ if $k$ is
odd; $g(1) = 1/f(1)$; and for every prime $p$, $g(p) = -f(p)/f(1)^2$,
$g(p^2) = -f(p^2)/f(1)^2$ and $g(p^3) = \big(2 f(p) f(p^2) - f(p^3) f(1)\big)/f(1)^3$.

Multiplicativity includes $f(1) = 1$, so the source's hypothesis $f(1) \ne 0$ holds automatically.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 5
(`integers-2026-A56-thm-5`). -/
public theorem_wanted squareSplitConv_inverse_of_isMultiplicative {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) :
    ∃ g : ArithmeticFunction ℂ, squareSplitConv f g = 1 ∧
      (∀ g' : ArithmeticFunction ℂ, squareSplitConv f g' = 1 → g' = g) ∧
      g.IsMultiplicative ∧
      (∀ p k : ℕ, p.Prime → 1 ≤ k →
        ∑ j ∈ Finset.range (k / 2 + 1), f (p ^ (2 * j)) * g (p ^ (k - 2 * j)) +
          (if Odd k then ∑ j ∈ Finset.range (k / 2 + 1),
            f (p ^ (2 * j + 1)) * g (p ^ (k - (2 * j + 1))) else 0) = 0) ∧
      g 1 = 1 / f 1 ∧
      ∀ p : ℕ, p.Prime →
        g p = -f p / f 1 ^ 2 ∧ g (p ^ 2) = -f (p ^ 2) / f 1 ^ 2 ∧
        g (p ^ 3) = (2 * f p * f (p ^ 2) - f (p ^ 3) * f 1) / f 1 ^ 3

/-- **The square-splitting totient function.** Let $A(n)$ be the set of square-splitting divisors
of $n$, and let $\varphi_\star$ be any integer-valued arithmetic function with
$\sum_{d \in A(n)} \varphi_\star(d) = n$ for every $n \ge 1$. Then $\varphi_\star$ is
multiplicative and $\varphi_\star(1) = 1$. For every prime $p$, $\varphi_\star(p) = p - 1$, and
for every $b \ge 1$, $\varphi_\star(p^{2b}) = (p^2 - 1)\,p^{2b-2}$ and
$\varphi_\star(p^{2b+1}) = (p - 1)(p^2 - 1)\,p^{2b-2}$. Moreover, for every $n \ge 1$,
$$\varphi_\star(n) = \varphi(u(n))\,v(n)^2 \prod_{p \mid v(n)} \left(1 - \frac{1}{p^2}\right),$$
where $\varphi$ is Euler's totient function, $u(n)$ is the product of the primes dividing $n$ to
an odd power and $v(n)$ is the positive integer with $n = u(n)\,v(n)^2$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 7
(`integers-2026-A56-thm-7`). -/
public theorem_wanted squareSplitTotient_formula (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) :
    φ.IsMultiplicative ∧ φ 1 = 1 ∧
    (∀ p : ℕ, p.Prime → φ p = (p : ℤ) - 1 ∧
      ∀ b, 1 ≤ b → φ (p ^ (2 * b)) = ((p : ℤ) ^ 2 - 1) * (p : ℤ) ^ (2 * b - 2) ∧
        φ (p ^ (2 * b + 1)) = ((p : ℤ) - 1) * ((p : ℤ) ^ 2 - 1) * (p : ℤ) ^ (2 * b - 2)) ∧
    ∀ n ≠ 0, (φ n : ℚ) = (squareSplitU n).totient * (squareSplitV n : ℚ) ^ 2 *
      ∏ p ∈ (squareSplitV n).primeFactors, (1 - 1 / (p : ℚ) ^ 2)

/-- **Average order of the square-splitting totient function.** Let $A(n)$ be the set of
square-splitting divisors of $n$, and let $\varphi_\star$ be any integer-valued arithmetic function
with $\sum_{d \in A(n)} \varphi_\star(d) = n$ for every $n \ge 1$. Then the product
$M = \prod_p \left(1 - \frac{1}{p^2} + \frac{(p-1)^2}{p^5}\right)$ converges absolutely, that is,
$\sum_p \left|\frac{(p-1)^2}{p^5} - \frac{1}{p^2}\right| < \infty$, and for every
$0 < \varepsilon < 1/2$,
$$\sum_{1 \le n \le x} \varphi_\star(n) = \frac{M}{2}\,x^2 + O(x^{1+\varepsilon})
\quad (x \to \infty).$$

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 8
(`integers-2026-A56-thm-8`). -/
public theorem_wanted squareSplitTotient_sum_asymptotic (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) :
    Summable (fun p : Nat.Primes =>
      |-(1 / ((p : ℕ) : ℝ) ^ 2) + (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5|) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (φ n : ℝ) -
        (∏' p : Nat.Primes,
          (1 - 1 / ((p : ℕ) : ℝ) ^ 2 + (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5)) / 2 * x ^ 2)
        =O[atTop] fun x => x ^ (1 + ε)

/-- **Dirichlet series of the square-splitting divisor function.** Let $\tau^\star(n) = |A(n)|$ be
the number of elements of the square-splitting divisor set $A(n)$, and let
$H(s) = \prod_p (1 - 3p^{-2s} + 2p^{-3s})$, where $p$ runs over the primes. For every complex
number $s$ with $\operatorname{Re} s > 1$, the series $\sum_{k \ge 0} \tau^\star(p^k) p^{-ks}$
converges to $(1 + 2p^{-s})/(1 - p^{-2s})^2$ for each prime $p$, and the Dirichlet series
$\sum_{n \ge 1} \tau^\star(n) n^{-s}$ equals both $\prod_p (1 + 2p^{-s})/(1 - p^{-2s})^2$ and
$\zeta(s)^2 \zeta(2s)^2 H(s)$. Moreover, for every $s$ with $\operatorname{Re} s > 1/2$ the series
$\sum_p |-3p^{-2s} + 2p^{-3s}|$ converges (so the product defining $H(s)$ converges absolutely),
$H$ is holomorphic on the half-plane $\operatorname{Re} s > 1/2$, and $H(1) \ne 0$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 9
(`integers-2026-A56-thm-9`). -/
public theorem_wanted squareSplitDivisorCount_LSeries :
    let τ : ℕ → ℂ := fun n => ((squareSplitDivisors n).card : ℂ)
    let H : ℂ → ℂ := fun s => ∏' p : Nat.Primes,
      (1 - 3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s)))
    (∀ s : ℂ, 1 < s.re →
      (∀ p : Nat.Primes, HasSum (fun k : ℕ => τ ((p : ℕ) ^ k) * ((p : ℕ) : ℂ) ^ (-(k * s)))
        ((1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2)) ∧
      LSeries (fun n => τ n) s = ∏' p : Nat.Primes,
        (1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2 ∧
      LSeries (fun n => τ n) s = riemannZeta s ^ 2 * riemannZeta (2 * s) ^ 2 * H s) ∧
    (∀ s : ℂ, 1 / 2 < s.re → Summable (fun p : Nat.Primes =>
      ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s))‖)) ∧
    DifferentiableOn ℂ H {s | 1 / 2 < s.re} ∧ H 1 ≠ 0

/-- **Partial-sum asymptotics for a Riemann zeta quotient times a Dirichlet series.** Let
$f, g : \mathbb{N} \to \mathbb{C}$ and let $\sigma_0 < 1/2$ be a real number. Suppose that the
Dirichlet series $G(s) = \sum_{n \ge 1} g(n) n^{-s}$ converges absolutely for
$\operatorname{Re} s > \sigma_0$, that $G(1) \ne 0$, and that for every complex $s$ with
$\operatorname{Re} s > 1$ the Dirichlet series $F(s) = \sum_{n \ge 1} f(n) n^{-s}$ converges
absolutely and $F(s) = \zeta(s)^2 G(s) / \zeta(2s)$, where $\zeta$ is the Riemann zeta
function. Then, as the real number $x$ tends to infinity,
$$
\sum_{1 \le n \le x} f(n) = \frac{G(1)}{\zeta(2)}\, x \log x +
\frac{G(1)}{\zeta(2)} \left(2\gamma - 1 + \frac{G'(1)}{G(1)} -
\frac{2\zeta'(2)}{\zeta(2)}\right) x + O\big(x^{1/2} (\log x)^3\big),
$$
where $\gamma$ is the Euler–Mascheroni constant and $G'$, $\zeta'$ are complex derivatives.

The hypothesis $G(1) \ne 0$ is added so that the quotient $G'(1)/G(1)$ is meaningful.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Lemma 1
(`integers-2026-A56-lem-1`). -/
public theorem_wanted sum_asymptotic_of_LSeries_eq_zeta_sq_div_zeta_two_mul (f g : ℕ → ℂ)
    {σ₀ : ℝ} (hσ₀ : σ₀ < 1 / 2) (hg : ∀ s : ℂ, σ₀ < s.re → LSeriesSummable g s)
    (hf : ∀ s : ℂ, 1 < s.re →
      LSeriesSummable f s ∧ LSeries f s = riemannZeta s ^ 2 / riemannZeta (2 * s) * LSeries g s)
    (hG1 : LSeries g 1 ≠ 0) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n -
        (LSeries g 1 / riemannZeta 2 * x * Real.log x +
          LSeries g 1 / riemannZeta 2 * (2 * Real.eulerMascheroniConstant - 1 +
            deriv (LSeries g) 1 / LSeries g 1 - 2 * deriv riemannZeta 2 / riemannZeta 2) * x))
      =O[atTop] fun x => x ^ (1 / 2 : ℝ) * Real.log x ^ 3

/-- **Average order of the square-splitting divisor function.** Let $\tau^\star(n) = |A(n)|$ be
the number of elements of the square-splitting divisor set $A(n)$, let $\gamma$ be the
Euler–Mascheroni constant, and let $A_\tau = \prod_p (1 - 1/(p+1)^2)$ and
$B_\tau = 6 \sum_p \log p / ((p-1)(p+1)(p+2))$, where $p$ runs over the primes. Then, as the real
number $x$ tends to infinity,
$\sum_{1 \le n \le x} \tau^\star(n) - A_\tau x \log x - A_\tau (2\gamma - 1 - B_\tau - c) x$ is
$O(x^{1/2} (\log x)^3)$, where $c = 2\zeta'(2)/\zeta(2)$.

These constants are the ones forced by the Dirichlet series of $\tau^\star$: with
$H(s) = \prod_p (1 - 3p^{-2s} + 2p^{-3s})$, one has $A_\tau = \zeta(2)^2 H(1)$ and
$-B_\tau - 2\zeta'(2)/\zeta(2) = 4\zeta'(2)/\zeta(2) + H'(1)/H(1)$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 10
(`integers-2026-A56-thm-10`). -/
public theorem_wanted squareSplitDivisorCount_sum_asymptotic :
    let Aτ : ℝ := ∏' p : Nat.Primes, (1 - 1 / (((p : ℕ) : ℝ) + 1) ^ 2)
    let Bτ : ℝ := 6 * ∑' p : Nat.Primes, Real.log (p : ℕ) /
      ((((p : ℕ) : ℝ) - 1) * (((p : ℕ) : ℝ) + 1) * (((p : ℕ) : ℝ) + 2))
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((squareSplitDivisors n).card : ℝ) -
        (Aτ * x * Real.log x + Aτ * (2 * Real.eulerMascheroniConstant - 1 - Bτ -
          2 * (deriv riemannZeta 2 / riemannZeta 2).re) * x))
      =O[atTop] fun x => x ^ (1 / 2 : ℝ) * Real.log x ^ 3

/-- **Support and density of the square-splitting Möbius function.** Let $\star$ be the
square-splitting convolution, $\mathbf{1}$ the constant function $1$ on the positive integers,
$\varepsilon$ the identity element ($\varepsilon(1) = 1$ and $\varepsilon(n) = 0$ for $n \ne 1$),
and let $\mu_\star$ be any complex-valued arithmetic function with
$\mathbf{1} \star \mu_\star = \varepsilon$. Then for every $n \ge 1$, $\mu_\star(n) \ne 0$ if and
only if every prime exponent of $n$ is at most $3$. The proportion of the integers
$1 \le n \le N$ with $\mu_\star(n) \ne 0$ tends to $\prod_p (1 - p^{-4})$ as $N \to \infty$, and
$\prod_p (1 - p^{-4}) = 1/\zeta(4)$. Finally,
$\sum_{1 \le n \le x} |\mu_\star(n)|^2 \sim x/\zeta(4)$ as $x \to \infty$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 11
(`integers-2026-A56-thm-11`). -/
public theorem_wanted squareSplitMoebius_support_density (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    (∀ n ≠ 0, m n ≠ 0 ↔ ∀ p, n.factorization p ≤ 3) ∧
    Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter fun n => m n ≠ 0).card : ℝ) / N) atTop
      (𝓝 (∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 4))) ∧
    ((∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 4) : ℝ) : ℂ) = 1 / riemannZeta 4 ∧
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖m n‖ ^ 2) ~[atTop]
      fun x => x / (riemannZeta 4).re

/-- **A square-splitting divisor function and its Euler product.** Let
$\alpha \in \mathbb{C}$, let $\sigma_\beta(m) = \sum_{d \mid m} d^\beta$ for $\beta \in \mathbb{C}$
(complex powers), and let $f(n) = \sigma_\alpha(u(n))\,\sigma_{2\alpha}(v(n))$, where $u(n)$ is
the product of the primes dividing $n$ to an odd power and $v(n)$ is the positive integer with
$n = u(n)\,v(n)^2$. Then $f(1) = 1$ and $f(mn) = f(m)\,f(n)$ for all coprime $m$ and $n$. For
every prime $p$ and every $b \ge 0$, $f(p^{2b}) = \sum_{j=0}^{b} p^{2j\alpha}$ and
$f(p^{2b+1}) = (1 + p^\alpha) \sum_{j=0}^{b} p^{2j\alpha}$. For every complex $s$ with
$\operatorname{Re} s > \max(1, 1 + \operatorname{Re} \alpha)$, for every prime $p$
$$\sum_{k \ge 0} \frac{f(p^k)}{p^{ks}}
= \frac{1 + p^{-s} + p^{-(s-\alpha)}}{(1 - p^{-2s})(1 - p^{-(2s-2\alpha)})},$$
the series $\sum_{n \ge 1} f(n)\,n^{-s}$ converges absolutely, and
$$\sum_{n \ge 1} \frac{f(n)}{n^s}
= \zeta(2s)\,\zeta(2s - 2\alpha) \prod_p \left(1 + p^{-s} + p^{-(s-\alpha)}\right).$$

The paper identifies $f$ with its divisor function $\sigma_{\star,\alpha}$; that identification is
not part of this statement.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 6
(`integers-2026-A56-thm-6`). -/
public theorem_wanted squareSplitSigma_multiplicative_eulerProduct (α : ℂ) :
    let σ : ℂ → ℕ → ℂ := fun β m => ∑ d ∈ m.divisors, (d : ℂ) ^ β
    let f : ℕ → ℂ := fun n => σ α (squareSplitU n) * σ (2 * α) (squareSplitV n)
    f 1 = 1 ∧ (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) ∧
    (∀ p : ℕ, p.Prime → ∀ b : ℕ,
      f (p ^ (2 * b)) = ∑ j ∈ Finset.range (b + 1), (p : ℂ) ^ (2 * j * α) ∧
      f (p ^ (2 * b + 1)) =
        (1 + (p : ℂ) ^ α) * ∑ j ∈ Finset.range (b + 1), (p : ℂ) ^ (2 * j * α)) ∧
    ∀ s : ℂ, max 1 (1 + α.re) < s.re →
      (∀ p : ℕ, p.Prime →
        HasSum (fun k : ℕ => f (p ^ k) * (p : ℂ) ^ (-(k * s)))
          ((1 + (p : ℂ) ^ (-s) + (p : ℂ) ^ (-(s - α))) /
            ((1 - (p : ℂ) ^ (-(2 * s))) * (1 - (p : ℂ) ^ (-(2 * s - 2 * α)))))) ∧
      LSeriesSummable f s ∧
      LSeries f s = riemannZeta (2 * s) * riemannZeta (2 * s - 2 * α) *
        ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s) + ((p : ℕ) : ℂ) ^ (-(s - α)))

end

end MetaMathlibExt
