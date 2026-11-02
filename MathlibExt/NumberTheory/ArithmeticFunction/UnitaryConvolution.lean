/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
public import MathlibExt.NumberTheory.UnitaryDivisor

/-!
# Unitary convolution and arithmetic functions given on prime powers

This file defines, for arithmetic functions with values in a (semi)ring `R`:

* `MetaMathlibExt.powOmega c`: the completely multiplicative function `n ↦ c ^ Ω(n)`;
* `MetaMathlibExt.unitaryConv f g`: the unitary convolution
  `(f ⊔ g)(n) = ∑_{d ∥ n} f(d) g(n / d)` over the unitary divisors `Nat.unitaryDivisors`;
* `MetaMathlibExt.multiplicativeOfPrimePowers g`: the multiplicative function with value `g m`
  at every prime power `p ^ m`, `m ≥ 1`.

It proves their prime-power formulas and that all three are multiplicative (`powOmega`
completely multiplicative; the unitary convolution of multiplicative functions is
multiplicative), so that identities between them reduce to prime powers through
`ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers`.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Sections 1.3
and 2.
-/

open ArithmeticFunction Finset

namespace Nat

@[expose] public section

/-- **Unitary divisors of a prime power.** For every prime $p$ and every natural number $m$, the
unitary divisors of $p^m$, that is, the divisors $d$ of $p^m$ with $\gcd(d, p^m/d) = 1$, are
exactly $1$ and $p^m$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3. -/
theorem unitaryDivisors_prime_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (p ^ m).unitaryDivisors = {1, p ^ m} := by
  ext d
  simp only [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, -, hcop⟩
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
    rw [Nat.pow_div hk hp.pos] at hcop
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    rcases Nat.eq_zero_or_pos (m - k) with hmk | hmk
    · right
      rw [show k = m by omega]
    · exfalso
      rw [Nat.coprime_pow_left_iff hk0, Nat.coprime_pow_right_iff hmk] at hcop
      exact hp.one_lt.ne' ((Nat.coprime_self p).mp hcop)
  · rintro (rfl | rfl)
    · exact ⟨one_dvd _, pow_ne_zero _ hp.ne_zero, Nat.coprime_one_left _⟩
    · refine ⟨dvd_rfl, pow_ne_zero _ hp.ne_zero, ?_⟩
      rw [Nat.div_self (pow_pos hp.pos _)]
      exact Nat.coprime_one_right _

/-- **Products of unitary divisors of coprime numbers.** Let $m$ and $n$ be coprime natural
numbers. If $a$ is a unitary divisor of $m$ and $b$ is a unitary divisor of $n$, then $ab$ is a
unitary divisor of $mn$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3. -/
theorem mul_mem_unitaryDivisors_mul {m n a b : ℕ} (hmn : m.Coprime n)
    (ha : a ∈ m.unitaryDivisors) (hb : b ∈ n.unitaryDivisors) :
    a * b ∈ (m * n).unitaryDivisors := by
  rw [mem_unitaryDivisors] at ha hb ⊢
  obtain ⟨ham, hm0, hacop⟩ := ha
  obtain ⟨hbn, hn0, hbcop⟩ := hb
  refine ⟨Nat.mul_dvd_mul ham hbn, Nat.mul_ne_zero hm0 hn0, ?_⟩
  rw [← Nat.div_mul_div_comm ham hbn]
  refine Nat.Coprime.mul_left (Nat.Coprime.mul_right hacop ?_) (Nat.Coprime.mul_right ?_ hbcop)
  · exact (hmn.coprime_dvd_left ham).coprime_dvd_right (Nat.div_dvd_of_dvd hbn)
  · exact (hmn.symm.coprime_dvd_left hbn).coprime_dvd_right (Nat.div_dvd_of_dvd ham)

/-- **Gcd with a coprime factor preserves unitary divisors.** Let $m$ and $n$ be coprime natural
numbers. If $d$ is a unitary divisor of $mn$, then $\gcd(d, m)$ is a unitary divisor of $m$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3. -/
theorem gcd_mem_unitaryDivisors_of_mem_mul {m n d : ℕ} (hmn : m.Coprime n)
    (hd : d ∈ (m * n).unitaryDivisors) : d.gcd m ∈ m.unitaryDivisors := by
  rw [mem_unitaryDivisors] at hd ⊢
  obtain ⟨hdmn, hmn0, hdcop⟩ := hd
  have hm0 : m ≠ 0 := left_ne_zero_of_mul hmn0
  have hsplit : d.gcd m * d.gcd n = d := by
    rw [← Nat.Coprime.gcd_mul d hmn, Nat.gcd_eq_left hdmn]
  have hquot : m * n / d = m / d.gcd m * (n / d.gcd n) := by
    conv_lhs => rw [← hsplit]
    rw [Nat.div_mul_div_comm (Nat.gcd_dvd_right d m) (Nat.gcd_dvd_right d n)]
  refine ⟨Nat.gcd_dvd_right d m, hm0, ?_⟩
  rw [hquot] at hdcop
  exact (hdcop.coprime_dvd_left (Nat.gcd_dvd_left d m)).coprime_dvd_right
    (Nat.dvd_mul_right _ _)

end

end Nat

namespace MetaMathlibExt

@[expose] public section

variable {R : Type*}

/-! ### `c ^ Ω` -/

/-- **The arithmetic function $c^{\Omega}$.** Let $R$ be a monoid with zero and let $c \in R$. This
is the arithmetic function $c^{\Omega}$ with values in $R$ given by $c^{\Omega}(0) = 0$ and
$c^{\Omega}(n) = c^{\Omega(n)}$ for $n \ge 1$, where $\Omega(n)$ is the number of prime factors of
$n$ counted with multiplicity. It is completely multiplicative.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 2. -/
def powOmega [MonoidWithZero R] (c : R) : ArithmeticFunction R :=
  ⟨fun n => if n = 0 then 0 else c ^ cardFactors n, by simp⟩

/-- **Value of $c^{\Omega}$ at a positive integer.** Let $R$ be a monoid with zero, let $c \in R$,
and let $c^{\Omega}$ be the arithmetic function with values in $R$ that is $0$ at $0$ and
$c^{\Omega(n)}$ at each $n \ge 1$, where $\Omega(n)$ is the number of prime factors of $n$ counted
with multiplicity. For every natural number $n \ne 0$, its value at $n$ is $c^{\Omega(n)}$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 2. -/
theorem powOmega_apply [MonoidWithZero R] (c : R) {n : ℕ} (hn : n ≠ 0) :
    powOmega c n = c ^ cardFactors n := by
  simp [powOmega, hn]

/-- **Value of $c^{\Omega}$ at $1$.** Let $R$ be a monoid with zero, let $c \in R$, and let
$c^{\Omega}$ be the arithmetic function with values in $R$ that is $0$ at $0$ and $c^{\Omega(n)}$ at
each $n \ge 1$, where $\Omega(n)$ is the number of prime factors of $n$ counted with multiplicity.
Its value at $1$ is $1$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 2. -/
@[simp]
theorem powOmega_one [MonoidWithZero R] (c : R) : powOmega c 1 = 1 := by
  simp [powOmega]

/-- **Value of $c^{\Omega}$ at prime powers.** Let $R$ be a monoid with zero, let $c \in R$, and
let $c^{\Omega}$ be the arithmetic function with values in $R$ that is $0$ at $0$ and
$c^{\Omega(n)}$ at each $n \ge 1$, where $\Omega(n)$ is the number of prime factors of $n$ counted
with multiplicity. For every prime $p$ and every natural number $m$, its value at $p^m$ is $c^m$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 2. -/
theorem powOmega_prime_pow [MonoidWithZero R] (c : R) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    powOmega c (p ^ m) = c ^ m := by
  simp [powOmega, hp.ne_zero, cardFactors_apply_prime_pow hp]

/-- **Complete multiplicativity of $c^{\Omega}$.** Let $R$ be a monoid with zero and $c \in R$.
Let $c^{\Omega}$ be the arithmetic function $n \mapsto c^{\Omega(n)}$ for $n \ge 1$, where
$\Omega(n)$ is the number of prime factors of $n$ counted with multiplicity. Then $c^{\Omega}$ is
completely multiplicative: for all natural numbers $m$ and $n$, its value at $mn$ is the product
of its values at $m$ and at $n$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 2. -/
theorem isCompletelyMultiplicative_powOmega [MonoidWithZero R] (c : R) :
    (powOmega c).IsCompletelyMultiplicative := by
  intro m n
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [powOmega_apply c (Nat.mul_ne_zero hm hn), powOmega_apply c hm, powOmega_apply c hn,
    cardFactors_mul hm hn, pow_add]

/-- **Multiplicativity of $c^{\Omega}$.** Let $R$ be a monoid with zero and $c \in R$. The
arithmetic function $n \mapsto c^{\Omega(n)}$ for $n \ge 1$, where $\Omega(n)$ is the number of
prime factors of $n$ counted with multiplicity, is multiplicative.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 2. -/
theorem isMultiplicative_powOmega [MonoidWithZero R] (c : R) :
    (powOmega c).IsMultiplicative :=
  (isCompletelyMultiplicative_powOmega c).isMultiplicative (powOmega_one c)

/-! ### Unitary convolution -/

/-- **Unitary convolution.** Let $R$ be a semiring. The unitary convolution of two arithmetic
functions $f$ and $g$ with values in $R$ is the arithmetic function $f \sqcup g$ given by
$(f \sqcup g)(n) = \sum_{d \parallel n} f(d)\, g(n/d)$, where the sum runs over the unitary divisors
$d$ of $n$: for $n \ge 1$ these are the divisors $d$ of $n$ with $\gcd(d, n/d) = 1$, and $0$ has
no unitary divisors. In particular $(f \sqcup g)(0) = 0$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3. -/
def unitaryConv [Semiring R] (f g : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => ∑ d ∈ n.unitaryDivisors, f d * g (n / d), by simp⟩

/-- **Unitary convolution as a sum over unitary divisors.** Let $R$ be a semiring and let $f$ and
$g$ be arithmetic functions with values in $R$. For every natural number $n$, their unitary
convolution $f \sqcup g$ satisfies $(f \sqcup g)(n) = \sum_{d \parallel n} f(d)\, g(n/d)$, where the
sum runs over the unitary divisors $d$ of $n$: for $n \ge 1$ these are the divisors $d$ of $n$
with $\gcd(d, n/d) = 1$, and for $n = 0$ there are none, so the sum is $0$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3. -/
theorem unitaryConv_apply [Semiring R] (f g : ArithmeticFunction R) (n : ℕ) :
    unitaryConv f g n = ∑ d ∈ n.unitaryDivisors, f d * g (n / d) :=
  rfl

/-- **Unitary convolution at $1$.** Let $R$ be a semiring and let $f$ and $g$ be arithmetic
functions with values in $R$. Their unitary convolution $f \sqcup g$, defined by
$(f \sqcup g)(n) = \sum_{d \parallel n} f(d)\, g(n/d)$ over the unitary divisors $d$ of $n$,
satisfies $(f \sqcup g)(1) = f(1)\, g(1)$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3. -/
@[simp]
theorem unitaryConv_one [Semiring R] (f g : ArithmeticFunction R) :
    unitaryConv f g 1 = f 1 * g 1 := by
  simp [unitaryConv, Nat.unitaryDivisors, Finset.filter_singleton]

/-- **Unitary convolution at prime powers.** Let $R$ be a semiring and let $f$ and $g$ be
arithmetic functions with values in $R$. For every prime $p$ and every natural number $m \ge 1$,
their unitary convolution $f \sqcup g$ satisfies
$(f \sqcup g)(p^m) = f(1)\, g(p^m) + f(p^m)\, g(1)$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3. -/
theorem unitaryConv_prime_pow [Semiring R] (f g : ArithmeticFunction R) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) :
    unitaryConv f g (p ^ m) = f 1 * g (p ^ m) + f (p ^ m) * g 1 := by
  have hne : (1 : ℕ) ≠ p ^ m := (Nat.one_lt_pow hm hp.one_lt).ne
  rw [unitaryConv_apply, Nat.unitaryDivisors_prime_pow hp m, Finset.sum_pair hne,
    Nat.div_one, Nat.div_self (pow_pos hp.pos _)]

/-- **The unitary convolution of multiplicative functions is multiplicative.** Let $R$ be a
commutative semiring. If $f$ and $g$ are multiplicative arithmetic functions with values in $R$,
then their unitary convolution $f \sqcup g$, given by $(f \sqcup g)(n) = \sum_{d} f(d)\, g(n/d)$
with $d$ running over the unitary divisors of $n$, is multiplicative.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3
(`(𝓜, ⊔)` is a group). -/
theorem isMultiplicative_unitaryConv [CommSemiring R] {f g : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) :
    (unitaryConv f g).IsMultiplicative := by
  refine ⟨by simp [hf.map_one, hg.map_one], fun {m n} hmn => ?_⟩
  simp only [unitaryConv_apply]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun x => x.1 * x.2) (fun d => (d.gcd m, d.gcd n)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    rw [Finset.mem_product] at hab
    exact Nat.mul_mem_unitaryDivisors_mul hmn hab.1 hab.2
  · intro d hd
    rw [Finset.mem_product]
    refine ⟨Nat.gcd_mem_unitaryDivisors_of_mem_mul hmn hd, ?_⟩
    rw [mul_comm] at hd
    exact Nat.gcd_mem_unitaryDivisors_of_mem_mul hmn.symm hd
  · rintro ⟨a, b⟩ hab
    rw [Finset.mem_product] at hab
    have ha := Nat.dvd_of_mem_unitaryDivisors hab.1
    have hb := Nat.dvd_of_mem_unitaryDivisors hab.2
    have hbm : b.Coprime m := (hmn.symm.coprime_dvd_left hb)
    have han : a.Coprime n := (hmn.coprime_dvd_left ha)
    simp only [Prod.mk.injEq]
    exact ⟨by rw [Nat.Coprime.gcd_mul_right_cancel a hbm, Nat.gcd_eq_left ha],
      by rw [Nat.Coprime.gcd_mul_left_cancel b han, Nat.gcd_eq_left hb]⟩
  · intro d hd
    rw [Nat.mem_unitaryDivisors] at hd
    simp only
    rw [← Nat.Coprime.gcd_mul d hmn, Nat.gcd_eq_left hd.1]
  · rintro ⟨a, b⟩ hab
    rw [Finset.mem_product] at hab
    have ha := Nat.dvd_of_mem_unitaryDivisors hab.1
    have hb := Nat.dvd_of_mem_unitaryDivisors hab.2
    have hab' : a.Coprime b := (hmn.coprime_dvd_left ha).coprime_dvd_right hb
    have hq : (m / a).Coprime (n / b) :=
      (hmn.coprime_dvd_left (Nat.div_dvd_of_dvd ha)).coprime_dvd_right (Nat.div_dvd_of_dvd hb)
    simp only
    rw [← Nat.div_mul_div_comm ha hb, hf.map_mul_of_coprime hab', hg.map_mul_of_coprime hq]
    ring

/-! ### Multiplicative functions given on prime powers -/

/-- **Multiplicative function with prescribed values at prime powers.** Let $R$ be a commutative
monoid with zero and let $g : \mathbb{N} \to R$. This is the arithmetic function $f$ with values
in $R$ given by $f(0) = 0$ and $f(n) = \prod_{p \mid n} g(v_p(n))$ for $n \ge 1$, where the product
runs over the primes $p$ dividing $n$ and $v_p(n)$ is the exponent of $p$ in $n$. It is
multiplicative, it takes the value $g(m)$ at every prime power $p^m$ with $m \ge 1$, and its value
at $1$ is the empty product $1$, so $g(0)$ never enters.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3 (a
multiplicative function is determined by its values at the prime powers). -/
def multiplicativeOfPrimePowers [CommMonoidWithZero R] (g : ℕ → R) : ArithmeticFunction R :=
  ⟨fun n => if n = 0 then 0 else ∏ p ∈ n.primeFactors, g (n.factorization p), by simp⟩

/-- **Value of the function with prescribed prime-power values.** Let $R$ be a commutative monoid
with zero, let $g : \mathbb{N} \to R$, and let $n \ne 0$ be a natural number. The multiplicative
function with value $g(m)$ at every prime power $p^m$ with $m \ge 1$ takes the value
$\prod_{q \mid n} g(v_q(n))$ at $n$, where $q$ runs over the primes dividing $n$ and $v_q(n)$ is
the exponent of $q$ in the factorization of $n$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3. -/
theorem multiplicativeOfPrimePowers_apply [CommMonoidWithZero R] (g : ℕ → R) {n : ℕ}
    (hn : n ≠ 0) :
    multiplicativeOfPrimePowers g n = n.factorization.prod fun _ k => g k := by
  simp [multiplicativeOfPrimePowers, hn, Finsupp.prod, Nat.support_factorization]

/-- **The function with prescribed prime-power values is $1$ at $1$.** Let $R$ be a commutative
monoid with zero and $g : \mathbb{N} \to R$. The multiplicative function with prime-power values
$g$, given by $n \mapsto \prod_{q \mid n} g(v_q(n))$ for $n \ge 1$ (with $q$ running over the
primes dividing $n$ and $v_q(n)$ the exponent of $q$ in $n$), takes the value $1$ at $n = 1$,
whatever $g(0)$ is.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3. -/
@[simp]
theorem multiplicativeOfPrimePowers_one [CommMonoidWithZero R] (g : ℕ → R) :
    multiplicativeOfPrimePowers g 1 = 1 := by
  simp [multiplicativeOfPrimePowers]

/-- **The function with prescribed prime-power values at a prime power.** Let $R$ be a
commutative monoid with zero and $g : \mathbb{N} \to R$. For every prime $p$ and every $m \ge 1$,
the multiplicative function with prime-power values $g$, given by
$n \mapsto \prod_{q \mid n} g(v_q(n))$ for $n \ge 1$ (with $q$ running over the primes dividing
$n$ and $v_q(n)$ the exponent of $q$ in $n$), takes the value $g(m)$ at $p^m$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3. -/
theorem multiplicativeOfPrimePowers_prime_pow [CommMonoidWithZero R] (g : ℕ → R) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) : multiplicativeOfPrimePowers g (p ^ m) = g m := by
  simp [multiplicativeOfPrimePowers, hp.ne_zero, Nat.primeFactors_prime_pow hm hp,
    hp.factorization_self]

/-- **Multiplicativity of the function with prescribed prime-power values.** Let $R$ be a
commutative monoid with zero and $g : \mathbb{N} \to R$. The arithmetic function
$n \mapsto \prod_{q \mid n} g(v_q(n))$ for $n \ge 1$, where $q$ runs over the primes dividing $n$
and $v_q(n)$ is the exponent of $q$ in $n$, is multiplicative.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3. -/
theorem isMultiplicative_multiplicativeOfPrimePowers [CommMonoidWithZero R] (g : ℕ → R) :
    (multiplicativeOfPrimePowers g).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr
    ⟨multiplicativeOfPrimePowers_one g, fun {m n} hm hn hmn => ?_⟩
  rw [multiplicativeOfPrimePowers_apply g (Nat.mul_ne_zero hm hn),
    multiplicativeOfPrimePowers_apply g hm, multiplicativeOfPrimePowers_apply g hn,
    Nat.factorization_mul_of_coprime hmn,
    Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors]

/-- **A multiplicative function with prescribed prime-power values.** Let $R$ be a
commutative monoid with zero, let $g : \mathbb{N} \to R$, and let $f$ be a multiplicative
arithmetic function with values in $R$. If $f(p^m) = g(m)$ for every prime $p$ and every
$m \ge 1$, then $f$ is the multiplicative function with prime-power values $g$, that is, the
arithmetic function $n \mapsto \prod_{q \mid n} g(v_q(n))$ for $n \ge 1$, where $q$ runs over the
primes dividing $n$ and $v_q(n)$ is the exponent of $q$ in $n$.

Source: Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3 (a
multiplicative function is determined by its values at the prime powers). -/
theorem eq_multiplicativeOfPrimePowers [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (g : ℕ → R)
    (h : ∀ p m : ℕ, p.Prime → m ≠ 0 → f (p ^ m) = g m) :
    f = multiplicativeOfPrimePowers g := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers f hf _
    (isMultiplicative_multiplicativeOfPrimePowers g)).mpr fun p m hp => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hf.map_one]
  · rw [h p m hp hm, multiplicativeOfPrimePowers_prime_pow g hp hm]

end

end MetaMathlibExt
