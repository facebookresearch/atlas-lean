/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Finset.NatDivisors

/-!
# Square-splitting convolution

Splitting each prime exponent into its parity and its half gives a divisor system
whose convolution preserves multiplicativity.
-/

namespace MetaMathlibExt

@[expose] public section

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

namespace squareSplitConv_isMultiplicative

open scoped Pointwise

private theorem squareSplitDivisors_subset {n : ℕ} (hn : n ≠ 0) :
    squareSplitDivisors n ⊆ n.divisors := by
  intro d hd
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
  refine Nat.mem_divisors.mpr ⟨?_, hn⟩
  rw [← squareSplitU_mul_squareSplitV_sq hn]
  exact Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hu)
    (pow_dvd_pow_of_dvd (Nat.dvd_of_mem_divisors hv) 2)

private theorem squareSplitDivisors_mul {m n : ℕ} (h : m.Coprime n) :
    squareSplitDivisors (m * n) = squareSplitDivisors m * squareSplitDivisors n := by
  have prod_mul (F : ℕ → ℕ → ℕ) :
      (m * n).factorization.prod F = m.factorization.prod F * n.factorization.prod F := by
    rw [Nat.factorization_mul_of_coprime h]
    exact Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors F
  have hA (k : ℕ) : squareSplitDivisors k =
      (squareSplitU k).divisors * (squareSplitV k).divisors.image (powMonoidHom 2) :=
    (Finset.image₂_image_right (· * ·) (powMonoidHom 2)).symm
  simp only [hA, squareSplitU, squareSplitV, prod_mul, Nat.divisors_mul, Finset.image_mul]
  ac_rfl

end squareSplitConv_isMultiplicative

open squareSplitConv_isMultiplicative

/-- **The square-splitting convolution preserves multiplicativity.** If $f$ and $g$ are
multiplicative complex arithmetic functions, then their square-splitting convolution $f \star g$
is multiplicative. Here an arithmetic function $h$ is multiplicative when $h(1) = 1$ and
$h(mn) = h(m)\, h(n)$ for all coprime $m$ and $n$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Corollary 1
(`integers-2026-A56-cor-1`). -/
public theorem squareSplitConv_isMultiplicative {f g : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) :
    (squareSplitConv f g).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [squareSplitConv_apply, squareSplitDivisors_one, hf.1, hg.1]
  intro m n hm hn h
  have hsub := Finset.product_subset_product (squareSplitDivisors_subset hm)
    (squareSplitDivisors_subset hn)
  rw [squareSplitConv_apply _ _ (mul_ne_zero hm hn), squareSplitConv_apply _ _ hm,
    squareSplitConv_apply _ _ hn, squareSplitDivisors_mul h, Finset.mul_def,
    Finset.sum_image (h.mul_injOn_divisors.mono hsub), Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ hab
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp (hsub hab)
  have ham := Nat.dvd_of_mem_divisors ha
  have hbn := Nat.dvd_of_mem_divisors hb
  rw [hf.map_mul_of_coprime (h.of_dvd ham hbn), ← Nat.div_mul_div_comm ham hbn,
    hg.map_mul_of_coprime (h.of_dvd (Nat.div_dvd_of_dvd ham) (Nat.div_dvd_of_dvd hbn))]
  exact mul_mul_mul_comm ..

end

end MetaMathlibExt
