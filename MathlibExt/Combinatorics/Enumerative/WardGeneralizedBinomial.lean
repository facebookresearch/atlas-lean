/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Ring.Nat

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-!
# Ward generalized binomial coefficients

Source: T. Edgar and M. Z. Spivey, *Multiplicative Functions, Generalized Binomial
Coefficients, and Generalized Catalan Numbers*, Journal of Integer Sequences 19 (2016),
[`edgar3.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex).
-/

/-- **Units-place carry.** For natural numbers $b$, $n$ and $m$, the units-place carry
$\varepsilon_0^{b,n,m}$ of $n + m$ in base $b$ is $1$ if $b > 1$ and
$(n \bmod b) + (m \bmod b) \ge b$, and $0$ otherwise; in particular it is $0$ for the invalid
bases $b \le 1$. -/
public def wardUnitsCarry (b n m : ℕ) : ℕ :=
  if 1 < b ∧ b ≤ n % b + m % b then 1 else 0

/-- **Ward generalized binomial coefficient.** Let $R$ be a commutative monoid and
$s = (s_b)_{b \in \mathbb{N}}$ a sequence in $R$. For natural numbers $n$ and $m$, the Ward
generalized binomial coefficient is

$$\binom{n+m}{n}_s = \prod_{b=2}^{n+m} s_b^{\varepsilon_0^{b,n,m}},$$

where $\varepsilon_0^{b,n,m} \in \{0, 1\}$ is the carry in the units place when $n$ and $m$ are
added in base $b$.

This is Ward's product $\prod_{b > 1} s_b^{\varepsilon_0^{b,n,m}}$: no base larger than $n + m$
carries in the units place, so the product is finite. The source uses the product as a
definition for arbitrary coefficient sequences, including sequences with zero terms. -/
public def wardGeneralizedBinomialCoefficient {R : Type*} [CommMonoid R]
    (s : ℕ → R) (n m : ℕ) : R :=
  ((Finset.range (n + m + 1)).filter fun b => 1 < b).prod
    fun b => s b ^ wardUnitsCarry b n m

/-- **Units-place carry as a quotient.** For all natural numbers $b$, $n$ and $m$, the units-place
carry of $n + m$ in base $b$ (taken to be $0$ when $b \le 1$) equals
$\lfloor ((n \bmod b) + (m \bmod b)) / b \rfloor$, where $n \bmod 0 = n$ and division by $0$
gives $0$. -/
theorem wardUnitsCarry_eq_div (b n m : ℕ) : wardUnitsCarry b n m = (n % b + m % b) / b := by
  unfold wardUnitsCarry
  rcases Nat.lt_or_ge 1 b with hb | hb
  · have hn := Nat.mod_lt n (by omega : 0 < b)
    have hm := Nat.mod_lt m (by omega : 0 < b)
    split_ifs with h
    · exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm
    · exact (Nat.div_eq_of_lt (by omega)).symm
  · rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp [Nat.mod_one]

/-- **Ward's generalized binomial coefficient as a finite product.** Let $R$ be a commutative
monoid and $s = (s_b)_{b \in \mathbb{N}}$ a sequence in $R$. For all natural numbers $n$ and $m$,
the Ward generalized binomial coefficient $\binom{n+m}{n}_s$ equals

$$\prod_{b=2}^{n+m} s_b^{\lfloor ((n \bmod b) + (m \bmod b)) / b \rfloor}.$$
-/
theorem wardGeneralizedBinomialCoefficient_eq_prod_Icc {R : Type*} [CommMonoid R]
    (s : ℕ → R) (n m : ℕ) :
    wardGeneralizedBinomialCoefficient s n m =
      ∏ b ∈ Finset.Icc 2 (n + m), s b ^ ((n % b + m % b) / b) := by
  have hset : (Finset.range (n + m + 1)).filter (fun b => 1 < b) = Finset.Icc 2 (n + m) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  simp only [wardGeneralizedBinomialCoefficient, hset, wardUnitsCarry_eq_div]

end

end MetaMathlibExt
