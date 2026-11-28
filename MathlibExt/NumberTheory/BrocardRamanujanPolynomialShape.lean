/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.PowerFree
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.BrocardRamanujanFewPrimeFactors
import MathlibExt.NumberTheory.BrocardRamanujanPowerFree

/-!
# Brocard–Ramanujan solutions of polynomial shape

For `k ≥ 2`, `l ≥ 2`, `m ≥ 1`, and an integer polynomial `P` in `m` variables, there are
only finitely many pairs `(n, x)` in `ℕ × ℤ` solving `n! + 1 = x ^ 2` with
`x = x₁ ⋯ xₘ P(x₁, …, xₘ) ± 1`, where each `xᵢ` is a product of a `k`-free natural number
and a positive integer with fewer than `l` distinct prime divisors.

Each `xᵢ` divides `n!`, since their product divides `x - 1` or `x + 1`. For `n > 0`, the two
factorial divisor bounds give `xᵢ ≤ B ^ n` for a fixed `B`. Expanding `P` bounds `|x|` by an
exponential in `n`. Since `n!` eventually exceeds every exponential, both `n` and `|x|`
are bounded. The argument handles either sign of `x` without changing `P`.

## References

* Abderrahim Makki Naciri, *On the Brocard–Ramanujan Equation with 7-Free Integers and Prime
  Powers*, INTEGERS 25 (2025), Article A71, pp. 1–8, Theorem 2 (§4). We use the power-free
  divisor bound from Lemma 1 and a power-of-two bound from the factorial valuation estimate
  in §2 in place of Lemma 2's real-power bound.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 5th ed.,
  Oxford University Press, 1979 (Legendre's formula, cited in §2).
* The ATLAS formalizations `le_exp_of_isPowerFree_dvd_factorial`
  and `le_pow_of_dvd_factorial_of_primeFactors_card_le` in
  `MathlibExt.NumberTheory.BrocardRamanujanPowerFree` and
  `MathlibExt.NumberTheory.BrocardRamanujanFewPrimeFactors`, respectively, supply the divisor
  bounds. As in `brocardRamanujan_fewPrimeFactors_finite`, we use factorial growth to put all
  solutions in a finite box.
-/

open Nat

namespace MetaMathlibExt

private theorem natAbs_eval_le {m : ℕ} (P : MvPolynomial (Fin m) ℤ) {R : ℕ} (hR : 1 ≤ R)
    {xs : Fin m → ℕ} (hxs : ∀ i, xs i ≤ R) :
    (MvPolynomial.eval (fun i => (xs i : ℤ)) P).natAbs ≤
      (∑ d ∈ P.support, (P.coeff d).natAbs) * R ^ P.totalDegree := by
  classical
  rw [MvPolynomial.eval_eq, Finset.sum_mul]
  refine (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun d hd ↦ ?_)
  simp only [Int.natAbs_mul, Int.natAbs_prod, Int.natAbs_pow, Int.natAbs_natCast]
  apply Nat.mul_le_mul_left
  calc
    ∏ i ∈ d.support, xs i ^ d i ≤ ∏ i ∈ d.support, R ^ d i :=
      Finset.prod_le_prod fun i _ ↦ Nat.pow_le_pow_left (hxs i) _
    _ = R ^ d.sum (fun _ e ↦ e) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ R ^ P.totalDegree := Nat.pow_le_pow_right hR (MvPolynomial.le_totalDegree hd)

/-- **Finitely many Brocard–Ramanujan solutions of polynomial shape.** Let $k \ge 2$, $l \ge 2$
and $m \ge 1$ be natural numbers and let $P \in \mathbb{Z}[X_1, \ldots, X_m]$. Write
$F_k P_l$ for the set of products $y z$ of a $k$-free number $y$ and a positive integer $z$
with fewer than $l$ distinct prime divisors. Then there are only finitely many pairs $(n, x)$
of a natural number $n$ and an integer $x$ such that $n! + 1 = x^2$ and
$x = x_1 \cdots x_m P(x_1, \ldots, x_m) + 1$ or $x = x_1 \cdots x_m P(x_1, \ldots, x_m) - 1$
for some $x_1, \ldots, x_m \in F_k P_l$.

Here $x$ ranges over the integers, since negating $x$ does not preserve the shape
$x_1 \cdots x_m P(x_1, \ldots, x_m) \pm 1$.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 2
(`integers-2025-A71-thm-2`). -/
public theorem brocardRamanujan_polynomial_powerFree_mul_fewPrimeFactors_finite
    {k l m : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l) (hm : 1 ≤ m) (P : MvPolynomial (Fin m) ℤ) :
    {p : ℕ × ℤ | ((p.1 ! : ℕ) : ℤ) + 1 = p.2 ^ 2 ∧
      ∃ xs : Fin m → ℕ, (∀ i, ∃ y z : ℕ, xs i = y * z ∧ y.IsPowerFree k ∧ 0 < z ∧
          z.primeFactors.card < l) ∧
        (p.2 = (∏ i, (xs i : ℤ)) * MvPolynomial.eval (fun i => (xs i : ℤ)) P + 1 ∨
          p.2 = (∏ i, (xs i : ℤ)) * MvPolynomial.eval (fun i => (xs i : ℤ)) P - 1)}.Finite := by
  classical
  let A : ℕ := ⌈Real.exp (3 * k / 2)⌉₊
  let B : ℕ := A * 2 ^ (l - 1)
  let C : ℕ := ∑ d ∈ P.support, (P.coeff d).natAbs
  let d : ℕ := m + P.totalDegree
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_le 2).trans hk
  have hA : 1 ≤ A := by
    rw [← Nat.cast_le (α := ℝ), Nat.cast_one]
    exact (Real.one_le_exp_iff.mpr (show 0 ≤ (3 : ℝ) * k / 2 by positivity)).trans
      (Nat.le_ceil _)
  have hB : 1 ≤ B := Nat.mul_pos hA (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Nat.eventually_mul_pow_lt_factorial_sub ((C + 1) ^ 2) ((B ^ d) ^ 2) 0)
  simp only [Nat.sub_zero] at hN
  let M : ℕ := (N + 1) ! + 1
  refine ((Set.finite_Iio (N + 1)).prod (Set.finite_Icc (-(M : ℤ)) M)).subset ?_
  rintro ⟨n, x⟩ ⟨hsol, xs, hxs, hx⟩
  have hsol' : ((n ! + 1 : ℕ) : ℤ) = x ^ 2 := by exact_mod_cast hsol
  have hsq : x.natAbs ^ 2 = n ! + 1 := by
    simpa only [Int.natAbs_pow, Int.natAbs_natCast] using congrArg Int.natAbs hsol'.symm
  have hn : n < N + 1 := by
    by_contra! hlarge
    have hn0 : 0 < n := by omega
    let q : ℤ := (∏ i, (xs i : ℤ)) * MvPolynomial.eval (fun i => (xs i : ℤ)) P
    change x = q + 1 ∨ x = q - 1 at hx
    have hq : q ∣ ((n ! : ℕ) : ℤ) := by
      have hfac : ((n ! : ℕ) : ℤ) = x ^ 2 - 1 := by omega
      rw [hfac]
      rcases hx with hx | hx
      · exact ⟨q + 2, by rw [hx]; ring⟩
      · exact ⟨q - 2, by rw [hx]; ring⟩
    have hxsB (i : Fin m) : xs i ≤ B ^ n := by
      have hdiv : xs i ∣ n ! := Int.natCast_dvd_natCast.mp
        ((Finset.dvd_prod_of_mem (fun j : Fin m ↦ (xs j : ℤ)) (Finset.mem_univ i)).trans
          ((dvd_mul_right _ _).trans hq))
      obtain ⟨y, z, hmul, hy, hz, hcard⟩ := hxs i
      rw [hmul] at hdiv ⊢
      have hyExp := le_exp_of_isPowerFree_dvd_factorial hn0 hy
        ((dvd_mul_right y z).trans hdiv)
      have hyA : (y : ℝ) ≤ (A : ℝ) ^ n := calc
        _ ≤ Real.exp (3 * n * k / 2) := hyExp
        _ = Real.exp (3 * k / 2) ^ n := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ (A : ℝ) ^ n := by gcongr; exact Nat.le_ceil _
      have hzBound := le_pow_of_dvd_factorial_of_primeFactors_card_le hz.ne'
        ((dvd_mul_left z y).trans hdiv) ((Nat.le_sub_iff_add_le (Nat.le_of_succ_le hl)).2 hcard)
      rw [mul_pow]
      exact Nat.mul_le_mul (by exact_mod_cast hyA) hzBound
    have hprod : (∏ i, (xs i : ℤ)).natAbs ≤ (B ^ n) ^ m := by
      simp only [Int.natAbs_prod, Int.natAbs_natCast]
      calc
        _ ≤ ∏ _i : Fin m, B ^ n := Finset.prod_le_prod fun i _ ↦ hxsB i
        _ = _ := by simp
    have hR : 1 ≤ B ^ n := Nat.pow_pos hB
    have hqB : q.natAbs ≤ C * (B ^ n) ^ d := by
      dsimp only [q]
      rw [Int.natAbs_mul]
      calc
        _ ≤ (B ^ n) ^ m * (C * (B ^ n) ^ P.totalDegree) :=
          Nat.mul_le_mul hprod (natAbs_eval_le P hR hxsB)
        _ = _ := by dsimp only [d]; rw [pow_add]; ac_rfl
    have hxq : x.natAbs ≤ q.natAbs + 1 := by
      rcases hx with hx | hx
      · rw [hx]
        simpa only [Int.natAbs_one] using Int.natAbs_add_le q 1
      · rw [hx]
        simpa only [sub_eq_add_neg, Int.natAbs_neg, Int.natAbs_one] using Int.natAbs_add_le q (-1)
    have hone : 1 ≤ (B ^ n) ^ d := by
      have hd : 1 ≤ d := hm.trans (Nat.le_add_right _ _)
      exact hR.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hR hd)
    have hxB : x.natAbs ≤ (C + 1) * (B ^ d) ^ n := calc
      _ ≤ C * (B ^ n) ^ d + 1 := hxq.trans (Nat.add_le_add_right hqB 1)
      _ ≤ (C + 1) * (B ^ n) ^ d := by rw [Nat.add_mul, one_mul]; exact Nat.add_le_add_left hone _
      _ = _ := by rw [pow_right_comm B n d]
    apply (not_le_of_gt (hN n (by omega)))
    calc
      n ! ≤ x.natAbs ^ 2 := by omega
      _ ≤ ((C + 1) * (B ^ d) ^ n) ^ 2 := Nat.pow_le_pow_left hxB _
      _ = _ := by rw [mul_pow, pow_right_comm (B ^ d) n 2]
  refine ⟨hn, abs_le.mp ?_⟩
  rw [← Int.natCast_natAbs]
  exact_mod_cast (calc
    x.natAbs ≤ x.natAbs ^ 2 := Nat.le_self_pow (by decide) _
    _ = n ! + 1 := hsq
    _ ≤ M := Nat.add_le_add_right (Nat.factorial_le hn.le) 1)

end MetaMathlibExt
