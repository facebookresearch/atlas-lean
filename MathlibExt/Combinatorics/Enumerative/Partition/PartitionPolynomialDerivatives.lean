/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private theorem deriv_sum_aux (k n : ℕ) (m : ℕ → ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * y ^ i) x =
      ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * (i.descFactorial n : ℝ) * x ^ (i - n) := by
  have hcd : ∀ i ∈ Finset.Icc 1 k,
      ContDiffAt ℝ (↑n) (fun y => (m i : ℝ) * y ^ i) x := by
    intro i _
    fun_prop
  have hpow : ∀ i ∈ Finset.Icc 1 k,
      ContDiffAt ℝ (↑n) (fun y : ℝ => y ^ i) x := by
    intro i _
    fun_prop
  have hfun : (fun y => ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * y ^ i) =
      ∑ i ∈ Finset.Icc 1 k, (fun y => (m i : ℝ) * y ^ i) := by
    funext y
    simp [Finset.sum_apply]
  rw [hfun, iteratedDeriv_sum hcd]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_const_mul _ (hpow i ‹_›)]
  rw [iteratedDeriv_pow]
  ring

private theorem stirling_cast_aux (i d : ℕ) :
    (i : ℝ) ^ d = ∑ j ∈ Finset.range (d + 1),
      (Nat.stirlingSecond d j : ℝ) * (i.descFactorial j : ℝ) := by
  have h := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial i d
  have h2 := congrArg (Nat.cast : ℕ → ℝ) h
  simp only [Nat.cast_pow, Nat.cast_sum, Nat.cast_mul] at h2
  exact h2

private theorem zpow_sub_mul_pow_aux (x : ℝ) (hx : x ≠ 0) (a : ℤ) (d : ℕ) :
    x ^ (a - (d : ℤ)) * x ^ d = x ^ a := by
  rw [← zpow_natCast x d, ← zpow_add₀ hx, sub_add_cancel]

/-- **Stirling recursion for derivatives, for arbitrary multiplicities.** Let $k$ and $d$ be
natural numbers, let $m \colon \mathbb{N} \to \mathbb{N}$, write $m_i = m(i)$, and let
$f(y) = \sum_{i=1}^{k} m_i y^i$ for real $y$. Then for every real $x \ne 0$,
$$f^{(d)}(x) = \sum_{i=1}^{k} i^d m_i x^{i-d} -
\sum_{j=0}^{d-1} S(d, j)\, x^{j-d} f^{(j)}(x),$$
where $S(d, j)$ are the Stirling numbers of the second kind and $f^{(j)}$ is the $j$th
derivative of $f$. No relation between $d$ and $k$ is assumed. -/
theorem partitionPolynomial_iteratedDeriv_eq_sum_stirlingSecond_general
    (k d : ℕ) (m : ℕ → ℕ) (x : ℝ) (hx : x ≠ 0) :
    let f : ℝ → ℝ := fun y => ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * y ^ i
    iteratedDeriv d f x =
      (∑ i ∈ Finset.Icc 1 k,
          (i : ℝ) ^ d * (m i : ℝ) * x ^ ((i : ℤ) - d)) -
        ∑ j ∈ Finset.range d,
          (Nat.stirlingSecond d j : ℝ) * x ^ ((j : ℤ) - d) *
            iteratedDeriv j f x := by
  change iteratedDeriv d (fun y => ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * y ^ i) x = _
  have hD : iteratedDeriv d (fun y => ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * y ^ i) x =
      ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * (i.descFactorial d : ℝ) * x ^ (i - d) :=
    deriv_sum_aux k d m x
  have hDj : ∀ j ∈ Finset.range d,
      iteratedDeriv j (fun y => ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * y ^ i) x =
      ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * (i.descFactorial j : ℝ) * x ^ (i - j) := by
    intro j _
    exact deriv_sum_aux k j m x
  rw [hD]
  have hxpow : (x : ℝ) ^ d ≠ 0 := pow_ne_zero d hx
  apply mul_right_cancel₀ hxpow
  have hLHS : (∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * (i.descFactorial d : ℝ) * x ^ (i - d)) * x ^ d =
      ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * (i.descFactorial d : ℝ) * (x ^ (i - d) * x ^ d) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hA : (∑ i ∈ Finset.Icc 1 k, (i : ℝ) ^ d * (m i : ℝ) * x ^ ((i : ℤ) - d)) * x ^ d =
      ∑ i ∈ Finset.Icc 1 k, (i : ℝ) ^ d * (m i : ℝ) * x ^ i := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hz : x ^ ((i : ℤ) - (d : ℤ)) * x ^ d = x ^ (i : ℤ) := zpow_sub_mul_pow_aux x hx _ d
    have hz2 : x ^ (i : ℤ) = x ^ i := zpow_natCast x i
    calc (i : ℝ) ^ d * (m i : ℝ) * x ^ ((i : ℤ) - ↑d) * x ^ d
        = (i : ℝ) ^ d * (m i : ℝ) * (x ^ ((i : ℤ) - ↑d) * x ^ d) := by ring
      _ = (i : ℝ) ^ d * (m i : ℝ) * x ^ (i : ℤ) := by rw [hz]
      _ = (i : ℝ) ^ d * (m i : ℝ) * x ^ i := by rw [hz2]
  have hBper : ∀ j ∈ Finset.range d,
      ((Nat.stirlingSecond d j : ℝ) * x ^ ((j : ℤ) - (d : ℤ)) *
        iteratedDeriv j (fun y => ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * y ^ i) x) * x ^ d =
      (Nat.stirlingSecond d j : ℝ) * x ^ j *
        (∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * (i.descFactorial j : ℝ) * x ^ (i - j)) := by
    intro j _
    rw [hDj j ‹_›]
    have hz : x ^ ((j : ℤ) - (d : ℤ)) * x ^ d = x ^ (j : ℤ) := zpow_sub_mul_pow_aux x hx _ d
    have hz2 : x ^ (j : ℤ) = x ^ j := zpow_natCast x j
    calc (Nat.stirlingSecond d j : ℝ) * x ^ ((j : ℤ) - ↑d) *
          (∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * ↑(i.descFactorial j) * x ^ (i - j)) * x ^ d
        = (Nat.stirlingSecond d j : ℝ) * (x ^ ((j : ℤ) - ↑d) * x ^ d) *
          (∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * ↑(i.descFactorial j) * x ^ (i - j)) := by ring
      _ = (Nat.stirlingSecond d j : ℝ) * x ^ (j : ℤ) *
          (∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * ↑(i.descFactorial j) * x ^ (i - j)) := by rw [hz]
      _ = (Nat.stirlingSecond d j : ℝ) * x ^ j *
          (∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * ↑(i.descFactorial j) * x ^ (i - j)) := by rw [hz2]
  have hB : (∑ j ∈ Finset.range d, (Nat.stirlingSecond d j : ℝ) * x ^ ((j : ℤ) - d) *
        iteratedDeriv j (fun y => ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * y ^ i) x) * x ^ d =
      ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) *
        (∑ j ∈ Finset.range d,
          (Nat.stirlingSecond d j : ℝ) * (i.descFactorial j : ℝ) * (x ^ j * x ^ (i - j))) := by
    rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun j hj => hBper j hj)]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hLHS, sub_mul, hA, hB, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hpow1 : x ^ (i - d) * x ^ d = x ^ i ∨ (i.descFactorial d = 0) := by
    by_cases hle : d ≤ i
    · left
      have : i - d + d = i := Nat.sub_add_cancel hle
      calc x ^ (i - d) * x ^ d = x ^ (i - d + d) := by rw [pow_add]
        _ = x ^ i := by rw [this]
    · right
      exact (Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hle))
  have hpow2 : ∀ j ∈ Finset.range d, x ^ j * x ^ (i - j) = x ^ i ∨ (i.descFactorial j = 0) := by
    intro j _
    by_cases hle : j ≤ i
    · left
      have : j + (i - j) = i := Nat.add_sub_cancel' hle
      calc x ^ j * x ^ (i - j) = x ^ (j + (i - j)) := by rw [pow_add]
        _ = x ^ i := by rw [this]
    · right
      exact (Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hle))
  have hstirl := stirling_cast_aux i d
  rw [Finset.sum_range_succ] at hstirl
  simp only [Nat.stirlingSecond_self, Nat.cast_one, one_mul] at hstirl
  have hdesc : (m i : ℝ) * (i.descFactorial d : ℝ) * (x ^ (i - d) * x ^ d) =
      (m i : ℝ) * (i.descFactorial d : ℝ) * x ^ i := by
    rcases hpow1 with h | h
    · rw [h]
    · rw [h]; simp
  have hsum : (m i : ℝ) * (∑ j ∈ Finset.range d,
        (Nat.stirlingSecond d j : ℝ) * (i.descFactorial j : ℝ) * (x ^ j * x ^ (i - j))) =
      (m i : ℝ) * (∑ j ∈ Finset.range d,
        (Nat.stirlingSecond d j : ℝ) * (i.descFactorial j : ℝ)) * x ^ i := by
    have e1 : (m i : ℝ) * (∑ j ∈ Finset.range d,
          (Nat.stirlingSecond d j : ℝ) * (i.descFactorial j : ℝ) * (x ^ j * x ^ (i - j))) =
        ∑ j ∈ Finset.range d, (m i : ℝ) *
          ((Nat.stirlingSecond d j : ℝ) * (i.descFactorial j : ℝ) * (x ^ j * x ^ (i - j))) :=
      Finset.mul_sum _ _ _
    have e2 : (m i : ℝ) * (∑ j ∈ Finset.range d,
          (Nat.stirlingSecond d j : ℝ) * (i.descFactorial j : ℝ)) * x ^ i =
        ∑ j ∈ Finset.range d,
          (m i : ℝ) * ((Nat.stirlingSecond d j : ℝ) * (i.descFactorial j : ℝ)) * x ^ i := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [e1, e2]
    apply Finset.sum_congr rfl
    intro j hj
    rcases hpow2 j hj with h | h
    · rw [h]; ring
    · simp [h]
  have hcomb : (i : ℝ) ^ d * (m i : ℝ) * x ^ i =
      (m i : ℝ) * (i.descFactorial d : ℝ) * x ^ i +
      ((m i : ℝ) * (∑ j ∈ Finset.range d,
        (Nat.stirlingSecond d j : ℝ) * (i.descFactorial j : ℝ)) * x ^ i) := by
    have : (i : ℝ) ^ d = (∑ j ∈ Finset.range d,
        (Nat.stirlingSecond d j : ℝ) * (i.descFactorial j : ℝ)) + (i.descFactorial d : ℝ) := by
      exact hstirl
    rw [this]; ring
  rw [hdesc, hsum]
  rw [hcomb]; ring


set_option linter.unusedVariables false in
/--
**Derivatives of the partition polynomial via Stirling numbers.** Let $k \ge 1$, let
$m \colon \mathbb{N} \to \mathbb{N}$, and write $m_i = m(i)$. Assume $m_k \ne 0$ and $m_i = 0$
for every $i$ outside $\{1, \dots, k\}$, so that $m$ lists the part multiplicities of a
partition $\lambda = \langle 1^{m_1}, \dots, k^{m_k} \rangle$ with largest part $k$. Let
$f(y) = \sum_{i=1}^{k} m_i y^i$ for real $y$. Then for every natural number $d \le k$ and every
real $x \ne 0$,
$$f^{(d)}(x) = \sum_{i=1}^{k} i^d m_i x^{i-d} -
\sum_{j=0}^{d-1} S(d, j)\, x^{j-d} f^{(j)}(x),$$
where $S(d, j)$ are the Stirling numbers of the second kind and $f^{(j)}$ is the $j$th
derivative of $f$; for $d = 0$ the second sum is empty.

Proves `Wanted` entry `partitionPolynomial_iteratedDeriv_eq_sum_stirlingSecond`.

Source: Madeline Locus Dawsey, Tyler Russell, and Dannie Urban, "Derivatives and Integrals
of Polynomials Associated with Integer Partitions," Journal of Integer Sequences 25 (2022),
Article 22.5.1, Theorem 1 (label `derivativethm`), lines 108–114,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Dawsey/dawsey3.tex>.
-/
@[nolint unusedArguments]
theorem partitionPolynomial_iteratedDeriv_eq_sum_stirlingSecond
    (k d : ℕ) (m : ℕ → ℕ) (hk : 0 < k)
    (hm_top : m k ≠ 0)
    (hm_support : ∀ i, m i ≠ 0 → i ∈ Finset.Icc 1 k)
    (x : ℝ) (hx : x ≠ 0) (hd : d ≤ k) :
    let f : ℝ → ℝ := fun y => ∑ i ∈ Finset.Icc 1 k, (m i : ℝ) * y ^ i
    iteratedDeriv d f x =
      (∑ i ∈ Finset.Icc 1 k,
          (i : ℝ) ^ d * (m i : ℝ) * x ^ ((i : ℤ) - d)) -
        ∑ j ∈ Finset.range d,
          (Nat.stirlingSecond d j : ℝ) * x ^ ((j : ℤ) - d) *
            iteratedDeriv j f x := by
  exact partitionPolynomial_iteratedDeriv_eq_sum_stirlingSecond_general k d m x hx

end MetaMathlibExt
