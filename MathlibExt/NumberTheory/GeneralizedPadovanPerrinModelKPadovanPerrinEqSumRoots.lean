/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Algebra.Polynomial.Roots
public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinCompanion
public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinExpansion
public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinModel
public import MathlibExt.NumberTheory.PadovanPerrinFundamentalProduct
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Root formula for the `k`-Padovan–Perrin numbers

For an integer `k ≥ 2`, let `P(z) = z ^ 3 - z - k` and let `v : ℕ → ℂ` solve the
Padovan–Perrin recurrence `v (n + 3) = v (n + 1) + k * v n`. Then for every `n ≥ 3`,
`v n` equals the sum over the complex roots `λ` of `P` of
`(A₀ * λ ^ (n - 1) + A₁ * λ ^ (n - 2) + A₂ * λ ^ (n - 3)) / P′ λ`, where
`A₀ = k * v 0 + v 1`, `A₁ = k * v 1 + v 2` and `A₂ = k * v 2`
(`kPadovanPerrin_eq_sum_roots`).

The polynomial `P` has three distinct roots by
`padovanPerrin_charPoly_separable_of_p_eq_one`. The root sum satisfies the same
recurrence as `v` and takes the same values at `3`, `4` and `5`, using
`∑ λ ^ j / P′ λ = 0` for `j = 0, 1` and `= 1` for `j = 2` over the three roots.

## References

* Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
  *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*,
  INTEGERS 24 (2024), Article A49.
-/

@[expose] public section

namespace MetaMathlibExt

open Polynomial

private theorem kPadovanPerrin_separable_aux (k : ℕ) (hk : 2 ≤ k) :
    (X ^ 3 - X - C (k : ℂ)).Separable := by
  have hkq : (2 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hsq : (4 : ℚ) ≤ (k : ℚ) ^ 2 := by nlinarith [hkq]
  have h := padovanPerrin_charPoly_separable_of_p_eq_one 1 k 2 zero_lt_one (by omega) zero_lt_two
    (by norm_num; nlinarith [hsq])
  rwa [show (2 : ℕ) + 1 = 3 by rfl, Nat.cast_one, C_1, one_mul] at h

/-- **Root formula for the $k$-Padovan–Perrin numbers.** Let $k \ge 2$ be an integer, let
$P(z) = z^3 - z - k$, and let $v \colon \mathbb{N} \to \mathbb{C}$ satisfy
$v(n + 3) = v(n + 1) + k\,v(n)$ for every $n$, that is, $v$ solves the Padovan–Perrin recurrence
with $k_1 = 1$, $k_2 = k$, $p = 1$, $s = 2$. Put $A_0 = k\,v(0) + v(1)$, $A_1 = k\,v(1) + v(2)$
and $A_2 = k\,v(2)$. Then for every $n \ge 3$,
$$v(n) = \sum_\lambda \frac{A_0\lambda^{n-1} + A_1\lambda^{n-2} + A_2\lambda^{n-3}}{P'(\lambda)},$$
where $\lambda$ runs over the complex roots of $P$ counted with multiplicity.

Since $27 k^2 - 4 \neq 0$, the roots of $P$ are distinct. The paper prints the middle coefficient
as $k\,v(1)$; $k\,v(1) + v(2)$ is the coefficient $A_1$ of its Theorem 3, and the printed form
fails already for $k = 2$, $(v(0), v(1), v(2)) = (0, 0, 1)$, $n = 4$, where it gives $0$ while
$v(4) = 1$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 10 (`integers-2024-A49-prop-10`). -/
public theorem kPadovanPerrin_eq_sum_roots (k : ℕ) (hk : 2 ≤ k) (v : ℕ → ℂ)
    (hv : (padovanPerrinRecurrence 1 (k : ℂ) 1 2).IsSolution v) (n : ℕ) (hn : 3 ≤ n) :
    v n = ((X ^ 3 - X - C (k : ℂ)).roots.map fun x =>
      (((k : ℂ) * v 0 + v 1) * x ^ (n - 1) + ((k : ℂ) * v 1 + v 2) * x ^ (n - 2) +
          (k : ℂ) * v 2 * x ^ (n - 3)) /
        (derivative (X ^ 3 - X - C (k : ℂ))).eval x).sum := by
  set P : ℂ[X] := X ^ 3 - X - C (k : ℂ) with hP
  set A₀ : ℂ := (k : ℂ) * v 0 + v 1 with hA₀
  set A₁ : ℂ := (k : ℂ) * v 1 + v 2 with hA₁
  set A₂ : ℂ := (k : ℂ) * v 2 with hA₂
  have hv3 : ∀ m, v (m + 3) = v (m + 1) + (k : ℂ) * v m := by
    intro m
    have h := (padovanPerrinRecurrence_isSolution_iff 1 (k : ℂ) 1 2 (by norm_num) v).mp hv m
    simpa using h
  have hPmonic : P.Monic := by
    rw [hP]
    have heq : (X ^ 3 - X - C (k : ℂ)) = X ^ 3 + (-X - C (k : ℂ)) := by ring
    rw [heq]
    apply monic_X_pow_add
    compute_degree
    decide
  have hPdeg : P.natDegree = 3 := by
    rw [hP]
    have heq : (X ^ 3 - X - C (k : ℂ)) = X ^ 3 + (-X - C (k : ℂ)) := by ring
    rw [heq, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · have h1 : (-X - C (k : ℂ)).natDegree ≤ 1 := by compute_degree
      have h2 : (X ^ 3 : ℂ[X]).natDegree = 3 := by simp
      omega
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hPsplits : P.Splits := IsAlgClosed.splits P
  have hPsep : P.Separable := by
    rw [hP]
    exact kPadovanPerrin_separable_aux k hk
  have hcard : P.roots.card = 3 := by
    rw [← hPsplits.natDegree_eq_card_roots, hPdeg]
  have hnodup : P.roots.Nodup := Polynomial.nodup_roots hPsep
  obtain ⟨a, b, c, habc⟩ := Multiset.card_eq_three.mp hcard
  have hnodup3 : ({a, b, c} : Multiset ℂ).Nodup := by rw [← habc]; exact hnodup
  obtain ⟨⟨hab, hac⟩, hbc⟩ := (by simpa using hnodup3 : (a ≠ b ∧ a ≠ c) ∧ b ≠ c)
  have hmem_a : a ∈ P.roots := by rw [habc]; simp
  have hmem_b : b ∈ P.roots := by rw [habc]; simp
  have hmem_c : c ∈ P.roots := by rw [habc]; simp
  have hroot : ∀ x ∈ P.roots, x ^ 3 = x + (k : ℂ) := by
    intro x hx
    have hr : P.IsRoot x := (Polynomial.mem_roots hPne).mp hx
    have hr2 : x ^ 3 - x - (k : ℂ) = 0 := by
      have hrr := hr
      rw [hP] at hrr
      simpa [Polynomial.IsRoot, eval_sub, eval_pow] using hrr
    linear_combination hr2
  have ha3 : a ^ 3 = a + (k : ℂ) := hroot a hmem_a
  have hb3 : b ^ 3 = b + (k : ℂ) := hroot b hmem_b
  have hc3 : c ^ 3 = c + (k : ℂ) := hroot c hmem_c
  have hPa : (derivative P).eval a = (a - b) * (a - c) := by
    have h := Polynomial.Splits.eval_root_derivative hPsplits hPmonic hmem_a
    rw [habc] at h
    have herase : (({a, b, c} : Multiset ℂ).erase a) = {b, c} := by
      simp [Multiset.erase_cons_head]
    rw [herase] at h
    simpa [Multiset.map_cons, Multiset.prod_cons] using h
  have hPb : (derivative P).eval b = (b - a) * (b - c) := by
    have h := Polynomial.Splits.eval_root_derivative hPsplits hPmonic hmem_b
    rw [habc] at h
    have herase : (({a, b, c} : Multiset ℂ).erase b) = {a, c} := by
      simp [Multiset.erase_cons_head, Multiset.erase_cons_tail, hab]
    rw [herase] at h
    simpa [Multiset.map_cons, Multiset.prod_cons] using h
  have hPc : (derivative P).eval c = (c - a) * (c - b) := by
    have h := Polynomial.Splits.eval_root_derivative hPsplits hPmonic hmem_c
    rw [habc] at h
    have herase : (({a, b, c} : Multiset ℂ).erase c) = {a, b} := by
      simp [Multiset.erase_cons_tail, hac, hbc]
    rw [herase] at h
    simpa [Multiset.map_cons, Multiset.prod_cons] using h
  have hsum : ∀ f : ℂ → ℂ, (P.roots.map f).sum = f a + f b + f c := by
    intro f
    rw [habc]
    simp [Multiset.map_cons, Multiset.sum_cons, add_assoc]
  have hv3_0 : v 3 = A₀ := by
    have h := hv3 0
    simpa [hA₀, add_comm] using h
  have hv4 : v 4 = A₁ := by
    have h := hv3 1
    simpa [hA₁, add_comm] using h
  have hv5 : v 5 = A₀ + A₂ := by
    have h := hv3 2
    simp only [show 2 + 3 = 5 by norm_num, show 2 + 1 = 3 by norm_num] at h
    rw [hv3_0] at h
    simpa [hA₂] using h
  have hE0 : (P.roots.map fun x => (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ 0 / (derivative P).eval x).sum
      = A₀ := by
    rw [hsum]
    simp only [pow_zero, mul_one]
    rw [hPa, hPb, hPc]
    field_simp
    ring
  have hE1 : (P.roots.map fun x => (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ 1 / (derivative P).eval x).sum
      = A₁ := by
    rw [hsum]
    have e1 : ∀ x : ℂ, x ^ 3 = x + (k : ℂ) →
        (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ 1 / (derivative P).eval x
          = (A₁ * x ^ 2 + (A₀ + A₂) * x + A₀ * (k : ℂ)) / (derivative P).eval x := by
      intro x hx3
      congr 1
      linear_combination A₀ * hx3
    rw [e1 a ha3, e1 b hb3, e1 c hc3, hPa, hPb, hPc]
    field_simp
    ring
  have hE2 : (P.roots.map fun x => (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ 2 / (derivative P).eval x).sum
      = A₀ + A₂ := by
    rw [hsum]
    have e2 : ∀ x : ℂ, x ^ 3 = x + (k : ℂ) →
        (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ 2 / (derivative P).eval x
          = ((A₀ + A₂) * x ^ 2 + (A₀ * (k : ℂ) + A₁) * x + A₁ * (k : ℂ)) /
            (derivative P).eval x := by
      intro x hx3
      congr 1
      linear_combination (A₀ * x) * hx3 + A₁ * hx3
    rw [e2 a ha3, e2 b hb3, e2 c hc3, hPa, hPb, hPc]
    field_simp
    ring
  have hSrec : ∀ m, (P.roots.map fun x => (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ (m + 3) /
      (derivative P).eval x).sum
      = (P.roots.map fun x => (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ (m + 1) /
        (derivative P).eval x).sum
      + (k : ℂ) * (P.roots.map fun x => (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ m /
        (derivative P).eval x).sum := by
    intro m
    rw [hsum, hsum, hsum]
    have e : ∀ x : ℂ, x ^ 3 = x + (k : ℂ) →
        (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ (m + 3) / (derivative P).eval x
          = (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ (m + 1) / (derivative P).eval x
          + (k : ℂ) * ((A₀ * x ^ 2 + A₁ * x + A₂) * x ^ m / (derivative P).eval x) := by
      intro x hx3
      have hpow : x ^ (m + 3) = x ^ (m + 1) + (k : ℂ) * x ^ m := by
        linear_combination x ^ m * hx3
      rw [hpow]
      ring
    rw [e a ha3, e b hb3, e c hc3]
    ring
  have hu_sol : (padovanPerrinRecurrence 1 (k : ℂ) 1 2).IsSolution
      (fun m => (P.roots.map fun x => (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ m /
        (derivative P).eval x).sum) := by
    rw [padovanPerrinRecurrence_isSolution_iff _ _ _ _ (by norm_num)]
    intro m
    have h := hSrec m
    simpa using h
  have hw_sol : (padovanPerrinRecurrence 1 (k : ℂ) 1 2).IsSolution (fun m => v (m + 3)) := by
    rw [padovanPerrinRecurrence_isSolution_iff _ _ _ _ (by norm_num)]
    intro m
    have h := hv3 (m + 3)
    simpa [add_assoc] using h
  have hagree : Set.EqOn (fun m => v (m + 3))
      (fun m => (P.roots.map fun x => (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ m /
        (derivative P).eval x).sum)
      ↑(Finset.range (padovanPerrinRecurrence 1 (k : ℂ) 1 2).order) := by
    intro m hm
    simp only [Finset.mem_coe, Finset.mem_range] at hm
    have hm3 : m < 3 := hm
    interval_cases m
    · simpa using hv3_0.trans hE0.symm
    · simpa using hv4.trans hE1.symm
    · simpa using hv5.trans hE2.symm
  have hfun := (LinearRecurrence.eq_iff_eqOn_range_order _ _ _ hw_sol hu_sol).2 hagree
  have hcongr2 : v (n - 3 + 3)
      = (P.roots.map fun x => (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ (n - 3) /
        (derivative P).eval x).sum := congrFun hfun (n - 3)
  have hn3 : n - 3 + 3 = n := by omega
  rw [hn3] at hcongr2
  refine hcongr2.trans ?_
  have hterm : ∀ x ∈ P.roots, (A₀ * x ^ 2 + A₁ * x + A₂) * x ^ (n - 3) / (derivative P).eval x
      = (A₀ * x ^ (n - 1) + A₁ * x ^ (n - 2) + A₂ * x ^ (n - 3)) / (derivative P).eval x := by
    intro x _
    congr 1
    have e1 : n - 1 = 2 + (n - 3) := by omega
    have e2 : n - 2 = 1 + (n - 3) := by omega
    rw [e1, e2, pow_add, pow_add]
    ring
  rw [Multiset.map_congr rfl hterm]

end MetaMathlibExt
