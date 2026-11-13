/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.LinearCombination

/-! Broder's expansion formula for r-Stirling numbers of the first kind.

Source: A. Z. Broder, "The r-Stirling numbers",
Stanford Computer Science Report STAN-CS-82-949 (December 1982),
PDF page 16 / printed page 13, Equation (43);
later published in Discrete Mathematics 49 (1984), 241-259,
DOI 10.1016/0012-365X(84)90161-4.

Equation (24) (PDF page 12 / printed page 9):
  ∑ k, [n,k]_r z^k = z^r (z+r)(z+r+1)...(z+n-1), n ≥ r > 0.
Equation (43): (-1)^r [n,m]_r = ∑ k, [n,m-r+k] {k-1,r-1} (-1)^k, n ≥ r ≥ 1.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem stirlingFirst_step (n j : ℕ) (hn : 1 ≤ n) :
    Nat.stirlingFirst (n + 1) j =
      Nat.stirlingFirst n (j - 1) + n * Nat.stirlingFirst n j := by
  cases j with
  | zero =>
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [show (0 : ℕ) - 1 = 0 from rfl]
    simp
  | succ j =>
    rw [Nat.stirlingFirst_succ_succ, Nat.add_sub_cancel]
    ring

private theorem shifted_stirling_sum (N : ℕ) (F : ℕ → ℤ) :
    ∑ j ∈ Finset.range (N + 1), (Nat.stirlingFirst N (j + 1) : ℤ) * (-1 : ℤ) ^ j * F (j + 1) =
      (Nat.stirlingFirst N 0 : ℤ) * F 0 -
        ∑ i ∈ Finset.range (N + 1), (Nat.stirlingFirst N i : ℤ) * (-1 : ℤ) ^ i * F i := by
  have e1 : ∑ i ∈ Finset.range (N + 2), (Nat.stirlingFirst N i : ℤ) * (-1 : ℤ) ^ i * F i =
      -(∑ j ∈ Finset.range (N + 1), (Nat.stirlingFirst N (j + 1) : ℤ) * (-1 : ℤ) ^ j * F (j + 1)) +
        (Nat.stirlingFirst N 0 : ℤ) * F 0 := by
    rw [Finset.sum_range_succ', ← Finset.sum_neg_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    · simp
  have e2 : ∑ i ∈ Finset.range (N + 2), (Nat.stirlingFirst N i : ℤ) * (-1 : ℤ) ^ i * F i =
      (∑ i ∈ Finset.range (N + 1), (Nat.stirlingFirst N i : ℤ) * (-1 : ℤ) ^ i * F i) := by
    rw [Finset.sum_range_succ]
    simp [Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self N)]
  linear_combination e1 - e2

private theorem vanish_stirling_sum : ∀ (N t s : ℕ), t < N →
    ∑ j ∈ Finset.range (N + 1), (Nat.stirlingFirst N j : ℤ) * (-1 : ℤ) ^ j *
      (Nat.stirlingSecond (j + s) t : ℤ) = 0 := by
  intro N
  induction N with
  | zero =>
    intro t s ht
    exact absurd ht (Nat.not_lt_zero t)
  | succ N ih =>
    intro t s ht
    rw [Finset.sum_range_succ']
    have hf0 : (Nat.stirlingFirst (N + 1) 0 : ℤ) * (-1 : ℤ) ^ 0 *
        (Nat.stirlingSecond (0 + s) t : ℤ) = 0 := by simp
    rw [hf0, add_zero]
    by_cases ht0 : t = 0
    · subst ht0
      apply Finset.sum_eq_zero
      intro j _
      have e : (j + 1) + s = (j + s) + 1 := by omega
      rw [e]
      simp
    · obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht0
      by_cases hN0 : N = 0
      · subst hN0
        omega
      · obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0
        have hc0 : (Nat.stirlingFirst (N' + 1) 0 : ℤ) = 0 := by simp
        have hC0 : (∑ j ∈ Finset.range (N' + 1 + 1),
            (Nat.stirlingFirst (N' + 1) j : ℤ) * (-1 : ℤ) ^ j *
              (Nat.stirlingSecond (j + s) t' : ℤ)) = 0 :=
          ih t' s (by omega)
        have term : ∀ j : ℕ,
            (Nat.stirlingFirst (N' + 1 + 1) (j + 1) : ℤ) * (-1 : ℤ) ^ (j + 1) *
              (Nat.stirlingSecond ((j + 1) + s) (t' + 1) : ℤ) =
              -((N' + 1 : ℤ) *
                ((Nat.stirlingFirst (N' + 1) (j + 1) : ℤ) * (-1 : ℤ) ^ j *
                  (Nat.stirlingSecond ((j + 1) + s) (t' + 1) : ℤ)) +
                (Nat.stirlingFirst (N' + 1) j : ℤ) * (-1 : ℤ) ^ j *
                  (Nat.stirlingSecond ((j + 1) + s) (t' + 1) : ℤ)) := by
          intro j
          rw [Nat.stirlingFirst_succ_succ]
          push_cast
          rw [pow_succ]
          ring
        have hsum : (∑ j ∈ Finset.range (N' + 1 + 1),
              (Nat.stirlingFirst (N' + 1 + 1) (j + 1) : ℤ) * (-1 : ℤ) ^ (j + 1) *
                (Nat.stirlingSecond ((j + 1) + s) (t' + 1) : ℤ)) =
            -((N' + 1 : ℤ) *
              (∑ j ∈ Finset.range (N' + 1 + 1),
                (Nat.stirlingFirst (N' + 1) (j + 1) : ℤ) * (-1 : ℤ) ^ j *
                  (Nat.stirlingSecond ((j + 1) + s) (t' + 1) : ℤ)) +
              (∑ j ∈ Finset.range (N' + 1 + 1),
                (Nat.stirlingFirst (N' + 1) j : ℤ) * (-1 : ℤ) ^ j *
                  (Nat.stirlingSecond ((j + 1) + s) (t' + 1) : ℤ))) := by
          have hcongr := Finset.sum_congr (s₁ := Finset.range (N' + 1 + 1)) rfl
            (fun j _ => term j)
          rw [hcongr, Finset.sum_neg_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum]
        have hA1 : (∑ j ∈ Finset.range (N' + 1 + 1),
              (Nat.stirlingFirst (N' + 1) (j + 1) : ℤ) * (-1 : ℤ) ^ j *
                (Nat.stirlingSecond ((j + 1) + s) (t' + 1) : ℤ)) =
            (Nat.stirlingFirst (N' + 1) 0 : ℤ) *
              (Nat.stirlingSecond (0 + s) (t' + 1) : ℤ) -
              (∑ j ∈ Finset.range (N' + 1 + 1),
                (Nat.stirlingFirst (N' + 1) j : ℤ) * (-1 : ℤ) ^ j *
                  (Nat.stirlingSecond (j + s) (t' + 1) : ℤ)) :=
          shifted_stirling_sum (N' + 1)
            (fun i => (Nat.stirlingSecond (i + s) (t' + 1) : ℤ))
        have esh : ∀ j, (j + 1) + s = (j + s) + 1 := fun j => by omega
        have srec : ∀ j : ℕ,
            (Nat.stirlingSecond ((j + 1) + s) (t' + 1) : ℤ) =
              (t' + 1 : ℤ) * (Nat.stirlingSecond (j + s) (t' + 1) : ℤ) +
                (Nat.stirlingSecond (j + s) t' : ℤ) := by
          intro j
          rw [esh j, Nat.stirlingSecond_succ_succ]
          push_cast
          ring
        have hA0 : (∑ j ∈ Finset.range (N' + 1 + 1),
              (Nat.stirlingFirst (N' + 1) j : ℤ) * (-1 : ℤ) ^ j *
                (Nat.stirlingSecond ((j + 1) + s) (t' + 1) : ℤ)) =
            (t' + 1 : ℤ) *
              (∑ j ∈ Finset.range (N' + 1 + 1),
                (Nat.stirlingFirst (N' + 1) j : ℤ) * (-1 : ℤ) ^ j *
                  (Nat.stirlingSecond (j + s) (t' + 1) : ℤ)) +
              (∑ j ∈ Finset.range (N' + 1 + 1),
                (Nat.stirlingFirst (N' + 1) j : ℤ) * (-1 : ℤ) ^ j *
                  (Nat.stirlingSecond (j + s) t' : ℤ)) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [srec j]
          ring
        have hD1 : (Nat.stirlingFirst (N' + 1) 0 : ℤ) *
            (Nat.stirlingSecond (0 + s) (t' + 1) : ℤ) = 0 := by
          rw [hc0, zero_mul]
        rw [hsum, hA1, hA0, hD1, hC0]
        by_cases hlt : t' + 1 < N' + 1
        · have hB0 : (∑ j ∈ Finset.range (N' + 1 + 1),
              (Nat.stirlingFirst (N' + 1) j : ℤ) * (-1 : ℤ) ^ j *
                (Nat.stirlingSecond (j + s) (t' + 1) : ℤ)) = 0 :=
            ih (t' + 1) s hlt
          rw [hB0]
          ring
        · have hNT : (↑N' + 1 : ℤ) = (↑t' + 1 : ℤ) := by
            exact_mod_cast (by omega : N' + 1 = t' + 1)
          rw [hNT]
          ring

/-- **Unsigned r-Stirling numbers of the first kind.** For natural numbers $n$, $m$ and $r$, the
unsigned $r$-Stirling number of the first kind $[n, m]_r$ is the coefficient of $x^m$ in the
polynomial with natural-number coefficients
$$x^r \prod_{r \le k < n} (x + k).$$
For $n \ge r$ this is Broder's characterization
$\sum_m [n, m]_r \, x^m = x^r (x+r)(x+r+1) \cdots (x+n-1)$. For $n < r$ the product is empty, so
the polynomial is $x^r$.

Source: A. Z. Broder, "The r-Stirling numbers", Stanford Computer Science Report STAN-CS-82-949
(December 1982), PDF page 12 / printed page 9, Equation (24);
journal version: Discrete Mathematics 49 (1984), 241-259,
DOI 10.1016/0012-365X(84)90161-4. -/
noncomputable def rStirlingFirst (n m r : ℕ) : ℕ :=
  Polynomial.coeff
    ((Polynomial.X : Polynomial ℕ) ^ r *
      Finset.prod (Finset.Ico r n)
        (fun k => (Polynomial.X : Polynomial ℕ) + Polynomial.C k)) m

/-- **Initial row of the r-Stirling numbers of the first kind.** For all natural numbers $m$ and
$r$, the unsigned $r$-Stirling number of the first kind $[r, m]_r$ equals $1$ if $m = r$ and $0$
otherwise: when the first index equals $r$, the product in the definition is empty, so the
polynomial is $x^r$. -/
theorem rStirlingFirst_self (m r : ℕ) :
    rStirlingFirst r m r = if m = r then 1 else 0 := by
  unfold rStirlingFirst
  rw [Finset.Ico_self, Finset.prod_empty, mul_one]
  exact Polynomial.coeff_X_pow r m

/-- **Vanishing of the r-Stirling numbers of the first kind with second index zero.** For all
natural numbers $N$ and $r$ with $r \ge 1$, the unsigned $r$-Stirling number of the first kind
$[N, 0]_r$ is $0$: the defining polynomial is divisible by $x$, so its constant coefficient
vanishes. -/
theorem rStirlingFirst_zero_of_pos (N r : ℕ) (hr : 1 ≤ r) :
    rStirlingFirst N 0 r = 0 := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  unfold rStirlingFirst
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp

/-- **Recurrence for the r-Stirling numbers of the first kind.** For natural numbers $n$, $m$ and
$r$ with $1 \le r \le n$, the unsigned $r$-Stirling numbers of the first kind $[n, m]_r$ satisfy
$[n+1, m]_r = [n, m-1]_r + n \, [n, m]_r$, where for $m = 0$ the term $[n, m-1]_r$ is read as
$[n, 0]_r$. -/
theorem rStirlingFirst_succ (n m r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    rStirlingFirst (n + 1) m r =
      rStirlingFirst n (m - 1) r + n * rStirlingFirst n m r := by
  have hprod : (∏ k ∈ Finset.Ico r (n + 1),
        ((Polynomial.X : Polynomial ℕ) + Polynomial.C k)) =
      (∏ k ∈ Finset.Ico r n,
        ((Polynomial.X : Polynomial ℕ) + Polynomial.C k)) *
        ((Polynomial.X : Polynomial ℕ) + Polynomial.C n) :=
    Finset.prod_Ico_succ_top hrn _
  have hP : ((Polynomial.X : Polynomial ℕ) ^ r *
      ∏ k ∈ Finset.Ico r (n + 1),
        ((Polynomial.X : Polynomial ℕ) + Polynomial.C k)) =
      ((Polynomial.X : Polynomial ℕ) ^ r *
        ∏ k ∈ Finset.Ico r n,
          ((Polynomial.X : Polynomial ℕ) + Polynomial.C k)) *
        ((Polynomial.X : Polynomial ℕ) + Polynomial.C n) := by
    rw [hprod]
    ring
  have hLHS : rStirlingFirst (n + 1) m r =
      (((Polynomial.X : Polynomial ℕ) ^ r *
        ∏ k ∈ Finset.Ico r n,
          ((Polynomial.X : Polynomial ℕ) + Polynomial.C k)) *
        ((Polynomial.X : Polynomial ℕ) + Polynomial.C n)).coeff m := by
    unfold rStirlingFirst
    rw [hP]
  rw [hLHS, mul_add, Polynomial.coeff_add, Polynomial.coeff_mul_C]
  unfold rStirlingFirst
  cases m with
  | zero =>
    rw [show (0 : ℕ) - 1 = 0 from rfl]
    have hQX0 : ((((Polynomial.X : Polynomial ℕ) ^ r *
        ∏ k ∈ Finset.Ico r n,
          ((Polynomial.X : Polynomial ℕ) + Polynomial.C k)) *
        Polynomial.X)).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simp
    have hQ0 : (((Polynomial.X : Polynomial ℕ) ^ r *
        ∏ k ∈ Finset.Ico r n,
          ((Polynomial.X : Polynomial ℕ) + Polynomial.C k))).coeff 0 = 0 :=
      rStirlingFirst_zero_of_pos n r hr
    rw [hQX0, hQ0]
    ring
  | succ m' =>
    rw [Nat.add_sub_cancel, Polynomial.coeff_mul_X]
    ring

/-- **Broder's alternating expansion of the r-Stirling numbers of the first kind.** Let $n$, $m$
and $r$ be natural numbers with $1 \le r \le n$. Write $[n, m]_r$ for the unsigned $r$-Stirling
number of the first kind, $[a, b]$ for the unsigned Stirling number of the first kind and
$\lbrace a, b \rbrace$ for the Stirling number of the second kind. Then, in the integers,
$$(-1)^r [n, m]_r = \sum_{k=r}^{n+r-m} [n, m+k-r] \, \lbrace k-1, r-1 \rbrace \, (-1)^k.$$

Broder's Equation (43) sums over all $k$; every term outside the range above vanishes, since
$\lbrace k-1, r-1 \rbrace$ vanishes for $k < r$ and $[n, m+k-r]$ vanishes for $k > n + r - m$.

Proves `Wanted` entry `rStirlingFirst_eq_alternating_sum`.

Source: A. Z. Broder, "The r-Stirling numbers",
Stanford Computer Science Report STAN-CS-82-949 (December 1982),
PDF page 16 / printed page 13, Equation (43);
journal version: Discrete Mathematics 49 (1984), 241-259,
DOI 10.1016/0012-365X(84)90161-4. -/
theorem rStirlingFirst_eq_alternating_sum (n m r : ℕ) (hr : 0 < r)
    (hrn : r ≤ n) :
    (-1 : Int) ^ r * (rStirlingFirst n m r : Int) =
      Finset.sum (Finset.Icc r (n + r - m)) (fun k =>
        (Nat.stirlingFirst n (m + (k - r)) : Int) *
          (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k) := by
  have hr1 : 1 ≤ r := hr
  suffices key : ∀ d m, (-1 : Int) ^ r * (rStirlingFirst (r + d) m r : Int) =
      Finset.sum (Finset.Icc r (r + d + r - m)) (fun k =>
        (Nat.stirlingFirst (r + d) (m + (k - r)) : Int) *
          (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k) from
    by have h := key (n - r) m; rwa [Nat.add_sub_cancel' hrn] at h
  intro d
  induction d with
  | zero =>
    intro m
    simp only [Nat.add_zero]
    by_cases heq : m = r
    · rw [heq]
      have hrr : rStirlingFirst r r r = 1 := by simp [rStirlingFirst_self]
      rw [hrr]
      have hb : r + r - r = r := by omega
      rw [hb, Finset.Icc_self, Finset.sum_singleton]
      have e1 : r + (r - r) = r := by omega
      rw [e1, Nat.stirlingFirst_self, Nat.stirlingSecond_self]
      push_cast
      ring
    · by_cases hlt : m < r
      · have hLHS0 : (-1 : Int) ^ r * (rStirlingFirst r m r : Int) = 0 := by
          simp [rStirlingFirst_self m r, heq]
        have hbij : (∑ k ∈ Finset.Icc r (r + r - m),
                ((Nat.stirlingFirst r (m + (k - r)) : Int) *
                  (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k)) =
            (∑ j ∈ Finset.Icc m r,
              ((Nat.stirlingFirst r j : Int) *
                (Nat.stirlingSecond (j + (r - 1 - m)) (r - 1) : Int) *
                (-1 : Int) ^ ((r - m) + j))) := by
          refine Finset.sum_bij (fun k _ => m + (k - r)) ?_ ?_ ?_ ?_
          · intro k hk
            rw [Finset.mem_Icc] at hk
            show m + (k - r) ∈ Finset.Icc m r
            rw [Finset.mem_Icc]
            omega
          · intro k₁ hk₁ k₂ hk₂ h
            rw [Finset.mem_Icc] at hk₁ hk₂
            have h' : m + (k₁ - r) = m + (k₂ - r) := h
            omega
          · intro j hj
            rw [Finset.mem_Icc] at hj
            refine ⟨j + (r - m), ?_, ?_⟩
            · show j + (r - m) ∈ Finset.Icc r (r + r - m)
              rw [Finset.mem_Icc]
              omega
            · show m + ((j + (r - m)) - r) = j
              omega
          · intro k hk
            rw [Finset.mem_Icc] at hk
            have e1 : (m + (k - r)) + (r - 1 - m) = k - 1 := by omega
            have e2 : (r - m) + (m + (k - r)) = k := by omega
            rw [e1, e2]
        have hfact : (∑ j ∈ Finset.Icc m r,
              ((Nat.stirlingFirst r j : Int) *
                (Nat.stirlingSecond (j + (r - 1 - m)) (r - 1) : Int) *
                (-1 : Int) ^ ((r - m) + j))) =
            (-1 : Int) ^ (r - m) *
              (∑ j ∈ Finset.Icc m r,
                ((Nat.stirlingFirst r j : Int) * (-1 : Int) ^ j *
                  (Nat.stirlingSecond (j + (r - 1 - m)) (r - 1) : Int))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by rw [pow_add]; ring)
        have hsub : (∑ j ∈ Finset.Icc m r,
              ((Nat.stirlingFirst r j : Int) * (-1 : Int) ^ j *
                (Nat.stirlingSecond (j + (r - 1 - m)) (r - 1) : Int))) =
            (∑ j ∈ Finset.range (r + 1),
              ((Nat.stirlingFirst r j : Int) * (-1 : Int) ^ j *
                (Nat.stirlingSecond (j + (r - 1 - m)) (r - 1) : Int))) := by
          apply Finset.sum_subset
          · intro x hx
            rw [Finset.mem_Icc] at hx
            rw [Finset.mem_range]
            omega
          · intro x hx hxnot
            rw [Finset.mem_range] at hx
            rw [Finset.mem_Icc] at hxnot
            have hxm : x < m := by omega
            have hS : ((Nat.stirlingSecond (x + (r - 1 - m)) (r - 1)) : Int) = 0 := by
              have h0 : Nat.stirlingSecond (x + (r - 1 - m)) (r - 1) = 0 :=
                Nat.stirlingSecond_eq_zero_of_lt (by omega)
              exact_mod_cast h0
            simp [hS]
        have hvan : (∑ j ∈ Finset.range (r + 1),
            ((Nat.stirlingFirst r j : Int) * (-1 : Int) ^ j *
              (Nat.stirlingSecond (j + (r - 1 - m)) (r - 1) : Int))) = 0 :=
          vanish_stirling_sum r (r - 1) (r - 1 - m) (by omega)
        rw [hLHS0, hbij, hfact, hsub, hvan]
        simp
      · have hgt : r < m := by omega
        have hLHS0 : (-1 : Int) ^ r * (rStirlingFirst r m r : Int) = 0 := by
          simp [rStirlingFirst_self m r, heq]
        have hempty : Finset.Icc r (r + r - m) = ∅ :=
          Finset.Icc_eq_empty (by omega)
        rw [hLHS0, hempty, Finset.sum_empty]
  | succ d ih =>
    intro m
    set n := r + d with hn_def
    have hnr : r ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    have hadd : r + (d + 1) = n + 1 := by omega
    rw [hadd]
    by_cases hm0 : m = 0
    · subst hm0
      have hL0 : (-1 : Int) ^ r * (rStirlingFirst (n + 1) 0 r : Int) = 0 := by
        rw [rStirlingFirst_zero_of_pos (n + 1) r hr1, Nat.cast_zero, mul_zero]
      rw [hL0]
      have hb0 : n + 1 + r - 0 = (n + 1) + r := by omega
      rw [hb0]
      have hbij2 : (∑ k ∈ Finset.Icc r ((n + 1) + r),
            ((Nat.stirlingFirst (n + 1) (0 + (k - r)) : Int) *
              (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k)) =
          (∑ j ∈ Finset.range (n + 1 + 1),
            ((Nat.stirlingFirst (n + 1) j : Int) * (-1 : Int) ^ (j + r) *
              (Nat.stirlingSecond (j + (r - 1)) (r - 1) : Int))) := by
        refine Finset.sum_bij (fun k _ => k - r) ?_ ?_ ?_ ?_
        · intro k hk
          rw [Finset.mem_Icc] at hk
          show k - r ∈ Finset.range (n + 1 + 1)
          rw [Finset.mem_range]
          omega
        · intro k₁ hk₁ k₂ hk₂ h
          rw [Finset.mem_Icc] at hk₁ hk₂
          have h' : k₁ - r = k₂ - r := h
          omega
        · intro j hj
          rw [Finset.mem_range] at hj
          refine ⟨j + r, ?_, Nat.add_sub_cancel j r⟩
          show j + r ∈ Finset.Icc r ((n + 1) + r)
          rw [Finset.mem_Icc]
          omega
        · intro k hk
          rw [Finset.mem_Icc] at hk
          have e2 : (k - r) + (r - 1) = k - 1 := by omega
          have e3 : (k - r) + r = k := Nat.sub_add_cancel hk.1
          rw [zero_add, e3, e2]
          ring
      have hfact : (∑ j ∈ Finset.range (n + 1 + 1),
            ((Nat.stirlingFirst (n + 1) j : Int) * (-1 : Int) ^ (j + r) *
              (Nat.stirlingSecond (j + (r - 1)) (r - 1) : Int))) =
          (-1 : Int) ^ r *
            (∑ j ∈ Finset.range (n + 1 + 1),
              ((Nat.stirlingFirst (n + 1) j : Int) * (-1 : Int) ^ j *
                (Nat.stirlingSecond (j + (r - 1)) (r - 1) : Int))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [pow_add]; ring)
      have hvan : (∑ j ∈ Finset.range (n + 1 + 1),
          ((Nat.stirlingFirst (n + 1) j : Int) * (-1 : Int) ^ j *
            (Nat.stirlingSecond (j + (r - 1)) (r - 1) : Int))) = 0 :=
        vanish_stirling_sum (n + 1) (r - 1) (r - 1) (by omega)
      rw [hbij2, hfact, hvan]
      simp
    · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [hm']
      have h5 := rStirlingFirst_succ n (m' + 1) r hr1 hnr
      rw [Nat.add_sub_cancel] at h5
      have hL : (-1 : Int) ^ r * (rStirlingFirst (n + 1) (m' + 1) r : Int) =
          (-1 : Int) ^ r * (rStirlingFirst n m' r : Int) +
            (n : Int) * ((-1 : Int) ^ r * (rStirlingFirst n (m' + 1) r : Int)) := by
        rw [h5]
        push_cast
        ring
      have hR : (∑ k ∈ Finset.Icc r (((n + 1) + r) - (m' + 1)),
            ((Nat.stirlingFirst (n + 1) ((m' + 1) + (k - r)) : Int) *
              (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k)) =
          (∑ k ∈ Finset.Icc r (((n + 1) + r) - (m' + 1)),
            ((Nat.stirlingFirst n (m' + (k - r)) : Int) *
              (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k)) +
            (n : Int) *
              (∑ k ∈ Finset.Icc r (((n + 1) + r) - (m' + 1)),
                ((Nat.stirlingFirst n ((m' + 1) + (k - r)) : Int) *
                  (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_Icc] at hk
        have e : (m' + 1) + (k - r) - 1 = m' + (k - r) := by omega
        have hcZ' : ((Nat.stirlingFirst (n + 1) ((m' + 1) + (k - r)) : ℕ) : Int) =
            ((Nat.stirlingFirst n (((m' + 1) + (k - r)) - 1) : ℕ) : Int) +
              (n : Int) * ((Nat.stirlingFirst n ((m' + 1) + (k - r)) : ℕ) : Int) := by
          exact_mod_cast stirlingFirst_step n ((m' + 1) + (k - r)) hn1
        rw [hcZ', e]
        ring
      have hbA : (n + 1) + r - (m' + 1) = n + r - m' := by omega
      have hA : (∑ k ∈ Finset.Icc r (((n + 1) + r) - (m' + 1)),
            ((Nat.stirlingFirst n (m' + (k - r)) : Int) *
              (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k)) =
          (∑ k ∈ Finset.Icc r (n + r - m'),
            ((Nat.stirlingFirst n (m' + (k - r)) : Int) *
              (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k)) := by
        rw [hbA]
      have hB : (∑ k ∈ Finset.Icc r (((n + 1) + r) - (m' + 1)),
            ((Nat.stirlingFirst n ((m' + 1) + (k - r)) : Int) *
              (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k)) =
          (∑ k ∈ Finset.Icc r (n + r - (m' + 1)),
            ((Nat.stirlingFirst n ((m' + 1) + (k - r)) : Int) *
              (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k)) := by
        have hsub2 : Finset.Icc r (n + r - (m' + 1)) ⊆
            Finset.Icc r (((n + 1) + r) - (m' + 1)) := by
          intro x hx
          rw [Finset.mem_Icc] at hx ⊢
          omega
        have hvan2 : ∀ x ∈ Finset.Icc r (((n + 1) + r) - (m' + 1)),
            x ∉ Finset.Icc r (n + r - (m' + 1)) →
              ((Nat.stirlingFirst n ((m' + 1) + (x - r)) : Int) *
                (Nat.stirlingSecond (x - 1) (r - 1) : Int) * (-1 : Int) ^ x) = 0 := by
          intro x hx hxnot
          rw [Finset.mem_Icc] at hx hxnot
          have hc0 : Nat.stirlingFirst n ((m' + 1) + (x - r)) = 0 := by
            apply Nat.stirlingFirst_eq_zero_of_lt
            omega
          simp [hc0]
        have h := Finset.sum_subset hsub2 hvan2
        exact h.symm
      have ih0 := ih m'
      have ih1 := ih (m' + 1)
      rw [hL, hR, hA, hB, ← ih0, ← ih1]

end MetaMathlibExt
