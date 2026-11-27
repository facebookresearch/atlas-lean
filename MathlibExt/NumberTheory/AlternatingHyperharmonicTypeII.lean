/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AlternatingHyperharmonic
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-!
# Finite sums for type II alternating hyperharmonic numbers

Li's coefficients express the iterated partial sums as a finite sum of alternating
harmonic numbers with shifted exponents.

## References

- Rusen Li, [*Sums over Primes II*](https://cs.uwaterloo.ca/journals/JIS/VOL27/Li/li15.html),
  Journal of Integer Sequences 27 (2024), Article 24.4.1, Lemma 3 (the type II finite-sum formula).
- Rusen Li, [*Euler sums of generalized hyperharmonic numbers*](https://doi.org/10.7169/facm/1953),
  Functiones et Approximatio Commentarii Mathematici 66, no. 2 (2022), pp. 179–189
  (the polynomial expansion of the iterated-sum kernel and its coefficient recurrence via
  Faulhaber's formula).
-/

namespace MetaMathlibExt

open Finset

@[expose] public section

/-- **Li's coefficients $a(r, m, j)$.** The rational numbers $a(r, m, j)$, for natural numbers
$r$, $m$, $j$, are defined by recursion on $r$. For all $m$ and $j$, $a(0, m, j) = 0$; moreover
$a(1, 0, 0) = 1$ and $a(1, m, j) = 0$ for $(m, j) \ne (0, 0)$. For $r \ge 1$ the values of
order $r + 1$ are as follows. First,
$$a(r+1, r, 0) = -\sum_{m=0}^{r-1} \frac{a(r, m, r-m-1)}{r-m}.$$
For $0 \le m \le r - 1$ and $1 \le \ell \le r - m$,
$$a(r+1,m,\ell) = \sum_{j=\ell-1}^{r-1-m} \frac{a(r,m,j)}{j+1} \binom{j+1}{j-\ell+1} B_{j-\ell+1}.$$
For $0 \le m \le r - 1$,
$$a(r+1, m, 0) = -\sum_{y=0}^{m} \sum_{j=\max(0, m-y-1)}^{r-1-y} a(r, y, j)\, D(m, j, y),$$
where
$$D(m, j, y) = \frac{1}{j+1} \sum_{\ell=\max(0, m-y-1)}^{j} \binom{j+1}{j-\ell} B_{j-\ell}
\binom{\ell+1}{m-y} (-1)^{1+\ell-m+y}.$$
All other values $a(r+1, m, \ell)$ are $0$. Here $B_n$ are the Bernoulli numbers with
$B_1 = 1/2$, that is, the numbers determined by $\sum_{j=0}^{k} \binom{k+1}{j} B_j = k + 1$ for
all $k \ge 0$.

Li writes $D(r, m, j, y)$; the value does not depend on $r$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3 (quoting Li, *Euler sums of generalized hyperharmonic numbers*). -/
public def liCoeffA : ℕ → ℕ → ℕ → ℚ
  | 0, _, _ => 0
  | 1, m, j => if m = 0 ∧ j = 0 then 1 else 0
  | r + 2, m, l =>
    if m = r + 1 ∧ l = 0 then
      -∑ m' ∈ range (r + 1), liCoeffA (r + 1) m' (r - m') / ((r + 1 - m' : ℕ) : ℚ)
    else if m ≤ r ∧ 1 ≤ l ∧ l ≤ r + 1 - m then
      ∑ j ∈ Icc (l - 1) (r - m), liCoeffA (r + 1) m j / ((j + 1 : ℕ) : ℚ) *
        ((j + 1).choose (j + 1 - l) : ℚ) * bernoulli' (j + 1 - l)
    else if m ≤ r ∧ l = 0 then
      -∑ y ∈ range (m + 1), ∑ j ∈ Icc (m - y - 1) (r - y), liCoeffA (r + 1) y j *
        ∑ i ∈ Icc (m - y - 1) j, 1 / ((j + 1 : ℕ) : ℚ) * ((j + 1).choose (j - i) : ℚ) *
          bernoulli' (j - i) * ((i + 1).choose (m - y) : ℚ) * (-1) ^ (1 + i + y - m)
    else 0

/-- **The coefficient $a(1, 0, 0)$.** The coefficient $a(1, 0, 0)$ of Li's Lemma 3 equals $1$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3. -/
public theorem liCoeffA_one_zero_zero : liCoeffA 1 0 0 = 1 := by
  simp [liCoeffA]

/-- **The coefficient $a(2, 1, 0)$.** The coefficient $a(2, 1, 0)$ of Li's Lemma 3 equals $-1$.

By the recursion, $a(2, 1, 0) = -a(1, 0, 0) = -1$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3. -/
public theorem liCoeffA_two_one_zero : liCoeffA 2 1 0 = -1 := by
  simp [liCoeffA]

/-- **Li's coefficients $c(m, j)$.** For natural numbers $m$ and $j$, the rational number
$c(m, j)$ is $\frac{1}{m+1} \binom{m+1}{m+1-j} B_{m+1-j}$ when $j \le m + 1$ and $0$ otherwise,
where $B_i$ denotes the Bernoulli numbers with the convention $B_1 = +\frac{1}{2}$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public def liCoeffC (m j : ℕ) : ℚ :=
  if j ≤ m + 1 then
    1 / ((m + 1 : ℕ) : ℚ) * ((m + 1).choose (m + 1 - j) : ℚ) * bernoulli' (m + 1 - j)
  else 0

/-- **Li's coefficients $d(m, j)$.** For natural numbers $m$ and $j$, the rational number
$d(m, j)$ is $\frac{1}{m+1} \sum_{k} \binom{m+1}{m-k} B_{m-k} \binom{1+k}{j} (-1)^{1+k-j}$, the sum
running over the natural numbers $k$ with $\max(j - 1, 0) \le k \le m$ (so $d(m, j) = 0$ when
$j > m + 1$), where $B_i$ denotes the Bernoulli numbers with the convention $B_1 = +\frac{1}{2}$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public def liCoeffD (m j : ℕ) : ℚ :=
  1 / ((m + 1 : ℕ) : ℚ) * ∑ k ∈ Icc (j - 1) m,
    ((m + 1).choose (m - k) : ℚ) * bernoulli' (m - k) * ((1 + k).choose j : ℚ) * (-1) ^ (1 + k - j)

end

-- The power-sum polynomial has no constant term, unlike Li's general coefficient array.
private def powerCoeff (j l : ℕ) : ℚ :=
  if 1 ≤ l then liCoeffC j l else 0

private theorem powerCoeff_of_le {j l : ℕ} (hl : 1 ≤ l) (h : l ≤ j + 1) :
    powerCoeff j l = 1 / ((j + 1 : ℕ) : ℚ) * ((j + 1).choose (j + 1 - l) : ℚ) *
      bernoulli' (j + 1 - l) := by
  simp [powerCoeff, liCoeffC, hl, h]

private theorem liCoeffD_eq_sum (j d : ℕ) :
    liCoeffD j d = ∑ i ∈ Icc (d - 1) j,
      powerCoeff j (i + 1) * ((i + 1).choose d : ℚ) * (-1) ^ (i + 1 - d) := by
  rw [liCoeffD, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [powerCoeff_of_le (by omega) (by have := (mem_Icc.mp hi).2; omega),
    show j + 1 - (i + 1) = j - i by omega, Nat.add_comm 1 i]
  ring

private theorem liCoeffD_zero_of_lt {j d : ℕ} (h : j + 1 < d) : liCoeffD j d = 0 := by
  rw [liCoeffD, Icc_eq_empty_of_lt (by omega : j < d - 1), sum_empty, mul_zero]

private theorem liCoeffD_top (j : ℕ) : liCoeffD j (j + 1) = 1 / ((j + 1 : ℕ) : ℚ) := by
  simp [liCoeffD, Nat.add_comm 1]

private theorem liCoeffA_zero_of_le_add {r m j : ℕ} (h : r ≤ m + j) :
    liCoeffA r m j = 0 := by
  rcases r with _ | _ | r
  · rfl
  · rw [liCoeffA, ite_eq_right (by omega)]
  · rw [liCoeffA, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

-- Padding the recurrence by zeros lets the same index set serve all monomials.
private theorem liCoeffA_succ_pos (r m l : ℕ) (hl : 1 ≤ l) :
    liCoeffA (r + 2) m l = ∑ j ∈ range (r + 2), liCoeffA (r + 1) m j * powerCoeff j l := by
  rw [liCoeffA, ite_eq_right (by omega)]
  by_cases h : m ≤ r ∧ 1 ≤ l ∧ l ≤ r + 1 - m
  · rw [ite_eq_left h]
    calc
      _ = ∑ j ∈ Icc (l - 1) (r - m), liCoeffA (r + 1) m j * powerCoeff j l := by
        refine sum_congr rfl fun j hj => ?_
        rw [powerCoeff_of_le hl (by have := (mem_Icc.mp hj).1; omega)]
        ring
      _ = _ := by
        refine sum_subset (fun j hj => mem_range.mpr (by have := (mem_Icc.mp hj).2; omega)) ?_
        intro j _ hj
        by_cases hd : l ≤ j + 1
        · rw [liCoeffA_zero_of_le_add (by rw [mem_Icc] at hj; omega), zero_mul]
        · simp [powerCoeff, liCoeffC, hd]
  · rw [ite_eq_right h, ite_eq_right (by omega)]
    symm
    apply sum_eq_zero
    intro j _
    by_cases hd : l ≤ j + 1
    · rw [liCoeffA_zero_of_le_add (by omega), zero_mul]
    · simp [powerCoeff, liCoeffC, hd]

private theorem liCoeffA_succ_zero (r m : ℕ) (hm : m < r + 2) :
    liCoeffA (r + 2) m 0 = -∑ y ∈ range (m + 1), ∑ j ∈ range (r + 2),
      liCoeffA (r + 1) y j * liCoeffD j (m - y) := by
  rw [liCoeffA]
  by_cases ht : m = r + 1
  · subst m
    rw [ite_eq_left ⟨rfl, rfl⟩]
    congr 1
    have hlast : ∀ y ∈ range (r + 2),
        (∑ j ∈ range (r + 2), liCoeffA (r + 1) y j * liCoeffD j (r + 1 - y)) =
          if y < r + 1 then liCoeffA (r + 1) y (r - y) / ((r + 1 - y : ℕ) : ℚ) else 0 := by
      intro y hy
      by_cases hy' : y < r + 1
      · rw [ite_eq_left hy', sum_eq_single_of_mem (r - y) (mem_range.mpr (by omega))]
        · rw [show r + 1 - y = (r - y) + 1 by omega, liCoeffD_top]
          ring
        · intro j _ hj
          by_cases h : j < r - y
          · rw [liCoeffD_zero_of_lt (by omega), mul_zero]
          · rw [liCoeffA_zero_of_le_add (by omega), zero_mul]
      · rw [ite_eq_right hy']
        exact sum_eq_zero fun j _ => by rw [liCoeffA_zero_of_le_add (by omega), zero_mul]
    rw [sum_congr rfl hlast]
    conv_rhs => rw [sum_range_succ]
    simp only [lt_irrefl, ite_false, add_zero]
    exact sum_congr rfl fun y hy => (ite_eq_left (mem_range.mp hy)).symm
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1
    refine sum_congr rfl fun y hy => ?_
    have hy' : y ≤ m := by simpa using hy
    calc
      _ = ∑ j ∈ Icc (m - y - 1) (r - y), liCoeffA (r + 1) y j * liCoeffD j (m - y) := by
        refine sum_congr rfl fun j _ => congrArg (_ * ·) ?_
        rw [liCoeffD_eq_sum]
        refine sum_congr rfl fun i hi => ?_
        rw [powerCoeff_of_le (by omega) (by have := (mem_Icc.mp hi).2; omega),
          show j + 1 - (i + 1) = j - i by omega,
          show i + 1 - (m - y) = 1 + i + y - m by omega]
      _ = _ := by
        refine sum_subset (fun j hj => mem_range.mpr (by have := (mem_Icc.mp hj).2; omega)) ?_
        intro j _ hj
        rw [mem_Icc] at hj
        by_cases hd : j + 1 < m - y
        · rw [liCoeffD_zero_of_lt hd, mul_zero]
        · rw [liCoeffA_zero_of_le_add (by omega), zero_mul]

private def powerSum (j : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ range (j + 1), powerCoeff j (i + 1) * x ^ (i + 1)

private theorem powerSum_nat (n j : ℕ) :
    powerSum j n = ∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ j := by
  rw [sum_Ico_pow, powerSum, ← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  have h₁ : j + 1 - 1 - i + 1 = j + 1 - i := by omega
  rw [h₁, powerCoeff_of_le (by omega) (by omega), show j + 1 - (j + 1 - i) = i by omega]
  push_cast
  ring

private theorem powerSum_expand (j R : ℕ) (h : j + 1 < R) (x : ℚ) :
    powerSum j x = ∑ l ∈ Ico 1 R, powerCoeff j l * x ^ l := by
  calc
    _ = ∑ l ∈ Ico 1 (j + 2), powerCoeff j l * x ^ l := by
      rw [sum_Ico_eq_sum_range]
      simp [powerSum, Nat.add_comm 1]
    _ = _ := by
      refine sum_subset (Ico_subset_Ico_right (by omega)) ?_
      intro l hl hl'
      rw [mem_Ico] at hl hl'
      simp [powerCoeff, liCoeffC, show ¬ l ≤ j + 1 by omega]

private theorem powerSum_shift (j R : ℕ) (h : j + 1 < R) (x : ℚ) :
    powerSum j (x - 1) = ∑ d ∈ range R, liCoeffD j d * x ^ d := by
  calc
    _ = ∑ i ∈ range (j + 1), ∑ d ∈ range R,
        (powerCoeff j (i + 1) * ((i + 1).choose d : ℚ) * (-1) ^ (i + 1 - d)) * x ^ d := by
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.mp hi
      rw [sub_eq_add_neg, add_pow, mul_sum]
      calc
        _ = ∑ d ∈ range (i + 1 + 1),
            (powerCoeff j (i + 1) * ((i + 1).choose d : ℚ) * (-1) ^ (i + 1 - d)) * x ^ d := by
          exact sum_congr rfl fun d _ => by ring
        _ = _ := by
          refine sum_subset (range_mono (by omega)) ?_
          intro d _ hd
          simp only [mem_range, not_lt] at hd
          simp [Nat.choose_eq_zero_of_lt (show i + 1 < d by omega)]
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun d _ => ?_
      rw [liCoeffD_eq_sum, sum_mul]
      symm
      refine sum_subset (fun i hi => mem_range.mpr (by have := (mem_Icc.mp hi).2; omega)) ?_
      intro i hi hi'
      rw [mem_range] at hi
      rw [mem_Icc] at hi'
      simp [Nat.choose_eq_zero_of_lt (show i + 1 < d by omega)]

private theorem sum_power_interval (j : ℕ) {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Ico k (n + 1), (i : ℚ) ^ j = powerSum j n - powerSum j ((k : ℚ) - 1) := by
  rw [show (k : ℚ) - 1 = ((k - 1 : ℕ) : ℚ) by simp [Nat.cast_sub hk],
    powerSum_nat, powerSum_nat, Nat.sub_add_cancel hk]
  exact eq_sub_of_add_eq' (sum_Ico_consecutive (fun i => (i : ℚ) ^ j) hk (by omega))

private def coeffPoly (r : ℕ) (x y : ℚ) : ℚ :=
  ∑ m ∈ range r, (∑ j ∈ range r, liCoeffA r m j * x ^ j) * y ^ m

private theorem coeffPoly_pad {r R : ℕ} (h : r ≤ R) (x y : ℚ) :
    coeffPoly r x y = ∑ m ∈ range R, (∑ j ∈ range R, liCoeffA r m j * x ^ j) * y ^ m := by
  unfold coeffPoly
  calc
    _ = ∑ m ∈ range r, (∑ j ∈ range R, liCoeffA r m j * x ^ j) * y ^ m := by
      refine sum_congr rfl fun m _ => congrArg (· * y ^ m) ?_
      refine sum_subset (range_mono h) ?_
      intro j _ hj
      rw [liCoeffA_zero_of_le_add (by simp only [mem_range, not_lt] at hj; omega), zero_mul]
    _ = _ := by
      refine sum_subset (range_mono h) ?_
      intro m _ hm
      have hm' : r ≤ m := by simpa using hm
      have hz (j : ℕ) : liCoeffA r m j = 0 := liCoeffA_zero_of_le_add (by omega)
      simp [hz]

private theorem upper_eval (r m : ℕ) (x : ℚ) :
    ∑ j ∈ range (r + 2), liCoeffA (r + 1) m j * powerSum j x =
      ∑ l ∈ Ico 1 (r + 2), liCoeffA (r + 2) m l * x ^ l := by
  calc
    _ = ∑ j ∈ range (r + 2), ∑ l ∈ Ico 1 (r + 2),
        (liCoeffA (r + 1) m j * powerCoeff j l) * x ^ l := by
      refine sum_congr rfl fun j _ => ?_
      by_cases h : j + 1 < r + 2
      · rw [powerSum_expand j (r + 2) h, mul_sum]
        exact sum_congr rfl fun l _ => (mul_assoc ..).symm
      · simp [liCoeffA_zero_of_le_add (by omega : r + 1 ≤ m + j)]
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun l hl => ?_
      rw [liCoeffA_succ_pos r m l (mem_Ico.mp hl).1, sum_mul]

-- Group the lower-endpoint terms by their total degree in the harmonic index.
private theorem lower_eval (r : ℕ) (x : ℚ) :
    ∑ y ∈ range (r + 2), (∑ j ∈ range (r + 2), liCoeffA (r + 1) y j * powerSum j (x - 1)) * x ^ y =
      -(∑ m ∈ range (r + 2), liCoeffA (r + 2) m 0 * x ^ m) := by
  let u (y d : ℕ) := ∑ j ∈ range (r + 2), liCoeffA (r + 1) y j * liCoeffD j d
  have hu (y d : ℕ) (h : r + 2 ≤ y + d) : u y d = 0 := by
    apply sum_eq_zero
    intro j _
    by_cases hj : j + 1 < d
    · rw [liCoeffD_zero_of_lt hj, mul_zero]
    · rw [liCoeffA_zero_of_le_add (by omega), zero_mul]
  have hshift (y : ℕ) :
      ∑ j ∈ range (r + 2), liCoeffA (r + 1) y j * powerSum j (x - 1) =
        ∑ d ∈ range (r + 2), u y d * x ^ d := by
    calc
      _ = ∑ j ∈ range (r + 2), ∑ d ∈ range (r + 2),
          liCoeffA (r + 1) y j * liCoeffD j d * x ^ d := by
        refine sum_congr rfl fun j _ => ?_
        by_cases h : j + 1 < r + 2
        · rw [powerSum_shift j (r + 2) h, mul_sum]
          exact sum_congr rfl fun d _ => (mul_assoc ..).symm
        · simp [liCoeffA_zero_of_le_add (by omega : r + 1 ≤ y + j)]
      _ = _ := by rw [sum_comm]; simp only [u, sum_mul]
  simp_rw [hshift, ← sum_neg_distrib]
  calc
    _ = ∑ y ∈ Ico 0 (r + 2), ∑ m ∈ Ico y (r + 2), u y (m - y) * x ^ m := by
      refine sum_congr (range_eq_Ico _) fun y _ => ?_
      rw [sum_mul]
      conv_rhs => rw [sum_Ico_eq_sum_range]
      calc
        _ = ∑ d ∈ range (r + 2), u y d * x ^ (y + d) := by
          exact sum_congr rfl fun d _ => by rw [pow_add]; ring
        _ = ∑ d ∈ range (r + 2 - y), u y d * x ^ (y + d) := by
          symm
          refine sum_subset (range_mono (by omega)) ?_
          intro d _ hd
          rw [hu y d (by simp only [mem_range, not_lt] at hd; omega), zero_mul]
        _ = _ := by
          refine sum_congr rfl fun d _ => ?_
          rw [show y + d - y = d by omega]
    _ = _ := by
      rw [sum_Ico_Ico_comm]
      simp only [← range_eq_Ico]
      refine sum_congr rfl fun m hm => ?_
      rw [← neg_mul, liCoeffA_succ_zero r m (mem_range.mp hm), neg_neg, sum_mul]

private theorem sum_coeffPoly (r : ℕ) {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Ico k (n + 1), coeffPoly (r + 1) i k = coeffPoly (r + 2) n k := by
  simp_rw [coeffPoly_pad (show r + 1 ≤ r + 2 by omega)]
  calc
    _ = ∑ m ∈ range (r + 2), (∑ j ∈ range (r + 2),
        liCoeffA (r + 1) m j * (∑ i ∈ Ico k (n + 1), (i : ℚ) ^ j)) * (k : ℚ) ^ m := by
      rw [sum_comm]
      refine sum_congr rfl fun m _ => ?_
      rw [← sum_mul, sum_comm]
      simp_rw [mul_sum]
    _ = _ := by
      simp_rw [sum_power_interval _ hk hkn, mul_sub, sum_sub_distrib, sub_mul]
      rw [sum_sub_distrib, lower_eval, sub_neg_eq_add]
      simp_rw [upper_eval, coeffPoly, ← sum_add_distrib]
      refine sum_congr rfl fun m _ => ?_
      rw [← add_mul, sum_range_succ']
      simp [sum_Ico_eq_sum_range, Nat.add_comm 1]

private theorem iterated_eq_sum_kernel (b : ℕ → ℝ) (r n : ℕ) :
    signedIteratedPartialSum false (fun i => ∑ k ∈ Ico 1 (i + 1), b k) (r + 1) n =
      ∑ k ∈ Ico 1 (n + 1), (coeffPoly (r + 1) n k : ℝ) * b k := by
  induction r generalizing n with
  | zero => simp [signedIteratedPartialSum_one, coeffPoly, liCoeffA]
  | succ r ih =>
    rw [signedIteratedPartialSum_succ]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, ih, ← Ico_add_one_right_eq_Icc]
    rw [← sum_Ico_Ico_comm 1 (n + 1) (fun k i => (coeffPoly (r + 1) i k : ℝ) * b k)]
    refine sum_congr rfl fun k hk => ?_
    rw [← sum_mul, ← Rat.cast_sum, sum_coeffPoly r (mem_Ico.mp hk).1
      (by have := (mem_Ico.mp hk).2; omega)]

private theorem cast_coeffPoly (r n k : ℕ) :
    (coeffPoly r n k : ℝ) = ∑ m ∈ range r, ∑ j ∈ range (r - m),
      (liCoeffA r m j : ℝ) * (n : ℝ) ^ j * (k : ℝ) ^ m := by
  simp only [coeffPoly, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, sum_mul]
  refine sum_congr rfl fun m _ => ?_
  symm
  refine sum_subset (range_mono (by omega)) ?_
  intro j _ hj
  rw [liCoeffA_zero_of_le_add (by simp only [mem_range, not_lt] at hj; omega)]
  simp

/-- **Explicit formula for type II alternating hyperharmonic numbers.** For real $s$ write
$\overline{H}_n^{(s)} = \sum_{i=1}^{n} (-1)^{i-1}/i^s$ for the alternating generalized harmonic
numbers. For a natural number $p$, the type II generalized alternating hyperharmonic numbers are
$H_n^{(p,1,2)} = \overline{H}_n^{(p)}$ and $H_n^{(p,r+1,2)} = \sum_{k=1}^{n} H_k^{(p,r,2)}$. Let
$a(r, m, j)$ be Li's rational coefficients. Then for all natural numbers $r, n, p \ge 1$,
$$
H_n^{(p,r,2)} = \sum_{m=0}^{r-1} \sum_{j=0}^{r-1-m} a(r, m, j)\, n^j\, \overline{H}_n^{(p-m)},
$$
where the index $p - m$ is a real number and may be negative.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3 (`jis-2024-24.4.1-lem-3`). -/
public theorem alternatingHyperharmonic_typeII_eq_sum {r n p : ℕ} (hr : 1 ≤ r)
    (hn : 1 ≤ n) (hp : 1 ≤ p) :
    signedIteratedPartialSum false (alternatingGeneralizedHarmonic p) r n =
      ∑ m ∈ range r, ∑ j ∈ range (r - m),
        (liCoeffA r m j : ℝ) * (n : ℝ) ^ j * alternatingGeneralizedHarmonic ((p : ℝ) - m) n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hharmonic (s : ℝ) : alternatingGeneralizedHarmonic s = fun i =>
      ∑ k ∈ Ico (1 : ℕ) (i + 1), (-1 : ℝ) ^ (k - 1) * ((k : ℝ) ^ s)⁻¹ := by
    funext i
    rw [alternatingGeneralizedHarmonic, Ico_add_one_right_eq_Icc]
  rw [hharmonic, iterated_eq_sum_kernel]
  simp_rw [hharmonic, cast_coeffPoly, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k from (mem_Ico.mp hk).1)
  rw [Real.rpow_sub hk']
  simp only [Real.rpow_natCast, inv_div]
  ring

end MetaMathlibExt
