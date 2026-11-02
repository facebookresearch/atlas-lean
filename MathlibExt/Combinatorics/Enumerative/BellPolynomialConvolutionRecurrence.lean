/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.PartialBellPolynomial
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Nat.Cast.Field
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Product of monomials is the monomial of the summed degrees and multiplied coefficients. -/
private lemma prod_monomial {ι : Type*} (s : Finset ι) (d : ι → ℕ) (a : ι → K) :
    ∏ i ∈ s, PowerSeries.monomial (d i) (a i)
      = PowerSeries.monomial (∑ i ∈ s, d i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.prod_insert hx, ih,
        PowerSeries.monomial_mul_monomial]

/-- The multiplicity vectors of total multiplicity `k` and weighted total `n` are the same,
whether described via `piAntidiag` or the (bounded) `piFinset`. -/
private lemma bell_index_set (n k : ℕ) :
    (Finset.univ.piAntidiag k).filter (fun κ : Fin (n + 1) → ℕ => n = ∑ i, (κ i) * (i.val + 1))
      = (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (n + 1))).filter
          (fun j => (∑ i, j i = k) ∧ (∑ i, (i.val + 1) * j i = n)) := by
  ext κ
  simp only [Finset.mem_filter, Finset.mem_piAntidiag, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨⟨hsum, _⟩, hn⟩
    refine ⟨fun i => ?_, hsum, ?_⟩
    · have hle : κ i ≤ ∑ j, (κ j) * (j.val + 1) := by
        calc κ i ≤ (κ i) * (i.val + 1) := Nat.le_mul_of_pos_right _ (by omega)
          _ ≤ ∑ j, (κ j) * (j.val + 1) :=
              Finset.single_le_sum (f := fun j => κ j * (j.val + 1))
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    · calc ∑ i, (i.val + 1) * κ i
            = ∑ i, κ i * (i.val + 1) := Finset.sum_congr rfl (fun i _ => Nat.mul_comm _ _)
        _ = n := hn.symm
  · rintro ⟨_, hsum, hn⟩
    refine ⟨⟨hsum, fun i _ => Finset.mem_univ i⟩, ?_⟩
    calc n = ∑ i, (i.val + 1) * κ i := hn.symm
      _ = ∑ i, κ i * (i.val + 1) := Finset.sum_congr rfl (fun i _ => Nat.mul_comm _ _)

/-- The `k`-th coefficient collection of the partial-Bell / INVERT power series: the `n`-th
coefficient of `C^k` (where `C = ∑_{m≥1} c_m X^m`) equals the Bell term for that `k`. -/
private lemma bell_coeff_pow (c : ℕ → K) (n k : ℕ) :
    PowerSeries.coeff n ((PowerSeries.mk (fun m => if m = 0 then 0 else c m)) ^ k)
      = (k.factorial : K) * ∑ j ∈ (Fintype.piFinset
          (fun _ : Fin (n + 1) => Finset.range (n + 1))).filter
          (fun j => (∑ i, j i = k) ∧ (∑ i, (i.val + 1) * j i = n)),
          ∏ i, ((c (i.val + 1)) ^ (j i) / (((j i).factorial : ℕ) : K)) := by
  have hA : PowerSeries.coeff n ((PowerSeries.mk (fun m => if m = 0 then 0 else c m)) ^ k)
      = PowerSeries.coeff n ((∑ i : Fin (n + 1), PowerSeries.monomial (i.val + 1) (c (i.val + 1))) ^
          k) := by
    set C := PowerSeries.mk (fun m => if m = 0 then 0 else c m) with hCdef
    have hCC : ∀ m, m ≤ n → PowerSeries.coeff m C
        = PowerSeries.coeff m (∑ i : Fin (n + 1), PowerSeries.monomial (i.val + 1)
            (c (i.val + 1))) := by
      intro m hm
      rw [hCdef, PowerSeries.coeff_mk, map_sum]
      simp_rw [PowerSeries.coeff_monomial]
      rw [Fin.sum_univ_eq_sum_range (fun j => if m = j + 1 then c (j + 1) else 0) (n + 1)]
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; simp
      · rw [Finset.sum_eq_single (m - 1)]
        · have h1 : m - 1 + 1 = m := by omega
          rw [h1]; simp [show ¬ m = 0 by omega]
        · intro j _ hjne; rw [ite_eq_right (by omega)]
        · intro hnm; exact absurd (Finset.mem_range.mpr (by omega)) hnm
    rw [PowerSeries.coeff_pow, PowerSeries.coeff_pow]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_finsuppAntidiag] at hl
    apply Finset.prod_congr rfl
    intro i hi
    exact hCC (l i) (by rw [← hl.1]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
  have hB : PowerSeries.coeff n ((∑ i : Fin (n + 1), PowerSeries.monomial (i.val + 1)
      (c (i.val + 1))) ^ k)
      = ∑ κ ∈ (Finset.univ : Finset (Fin (n + 1))).piAntidiag k,
          (↑(Nat.multinomial Finset.univ κ) : K)
            * (if n = ∑ i, (κ i) * (i.val + 1) then ∏ i, c (i.val + 1) ^ (κ i) else 0) := by
    rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum]
    apply Finset.sum_congr rfl
    intro κ _
    have hp : ∏ i, (PowerSeries.monomial (i.val + 1) (c (i.val + 1)) : K⟦X⟧) ^ (κ i)
        = PowerSeries.monomial (∑ i, (κ i) * (i.val + 1)) (∏ i, c (i.val + 1) ^ (κ i)) := by
      simp_rw [PowerSeries.monomial_pow]; rw [prod_monomial]
    rw [hp, ← nsmul_eq_mul, map_nsmul, PowerSeries.coeff_monomial, nsmul_eq_mul]
  rw [hA, hB]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, bell_index_set n k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [Finset.mem_filter, Fintype.mem_piFinset] at hκ
  have hsum : ∑ i, κ i = k := hκ.2.1
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin (n + 1))) κ
  rw [hsum] at hspec
  have hprodne : (∏ i, ((κ i).factorial : K)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _; exact_mod_cast (κ i).factorial_ne_zero
  have hspecR : (∏ i, ((κ i).factorial : K)) * (Nat.multinomial Finset.univ κ : K) =
      (k.factorial : K) := by
    exact_mod_cast hspec
  rw [Finset.prod_div_distrib]
  have hmul : (↑(Nat.multinomial Finset.univ κ) : K) = ↑k.factorial /
      (∏ i, ((κ i).factorial : K)) := by
    rw [eq_div_iff hprodne, mul_comm]; exact hspecR
  rw [hmul]; ring

/-- The INVERT sequence `y` given by the Bell expansion is the inverse of `1 - C` as a power
series, i.e. `y` satisfies `Y * (1 - C) = 1`. -/
private lemma y_invert (c y : ℕ → K)
    (hBell : ∀ n : ℕ, y n = ∑ k ∈ Finset.range (n + 1), (k.factorial : K) *
      ∑ j ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (n + 1))).filter
        (fun j => (∑ i, j i = k) ∧ (∑ i, (i.val + 1) * j i = n)),
      ∏ i, ((c (i.val + 1)) ^ (j i) / (((j i).factorial : ℕ) : K))) :
    (PowerSeries.mk y) * (1 - PowerSeries.mk (fun m => if m = 0 then 0 else c m)) = 1 := by
  have hGeom : ∀ n, y n = ∑ k ∈ Finset.range (n + 1),
      PowerSeries.coeff n ((PowerSeries.mk (fun m => if m = 0 then 0 else c m)) ^ k) := by
    intro n
    rw [hBell n]
    exact Finset.sum_congr rfl (fun k _ => (bell_coeff_pow c n k).symm)
  set C := PowerSeries.mk (fun m => if m = 0 then 0 else c m) with hCdef
  have hCkzero : ∀ a k, a < k → PowerSeries.coeff a (C ^ k) = 0 := by
    intro a k h
    have hX : (PowerSeries.X : K⟦X⟧) ∣ C := by
      rw [PowerSeries.X_dvd_iff]; simp [hCdef, PowerSeries.constantCoeff_mk]
    have hdvd : (PowerSeries.X : K⟦X⟧) ^ k ∣ C ^ k := pow_dvd_pow_of_dvd hX k
    rw [PowerSeries.X_pow_dvd_iff] at hdvd
    exact hdvd a h
  have hyk : ∀ m, PowerSeries.coeff m (PowerSeries.mk y) = y m := fun m => PowerSeries.coeff_mk m y
  apply PowerSeries.ext
  intro n
  have hGn : PowerSeries.coeff n ((PowerSeries.mk y) * (1 - C))
      = PowerSeries.coeff n ((∑ k ∈ Finset.range (n + 1), C ^ k) * (1 - C)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hp1 : p.1 ≤ n := by omega
    congr 1
    rw [hyk, hGeom p.1, map_sum]
    refine Finset.sum_subset ?_ ?_
    · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    · intro k _ hknot
      rw [Finset.mem_range] at hknot
      exact hCkzero p.1 k (by omega)
  have hgeomseries : (∑ k ∈ Finset.range (n + 1), C ^ k) * (1 - C) = 1 - C ^ (n + 1) := by
    have hg := geom_sum_mul C (n + 1)
    linear_combination -hg
  rw [hGn, hgeomseries, map_sub, PowerSeries.coeff_one, hCkzero n (n + 1) (Nat.lt_succ_self n)]
  simp

omit [CharZero K] in
/-- The `r`-fold convolution `conv N` equals the `N`-th coefficient of `Y ^ r`. -/
private lemma conv_eq_coeff (y : ℕ → K) (r N : ℕ) :
    (∑ f ∈ Finset.univ.filter (fun f : Fin r → Fin (N + 1) => ∑ i, (f i).val = N),
        ∏ i, y ((f i).val))
      = PowerSeries.coeff N ((PowerSeries.mk y) ^ r) := by
  rw [PowerSeries.coeff_pow]
  simp only [PowerSeries.coeff_mk]
  refine Finset.sum_nbij'
    (i := fun f => Finsupp.onFinset (Finset.range r)
        (fun j => if h : j < r then (f ⟨j, h⟩).val else 0) ?_)
    (j := fun l => fun i : Fin r => (⟨min (l i.val) N, by omega⟩ : Fin (N + 1)))
    ?hi ?hj ?hleft ?hright ?hval
  · intro j hj
    rw [Finset.mem_range]
    by_contra h
    rw [dite_eq_right_iff.mpr (fun hh => absurd hh h)] at hj
    exact hj rfl
  case hi =>
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finsupp.support_onFinset_subset⟩
    have step : (Finset.range r).sum (Finsupp.onFinset (Finset.range r)
        (fun j => if h : j < r then (f ⟨j, h⟩).val else 0) (by
          intro j hj; rw [Finset.mem_range]; by_contra h
          rw [dite_eq_right_iff.mpr (fun hh => absurd hh h)] at hj; exact hj rfl))
        = ∑ i : Fin r, (f i).val := by
      rw [Finset.sum_congr rfl (fun j _ => Finsupp.onFinset_apply ..)]
      rw [Finset.sum_range (fun j => if h : j < r then (f ⟨j, h⟩).val else 0)]
      exact Finset.sum_congr rfl (fun i _ => by rw [dite_eq_left i.2])
    rw [step, hf.2]
  case hj =>
    intro l hl
    rw [Finset.mem_finsuppAntidiag] at hl
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have key : ∀ i : Fin r, min (l i.val) N = l i.val := fun i =>
      Nat.min_eq_left (hl.1 ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr i.2))
    change ∑ i : Fin r, min (l i.val) N = N
    calc ∑ i : Fin r, min (l i.val) N = ∑ i : Fin r, l i.val := by simp only [key]
      _ = ∑ j ∈ Finset.range r, l j := (Finset.sum_range _).symm
      _ = N := hl.1
  case hleft =>
    intro f hf
    funext i
    apply Fin.ext
    change min ((Finsupp.onFinset (Finset.range r)
        (fun j => if h : j < r then (f ⟨j, h⟩).val else 0) _) i.val) N = (f i).val
    rw [Finsupp.onFinset_apply, dite_eq_left i.2, Fin.eta]
    exact Nat.min_eq_left (Nat.lt_succ_iff.mp (f i).2)
  case hright =>
    intro l hl
    rw [Finset.mem_finsuppAntidiag] at hl
    apply Finsupp.ext
    intro j
    rw [Finsupp.onFinset_apply]
    by_cases h : j < r
    · rw [dite_eq_left h]
      change min (l j) N = l j
      exact Nat.min_eq_left (hl.1 ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr h))
    · rw [dite_eq_right h]
      symm
      by_contra hne
      exact h (Finset.mem_range.mp (hl.2 (Finsupp.mem_support_iff.mpr hne)))
  case hval =>
    intro f _
    simp only [Finsupp.onFinset_apply]
    rw [Finset.prod_range (fun j => y (if h : j < r then (f ⟨j, h⟩).val else 0))]
    exact Finset.prod_congr rfl (fun i _ => by rw [dite_eq_left i.2, Fin.eta])

/-- The linear recurrence at the level of power-series coefficients, from the ODE
`F' * (1 - C) = r • (F * C')`. -/
private lemma extraction (c y : ℕ → K) (r : ℕ) (hr : 0 < r)
    (hMain : PowerSeries.derivative ((PowerSeries.mk y) ^ r)
          * (1 - PowerSeries.mk (fun m => if m = 0 then 0 else c m))
        = r • (((PowerSeries.mk y) ^ r)
          * PowerSeries.derivative (PowerSeries.mk (fun m => if m = 0 then 0 else c m))))
    (n : ℕ) (hn : 1 ≤ n) :
    (n : K) * PowerSeries.coeff n ((PowerSeries.mk y) ^ r)
      = ∑ m ∈ Finset.Icc 1 n,
          ((n + m * (r - 1) : ℕ) : K) * c m * PowerSeries.coeff (n - m)
              ((PowerSeries.mk y) ^ r) := by
  set C := PowerSeries.mk (fun m => if m = 0 then 0 else c m) with hCdef
  set F := (PowerSeries.mk y) ^ r with hFdef
  have hCk : ∀ m, PowerSeries.coeff m C = if m = 0 then 0 else c m := fun m => PowerSeries.coeff_mk
      m _
  have hLHS : PowerSeries.coeff (n - 1) (PowerSeries.derivative F) = (n : K) * PowerSeries.coeff n
      F := by
    rw [PowerSeries.coeff_derivative]
    have e1 : n - 1 + 1 = n := by omega
    have e2 : (↑(n - 1) : K) + 1 = ↑n := by push_cast [Nat.cast_sub hn]; ring
    rw [e1, e2]; ring
  have hsplit : PowerSeries.coeff (n - 1) (PowerSeries.derivative F)
      = PowerSeries.coeff (n - 1) (PowerSeries.derivative F * (1 - C))
        + PowerSeries.coeff (n - 1) (PowerSeries.derivative F * C) := by
    rw [← map_add]; congr 1; ring
  have hM : PowerSeries.coeff (n - 1) (PowerSeries.derivative F * (1 - C))
      = (r : K) * PowerSeries.coeff (n - 1) (F * PowerSeries.derivative C) := by
    rw [hMain, map_nsmul, nsmul_eq_mul]
  have hA : PowerSeries.coeff (n - 1) (F * PowerSeries.derivative C)
      = ∑ m ∈ Finset.Icc 1 n, PowerSeries.coeff (n - m) F * (c m * (m : K)) := by
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_nbij' (i := fun p => p.2 + 1) (j := fun m => (n - m, m - 1)) ?_ ?_ ?_ ?_ ?_
    · intro p hp; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp; rw [Finset.mem_Icc]; omega
    · intro m hm; rw [Finset.mem_Icc] at hm; rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
    · intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have h1 : n - (p.2 + 1) = p.1 := by omega
      simp [h1]
    · intro m hm; rw [Finset.mem_Icc] at hm; omega
    · intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [PowerSeries.coeff_derivative, hCk]
      have h1 : p.2 + 1 ≠ 0 := by omega
      have h2 : n - (p.2 + 1) = p.1 := by omega
      simp only [h1, ite_false, h2]; push_cast; ring
  have hB : PowerSeries.coeff (n - 1) (PowerSeries.derivative F * C)
      = ∑ m ∈ Finset.Icc 1 n, PowerSeries.coeff (n - m) F * ((↑(n - m) : K) * c m) := by
    have step1 : PowerSeries.coeff (n - 1) (PowerSeries.derivative F * C)
        = ∑ m ∈ Finset.range n,
            PowerSeries.coeff (n - m) F * ((↑(n - m) : K) * (if m = 0 then (0 : K) else c m)) := by
      rw [PowerSeries.coeff_mul]
      refine Finset.sum_nbij' (i := fun p => p.2) (j := fun m => (n - 1 - m, m)) ?_ ?_ ?_ ?_ ?_
      · intro p hp; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp; rw [Finset.mem_range]; omega
      · intro m hm; rw [Finset.mem_range] at hm; rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
      · intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        have h1 : n - 1 - p.2 = p.1 := by omega
        simp [h1]
      · intro m hm; rfl
      · intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [PowerSeries.coeff_derivative, hCk]
        have h2 : p.1 + 1 = n - p.2 := by omega
        rw [← h2]; push_cast; ring
    rw [step1]
    have hins1 : Finset.range n = insert 0 (Finset.Ico 1 n) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
    have hins2 : Finset.Icc 1 n = insert n (Finset.Ico 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hins1, hins2, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    have z1 : PowerSeries.coeff (n - 0) F *
        ((↑(n - 0) : K) * (if (0 : ℕ) = 0 then (0 : K) else c 0)) = 0 := by simp
    have z2 : PowerSeries.coeff (n - n) F * ((↑(n - n) : K) * c n) = 0 := by simp
    rw [z1, z2, zero_add, zero_add]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Ico] at hm
    have : m ≠ 0 := by omega
    simp [this]
  rw [← hLHS, hsplit, hM, hA, hB, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  have hcast : ((n + m * (r - 1) : ℕ) : K) = (r : K) * ↑m + ↑(n - m) := by
    push_cast [Nat.cast_sub hm.2, Nat.cast_sub hr]; ring
  rw [hcast]; ring

/-- **Linear recurrence for INVERT convolution powers in characteristic zero.** Let $K$ be a
field of characteristic zero and let $(c_m)_{m \ge 0}$ and $(y_n)_{n \ge 0}$ be sequences in $K$
such that for every $n \ge 0$

$$y_n = \sum_{k=0}^{n} k! \sum_{j} \prod_{i=1}^{n+1} \frac{c_i^{j_i}}{j_i!},$$

where the inner sum runs over all tuples $(j_1, \dots, j_{n+1})$ of integers with
$0 \le j_i \le n$, $j_1 + j_2 + \dots + j_{n+1} = k$ and $j_1 + 2 j_2 + \dots + (n+1) j_{n+1} = n$.
Let $r \ge 1$ be an integer, and for $N \ge 0$ let $y^{(r)}_N$ be the sum of
$y_{a_1} y_{a_2} \cdots y_{a_r}$ over all tuples $(a_1, \dots, a_r)$ of nonnegative integers with
$a_1 + \dots + a_r = N$. Then for every $n \ge 1$

$$n \, y^{(r)}_n = \sum_{m=1}^{n} \bigl(n + m(r-1)\bigr) \, c_m \, y^{(r)}_{n-m}.$$

The hypothesis says that $y_n = \sum_{k=0}^{n} \frac{k!}{n!} B_{n,k}(1!\,c_1, 2!\,c_2, \dots)$
with the partial Bell polynomials $B_{n,k}$, that is, $y$ is the INVERT transform of $c$: as
formal power series in $z$, $\sum_{n \ge 0} y_n z^n = 1/(1 - \sum_{m \ge 1} c_m z^m)$. The value
$c_0$ plays no role, and the theorem for real sequences is the case $K = \mathbb{R}$. -/
theorem bell_convolution_linear_recurrence_of_charZero (c : ℕ → K) (y : ℕ → K)
    (r : ℕ) (hr : 0 < r)
    (hBell : ∀ n : ℕ, y n = ∑ k ∈ Finset.range (n + 1), (k.factorial : K) *
      ∑ j ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (n + 1))).filter
        (fun j => (∑ i, j i = k) ∧ (∑ i, (i.val + 1) * j i = n)),
      ∏ i, ((c (i.val + 1)) ^ (j i) / (((j i).factorial : ℕ) : K)))
    (n : ℕ) (hn : 1 ≤ n) :
    let conv : ℕ → K := fun N =>
      ∑ f ∈ Finset.univ.filter
        (fun f : Fin r → Fin (N + 1) => ∑ i, (f i).val = N),
      ∏ i, y ((f i).val);
    (n : K) * conv n = ∑ m ∈ Finset.Icc 1 n, ((n + m * (r - 1) : ℕ) : K) * c m * conv (n - m) := by
  intro conv
  set C := PowerSeries.mk (fun m => if m = 0 then 0 else c m) with hCdef
  set Y := PowerSeries.mk y with hYdef
  have hYC : Y * (1 - C) = 1 := y_invert c y hBell
  have hMain : PowerSeries.derivative (Y ^ r) * (1 - C) = r •
      ((Y ^ r) * PowerSeries.derivative C) := by
    have hY' : PowerSeries.derivative Y * (1 - C) = Y * PowerSeries.derivative C := by
      have h1 : PowerSeries.derivative (Y * (1 - C)) =
          0 := by rw [hYC]; exact Derivation.map_one_eq_zero _
      rw [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero] at h1
      simp only [smul_eq_mul, zero_sub, mul_neg] at h1
      linear_combination h1
    have hpow : Y ^ (r - 1) * Y = Y ^ r := by rw [← pow_succ]; congr 1; omega
    calc PowerSeries.derivative (Y ^ r) * (1 - C)
        = r • (Y ^ (r - 1) * PowerSeries.derivative Y) * (1 - C) := by
          rw [Derivation.leibniz_pow]; rw [smul_eq_mul (a := Y ^ (r - 1))]
      _ = r • (Y ^ (r - 1) * (PowerSeries.derivative Y *
          (1 - C))) := by rw [smul_mul_assoc, mul_assoc]
      _ = r • (Y ^ (r - 1) * (Y * PowerSeries.derivative C)) := by rw [hY']
      _ = r • ((Y ^ (r - 1) * Y) * PowerSeries.derivative C) := by rw [mul_assoc]
      _ = r • (Y ^ r * PowerSeries.derivative C) := by rw [hpow]
  have hconv : ∀ N, conv N = PowerSeries.coeff N (Y ^ r) := fun N => conv_eq_coeff y r N
  simp only [hconv]
  exact extraction c y r hr hMain n hn

/--
**Linear recurrence for convolution powers of an INVERT sequence.** Let $(c_m)_{m \ge 0}$ and
$(y_n)_{n \ge 0}$ be real sequences such that for every $n \ge 0$

$$y_n = \sum_{k=0}^{n} k! \sum_{j} \prod_{i=1}^{n+1} \frac{c_i^{j_i}}{j_i!},$$

where the inner sum runs over all tuples $(j_1, \dots, j_{n+1})$ of integers with
$0 \le j_i \le n$, $j_1 + j_2 + \dots + j_{n+1} = k$ and $j_1 + 2 j_2 + \dots + (n+1) j_{n+1} = n$.
Let $r \ge 1$ be an integer, and for $N \ge 0$ let $y^{(r)}_N$ be the sum of
$y_{a_1} y_{a_2} \cdots y_{a_r}$ over all tuples $(a_1, \dots, a_r)$ of nonnegative integers with
$a_1 + \dots + a_r = N$. Then for every $n \ge 1$

$$n \, y^{(r)}_n = \sum_{m=1}^{n} \bigl(n + m(r-1)\bigr) \, c_m \, y^{(r)}_{n-m}.$$

The hypothesis says that $y_n = \sum_{k=0}^{n} \frac{k!}{n!} B_{n,k}(1!\,c_1, 2!\,c_2, \dots)$
with the partial Bell polynomials $B_{n,k}$, that is, $y$ is the INVERT transform of $c$: as
formal power series in $z$, $\sum_{n \ge 0} y_n z^n = 1/(1 - \sum_{m \ge 1} c_m z^m)$. The value
$c_0$ plays no role.

Proves `Wanted` entry `bell_convolution_linear_recurrence`.

Source: Daniel Birmajer, Juan B. Gil, and Michael D. Weiner, "Linear Recurrence
Sequences and Their Convolutions via Bell Polynomials," Journal of Integer
Sequences 18 (2015), Article 15.1.2, Theorem (label `thm:linearRecurrence`),
equation (label `eq:linearRecurrence`), lines 425–435,
https://cs.uwaterloo.ca/journals/JIS/VOL18/Gil/gil3.tex
-/
theorem bell_convolution_linear_recurrence (c : ℕ → ℝ) (y : ℕ → ℝ)
    (r : ℕ) (hr : 0 < r)
    (hBell : ∀ n : ℕ, y n = ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ) *
      ∑ j ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (n + 1))).filter
        (fun j => (∑ i, j i = k) ∧ (∑ i, (i.val + 1) * j i = n)),
      ∏ i, ((c (i.val + 1)) ^ (j i) / (((j i).factorial : ℕ) : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    let conv : ℕ → ℝ := fun N =>
      ∑ f ∈ Finset.univ.filter
        (fun f : Fin r → Fin (N + 1) => ∑ i, (f i).val = N),
      ∏ i, y ((f i).val);
    (n : ℝ) * conv n = ∑ m ∈ Finset.Icc 1 n, ((n + m * (r - 1) : ℕ) : ℝ) * c m * conv (n - m) :=
  bell_convolution_linear_recurrence_of_charZero c y r hr hBell n hn

/-- The multinomial coefficient in each summand of `partialBellPolynomial` is an exact quotient. -/
private lemma partialBell_coeff_dvd {n : ℕ} (m : Fin (n + 1) → ℕ)
    (hm : ∑ i, (i.val + 1) * m i = n) :
    ∏ i, (m i).factorial * (i.val + 1).factorial ^ m i ∣ n.factorial := by
  calc ∏ i, (m i).factorial * (i.val + 1).factorial ^ m i
      ∣ ∏ i, ((i.val + 1) * m i).factorial := Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
        Dvd.intro_left (Nat.uniformBell (m i) (i.val + 1)) (by
          rw [mul_comm (i.val + 1), ← Nat.uniformBell_mul_eq (m i) (Nat.succ_ne_zero i.val)]
          ring)
    _ ∣ (∑ i, (i.val + 1) * m i).factorial := Nat.prod_factorial_dvd_factorial_sum _ _
    _ = n.factorial := by rw [hm]

/-- The `k`-th summand of `hBell` is the normalized partial Bell polynomial
`k! / n! * B_(n,k)(1! c₁, 2! c₂, ...)`. -/
private lemma bell_summand_eq_partialBellPolynomial (c : ℕ → K) (n k : ℕ) :
    (k.factorial : K) *
      ∑ j ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (n + 1))).filter
        (fun j => (∑ i, j i = k) ∧ (∑ i, (i.val + 1) * j i = n)),
      ∏ i, ((c (i.val + 1)) ^ (j i) / (((j i).factorial : ℕ) : K))
    = (k.factorial : K) / n.factorial *
      partialBellPolynomial n k (fun m => (m.factorial : K) * c m) := by
  rw [partialBellPolynomial, div_mul_eq_mul_div, mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun _ _ => and_comm) fun j hj => ?_
  have hdvd := partialBell_coeff_dvd j (Finset.mem_filter.mp hj).2.1
  have hP : ((∏ i, (j i).factorial * (i.val + 1).factorial ^ j i : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_of_dvd_of_pos hdvd n.factorial_pos).ne'
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [Nat.cast_div hdvd hP]
  push_cast at hP ⊢
  rw [Finset.prod_mul_distrib] at hP ⊢
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_div_distrib]
  obtain ⟨hB, hP'⟩ := mul_ne_zero_iff.mp hP
  field_simp

/--
**Linear recurrence for INVERT convolution powers via partial Bell polynomials.** Let $K$ be a
field of characteristic zero, let $(c_m)_{m \ge 0}$ and $(y_n)_{n \ge 0}$ be sequences in $K$, and
write $B_{n,k}$ for the partial Bell polynomial. Suppose that for every $n \ge 0$

$$y_n = \sum_{k=0}^{n} \frac{k!}{n!} \, B_{n,k}(x_1, x_2, \dots), \qquad x_m = m! \, c_m.$$

Let $r \ge 1$ be an integer, and for $N \ge 0$ let $y^{(r)}_N$ be the sum of
$y_{a_1} y_{a_2} \cdots y_{a_r}$ over all tuples $(a_1, \dots, a_r)$ of nonnegative integers with
$a_1 + \dots + a_r = N$. Then for every $n \ge 1$

$$n \, y^{(r)}_n = \sum_{m=1}^{n} \bigl(n + m(r-1)\bigr) \, c_m \, y^{(r)}_{n-m}.$$
-/
theorem bell_convolution_linear_recurrence_partialBellPolynomial (c : ℕ → K) (y : ℕ → K)
    (r : ℕ) (hr : 0 < r)
    (hBell : ∀ n : ℕ, y n = ∑ k ∈ Finset.range (n + 1), (k.factorial : K) / n.factorial *
      partialBellPolynomial n k (fun m => (m.factorial : K) * c m))
    (n : ℕ) (hn : 1 ≤ n) :
    let conv : ℕ → K := fun N =>
      ∑ f ∈ Finset.univ.filter
        (fun f : Fin r → Fin (N + 1) => ∑ i, (f i).val = N),
      ∏ i, y ((f i).val);
    (n : K) * conv n = ∑ m ∈ Finset.Icc 1 n, ((n + m * (r - 1) : ℕ) : K) * c m * conv (n - m) :=
  bell_convolution_linear_recurrence_of_charZero c y r hr
    (fun n => by simp only [hBell, bell_summand_eq_partialBellPolynomial]) n hn

end MetaMathlibExt
