/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Recurrences for step-`k` sums of binomial coefficients and Riordan arrays

Statements from Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial
Coefficients and Some Generalizations*, Journal of Integer Sequences 27 (2024),
Article 24.3.4.

The Riordan-array step sums are coefficients of a geometric series. For a rational Riordan
array, the step sums of all residues modulo the step therefore satisfy one common linear
recurrence with integer coefficients. A linear recurrence propagates any other linear recurrence
that holds on a sufficiently long initial window. For binomial step sums, multiplication in the
cyclic group algebra gives such a recurrence starting from any row of Pascal's triangle.
-/

namespace MetaMathlibExt

/-- **Finite window criterion for linear recurrences.** Let $R$ be a commutative ring, let
$x, A, a : \mathbb{N} \to R$ and let $r, s, N \in \mathbb{N}$. Suppose that
$x_n = \sum_{i=1}^{r} A_i x_{n-i}$ for all $n \ge r$, that $N \ge r + s - 1$, and that
$x_n = \sum_{i=1}^{s} a_i x_{n-i}$ for all $n$ with $s \le n \le N$. Then
$x_n = \sum_{i=1}^{s} a_i x_{n-i}$ for all $n \ge s$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 1. -/
public theorem linearRecurrence_of_finite_window {R : Type*} [CommRing R]
    (x A a : ℕ → R) (r s N : ℕ)
    (hA : ∀ n, r ≤ n → x n = ∑ i ∈ Finset.Icc 1 r, A i * x (n - i))
    (hN : r + s - 1 ≤ N)
    (ha : ∀ n, s ≤ n → n ≤ N → x n = ∑ i ∈ Finset.Icc 1 s, a i * x (n - i)) :
    ∀ n, s ≤ n → x n = ∑ i ∈ Finset.Icc 1 s, a i * x (n - i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hsn
    by_cases hn : n ≤ N
    · exact ha n hsn hn
    have hrs : r + s ≤ n := by omega
    calc
      x n = ∑ i ∈ Finset.Icc 1 r, A i * x (n - i) := hA n (by omega)
      _ = ∑ i ∈ Finset.Icc 1 r, ∑ j ∈ Finset.Icc 1 s,
          A i * (a j * x (n - i - j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨hi₁, hir⟩ := Finset.mem_Icc.mp hi
        rw [ih (n - i) (by omega) (by omega), Finset.mul_sum]
      _ = ∑ j ∈ Finset.Icc 1 s, ∑ i ∈ Finset.Icc 1 r,
          a j * (A i * x (n - j - i)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Nat.sub_right_comm, mul_left_comm]
      _ = ∑ j ∈ Finset.Icc 1 s, a j * x (n - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjs := (Finset.mem_Icc.mp hj).2
        rw [← Finset.mul_sum, ← hA (n - j) (by omega)]

private theorem linearRecurrence_of_powers {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [StrongRankCondition R] [Module.Finite R A] [Module.Free R A] (t : A) (f : A →ₗ[R] R) :
    ∃ a : ℕ → R, ∀ n, Module.finrank R A ≤ n →
      f (t ^ n) = ∑ i ∈ Finset.Icc 1 (Module.finrank R A), a i * f (t ^ (n - i)) := by
  let T := Algebra.lmul R A t
  let P := T.charpoly
  let k := Module.finrank R A
  have hdeg : P.natDegree = k := T.charpoly_natDegree
  have hlead : P.coeff k = 1 := hdeg ▸ T.charpoly_monic.coeff_natDegree
  refine ⟨fun i ↦ -P.coeff (k - i), fun n hn ↦ ?_⟩
  have hP : ∑ j ∈ Finset.range (k + 1), P.coeff j • t ^ j = 0 := by
    have h : Polynomial.aeval t P = 0 := Algebra.aeval_self_charpoly_lmul t
    rwa [Polynomial.aeval_eq_sum_range, hdeg] at h
  -- Shift to time `n`, then reverse the polynomial indices to count lags.
  have hzero := congrArg (fun z : A ↦ f (t ^ (n - k) * z)) hP
  simp only [Finset.mul_sum, Algebra.mul_smul_comm, ← pow_add, map_sum, map_smul,
    smul_eq_mul, mul_zero, map_zero] at hzero
  rw [← Finset.sum_range_reflect (fun j ↦ P.coeff j * f (t ^ (n - k + j))),
    Nat.add_sub_cancel, Finset.sum_range_eq_add_Ico _ (Nat.succ_pos k),
    Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc, Nat.sub_zero, hlead, one_mul,
    Nat.sub_add_cancel hn] at hzero
  have hsum : (∑ i ∈ Finset.Icc 1 k, P.coeff (k - i) * f (t ^ (n - k + (k - i)))) =
      ∑ i ∈ Finset.Icc 1 k, P.coeff (k - i) * f (t ^ (n - i)) := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have := (Finset.mem_Icc.mp hi).2
    rw [show n - k + (k - i) = n - i by omega]
  rw [hsum] at hzero
  simpa only [neg_mul, Finset.sum_neg_distrib] using eq_neg_of_add_eq_zero_left hzero

section BinomialStepSums

variable (k : ℕ)

local notation "A" => AddMonoidAlgebra ℤ (ZMod k)

/-- Multiplication by this element advances `α` rows of Pascal's triangle and shifts the
residue indices by `-γ`. The group algebra collects coefficients at congruent indices. -/
private noncomputable def binomialStepElement (α γ : ℕ) : A :=
  AddMonoidAlgebra.single (-(γ : ZMod k)) 1 * (AddMonoidAlgebra.single 1 1 + 1) ^ α

private noncomputable def binomialResidue (p : ZMod k) : A →ₗ[ℤ] ℤ :=
  (Finsupp.lapply p).comp (AddMonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

private theorem binomialStepElement_pow_coeff (α β γ p n : ℕ) :
    binomialResidue k (p : ZMod k)
        (binomialStepElement k α γ ^ n * (AddMonoidAlgebra.single 1 1 + 1) ^ β) =
      ∑ m ∈ (Finset.range (α * n + β + 1)).filter (fun m => m % k = (γ * n + p) % k),
        ((α * n + β).choose m : ℤ) := by
  have hshift : n • -(γ : ZMod k) = -((γ * n : ℕ) : ZMod k) := by
    simp [nsmul_eq_mul, mul_comm]
  rw [binomialStepElement, mul_pow, AddMonoidAlgebra.single_pow, hshift, one_pow, ← pow_mul,
    mul_assoc, ← pow_add, add_pow, Finset.mul_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [one_pow, mul_one, AddMonoidAlgebra.single_pow, nsmul_one, one_pow, ← mul_assoc,
    AddMonoidAlgebra.single_mul_single, mul_one, ← nsmul_eq_mul', map_nsmul]
  change (α * n + β).choose m • (AddMonoidAlgebra.single (-(↑(γ * n) : ZMod k) + ↑m) (1 : ℤ)).coeff
    (p : ZMod k) = _
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, neg_add_eq_iff_eq_add,
    ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
  split <;> simp

-- Multiplying by the initial row changes the coefficient functional on powers of the step.
private theorem shiftedBinomialStepSum_recurrence_of_window.exists_recurrence [NeZero k]
    (α β γ p : ℕ) :
    let c : ℕ → ℤ := fun n =>
      ∑ m ∈ (Finset.range (α * n + β + 1)).filter (fun m => m % k = (γ * n + p) % k),
        ((α * n + β).choose m : ℤ)
    ∃ a : ℕ → ℤ, ∀ n, k ≤ n → c n = ∑ i ∈ Finset.Icc 1 k, a i * c (n - i) := by
  let b := AddMonoidAlgebra.basis (ZMod k) ℤ
  let := Module.Free.of_basis b
  let := Module.Finite.of_basis b
  have hdim : Module.finrank ℤ A = k := (Module.finrank_eq_card_basis b).trans (ZMod.card k)
  let row : A := (AddMonoidAlgebra.single 1 1 + 1) ^ β
  obtain ⟨a, ha⟩ := linearRecurrence_of_powers (binomialStepElement k α γ)
    ((binomialResidue k p).comp (LinearMap.mulRight ℤ row))
  exact ⟨a, by simpa only [hdim, LinearMap.comp_apply, LinearMap.mulRight_apply, row,
    binomialStepElement_pow_coeff] using ha⟩

end BinomialStepSums

-- The residue-vector proof only needs `k ≠ 0`; retain the hypotheses and named arguments.
set_option linter.unusedVariables false in
/-- **Window criterion for step sums of binomial coefficients.** Let $\alpha, k, \gamma, p, s$
be natural numbers with $\alpha > 1$, $k > 1$, $\gamma \ge 1$ and $p < k$, and let
$\delta_1, \delta_2, \ldots$ be integers. For $n \in \mathbb{N}$ let $c(n)$ be the sum of
$\binom{\alpha n}{m}$ over all $m$ with $0 \le m \le \alpha n$ and
$m \equiv \gamma n + p \pmod{k}$, that is, $c(n) = \sum_{j \in \mathbb{Z}}
\binom{\alpha n}{\gamma n + p + kj}$. If $c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n$
with $s \le n \le k^2 + s - 1$, then $c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n \ge s$.

The coefficients $\delta_i$ need only work for this one residue $p$; the source's hypothesis,
with one family $\delta_i$ for every $p$, is a special case.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 8. -/
public theorem binomialStepSum_recurrence_of_window (α k γ p s : ℕ) (hα : 1 < α)
    (hk : 1 < k) (hγ : 1 ≤ γ) (hp : p < k) (δ : ℕ → ℤ) :
    let c : ℕ → ℤ := fun n =>
      ∑ m ∈ (Finset.range (α * n + 1)).filter (fun m => m % k = (γ * n + p) % k),
        ((α * n).choose m : ℤ)
    (∀ n, s ≤ n → n ≤ k ^ 2 + s - 1 → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)) →
      ∀ n, s ≤ n → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i) := by
  intro c hc
  let : NeZero k := ⟨by omega⟩
  obtain ⟨a, ha⟩ := shiftedBinomialStepSum_recurrence_of_window.exists_recurrence k α 0 γ p
  exact linearRecurrence_of_finite_window c a δ k s (k ^ 2 + s - 1) ha
    (by have : k ≤ k ^ 2 := Nat.le_pow (by decide); omega) hc

-- As for the unshifted sums, the recurrence only needs the modulus to be nonzero.
set_option linter.unusedVariables false in
/-- **Window criterion for shifted step sums of binomial coefficients.** Let
$\alpha, \beta, k, \gamma, p, s$ be natural numbers with $\alpha > 1$, $k > 1$, $\gamma > 1$ and
$p < k$, and let $\delta_1, \delta_2, \ldots$ be integers. For $n \in \mathbb{N}$ let $c(n)$ be
the sum of $\binom{\alpha n + \beta}{m}$ over all $m$ with $0 \le m \le \alpha n + \beta$ and
$m \equiv \gamma n + p \pmod{k}$, that is,
$c(n) = \sum_{j \in \mathbb{Z}} \binom{\alpha n + \beta}{\gamma n + p + kj}$. If
$c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n$ with $s \le n \le k^2 + s - 1$, then
$c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n \ge s$.

The coefficients $\delta_i$ need only work for this one residue $p$; the source's hypothesis,
with one family $\delta_i$ for every $p$, is a special case.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Theorem 9. -/
public theorem shiftedBinomialStepSum_recurrence_of_window (α β k γ p s : ℕ)
    (hα : 1 < α) (hk : 1 < k) (hγ : 1 < γ) (hp : p < k) (δ : ℕ → ℤ) :
    let c : ℕ → ℤ := fun n =>
      ∑ m ∈ (Finset.range (α * n + β + 1)).filter (fun m => m % k = (γ * n + p) % k),
        ((α * n + β).choose m : ℤ)
    (∀ n, s ≤ n → n ≤ k ^ 2 + s - 1 → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)) →
      ∀ n, s ≤ n → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i) := by
  intro c hc
  let : NeZero k := ⟨by omega⟩
  obtain ⟨a, ha⟩ := shiftedBinomialStepSum_recurrence_of_window.exists_recurrence k α β γ p
  exact linearRecurrence_of_finite_window c a δ k s (k ^ 2 + s - 1) ha
    (by have : k ≤ k ^ 2 := Nat.le_pow (by decide); omega) hc

/-- The step-sum formula of `riordan_stepSum_coeff` for every step `k ≥ 1`; the rational case
below also needs the step `k = 1`. -/
private theorem rationalRiordan_stepSum_linearRecurrence.stepSum_coeff {K : Type*} [Field K]
    (g h : PowerSeries K) (hh : PowerSeries.constantCoeff h = 0) (k p : ℕ) (hk : 1 ≤ k)
    (hp : p < k) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff n (g * h ^ (k * j + p)) =
      PowerSeries.coeff n (g * h ^ p * (1 - h ^ k)⁻¹) := by
  let q := h ^ k
  let u := g * h ^ p * (1 - q)⁻¹
  have hk₀ : k ≠ 0 := (lt_of_le_of_lt (Nat.zero_le p) hp).ne'
  have hq : PowerSeries.constantCoeff q = 0 := by
    simp only [q, map_pow, hh, zero_pow hk₀]
  have hunit : PowerSeries.constantCoeff (1 - q) ≠ 0 := by simp [hq]
  have hu : u * (1 - q) = g * h ^ p := by
    rw [show u = g * h ^ p * (1 - q)⁻¹ from rfl, mul_assoc,
      PowerSeries.inv_mul_cancel _ hunit, mul_one]
  have hdegree : n < k * (n + 1) := by
    refine (Nat.lt_succ_self n).trans_le ?_
    simpa only [one_mul] using Nat.mul_le_mul_right (n + 1) hk
  have horder : (n : ℕ∞) < (q ^ (n + 1)).order := by
    change (n : ℕ∞) < ((h ^ k) ^ (n + 1)).order
    rw [← pow_mul]
    have hcast : (n : ℕ∞) < ((k * (n + 1) : ℕ) : ℕ∞) := by exact_mod_cast hdegree
    exact hcast.trans_le (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ hh)
  calc
    _ = PowerSeries.coeff n (g * h ^ p * ∑ j ∈ Finset.range (n + 1), q ^ j) := by
      rw [Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [q, pow_mul, pow_add]
      congr 1
      ac_rfl
    _ = PowerSeries.coeff n (u * (1 - q ^ (n + 1))) := by
      rw [← geom_sum_mul_neg q (n + 1), ← hu]
      congr 1
      ac_rfl
    _ = _ := PowerSeries.coeff_mul_one_sub_of_lt_order n horder

/-- **Step sums along a Riordan array.** Let $K$ be a field, let $g, h \in K[[x]]$ with
$h(0) = 0$, and write $d(n, m) = [x^n]\, g(x) h(x)^m$. Then for all natural numbers $k > 1$,
$p < k$ and $n$,
$\sum_{j=0}^{n} d(n, kj + p) = [x^n]\, g(x) h(x)^p (1 - h(x)^k)^{-1}$.

Since $h(0) = 0$, $d(n, m) = 0$ for $m > n$, so the left side is the full sum over all
$j \ge 0$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 5. -/
public theorem riordan_stepSum_coeff {K : Type*} [Field K] (g h : PowerSeries K)
    (hh : PowerSeries.constantCoeff h = 0) (k p : ℕ) (hk : 1 < k) (hp : p < k) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff n (g * h ^ (k * j + p)) =
      PowerSeries.coeff n (g * h ^ p * (1 - h ^ k)⁻¹) :=
  rationalRiordan_stepSum_linearRecurrence.stepSum_coeff g h hh k p hk.le hp n

section RationalRiordan

open Polynomial

-- `hh₁` is kept from the statement: it makes `h` have order exactly `ν`, which the recurrence
-- does not need.
set_option linter.unusedVariables false in
/-- **Step sums of a rational Riordan array satisfy a common recurrence.** Let
$g_1, g_2, h_1, h_2 \in \mathbb{Z}[x]$ with $g_2(0) = h_1(0) = h_2(0) = 1$, let $\nu \ge 1$ and
$k \ge 1$ be natural numbers, and in $\mathbb{Q}[[x]]$ let $g = g_1/g_2$ and
$h = x^\nu h_1/h_2$. For $p, n \in \mathbb{N}$ let
$a_p(n) = \sum_{j=0}^{n} [x^n]\, g h^{kj+p}$. Then there are $r \in \mathbb{N}$ and integers
$\alpha_1, \ldots, \alpha_r$ such that $a_p(n) = \sum_{i=1}^{r} \alpha_i a_p(n - i)$ for every
$p < k$ and every $n \ge r$.

Since $h$ has no constant term, $[x^n]\, g h^m = 0$ for $m > n$, so $a_p(n)$ is the full sum
over all $j \ge 0$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4,
Proposition 11. -/
public theorem rationalRiordan_stepSum_linearRecurrence (g₁ g₂ h₁ h₂ : ℤ[X]) (ν : ℕ)
    (hg₂ : g₂.eval 0 = 1) (hh₁ : h₁.eval 0 = 1) (hh₂ : h₂.eval 0 = 1) (hν : 1 ≤ ν)
    (k : ℕ) (hk : 0 < k) :
    let toQ : ℤ[X] → PowerSeries ℚ := fun q => ((q.map (Int.castRingHom ℚ)) : PowerSeries ℚ)
    let g : PowerSeries ℚ := toQ g₁ * (toQ g₂)⁻¹
    let h : PowerSeries ℚ := PowerSeries.X ^ ν * toQ h₁ * (toQ h₂)⁻¹
    let a : ℕ → ℕ → ℚ := fun p n =>
      ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff n (g * h ^ (k * j + p))
    ∃ (r : ℕ) (αs : ℕ → ℤ), ∀ p < k, ∀ n, r ≤ n →
      a p n = ∑ i ∈ Finset.Icc 1 r, (αs i : ℚ) * a p (n - i) := by
  intro toQ g h a
  -- `toQ` is the ring homomorphism `φ`, and the step sums have the generating functions
  -- `g hᵖ / (1 - hᵏ) = P p / Q` for the integer polynomials `Q` and `P p` below.
  let φ : ℤ[X] →+* PowerSeries ℚ :=
    coeToPowerSeries.ringHom.comp (mapRingHom (Int.castRingHom ℚ))
  have hφ (q : ℤ[X]) : toQ q = φ q := rfl
  have hφX : φ X = PowerSeries.X := by simp [φ]
  have hφn (q : ℤ[X]) (n : ℕ) : PowerSeries.coeff n (φ q) = (q.coeff n : ℚ) := by
    change PowerSeries.coeff n ((q.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) = _
    rw [coeff_coe, coeff_map, eq_intCast]
  have hφ0 (q : ℤ[X]) : PowerSeries.constantCoeff (φ q) = (q.eval 0 : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hφn, coeff_zero_eq_eval_zero]
  let Q : ℤ[X] := g₂ * (h₂ ^ k - X ^ (ν * k) * h₁ ^ k)
  let P : ℕ → ℤ[X] := fun p ↦ g₁ * X ^ (ν * p) * h₁ ^ p * h₂ ^ (k - p)
  refine ⟨Q.natDegree + ∑ p ∈ Finset.range k, (P p).natDegree + 1, fun i ↦ -Q.coeff i, ?_⟩
  intro p hp n hn
  have hν₀ : ν ≠ 0 := by omega
  have hk₀ : k ≠ 0 := by omega
  have hh : PowerSeries.constantCoeff h = 0 := by simp [h, zero_pow hν₀]
  set F := g * h ^ p * (1 - h ^ k)⁻¹ with hF
  have ha (m : ℕ) : a p m = PowerSeries.coeff m F :=
    rationalRiordan_stepSum_linearRecurrence.stepSum_coeff g h hh k p hk hp m
  have eG : φ g₂ * (φ g₂)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [hφ0, hg₂])
  have eH : φ h₂ * (φ h₂)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [hφ0, hh₂])
  have eD : (1 - h ^ k) * (1 - h ^ k)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp [hh, zero_pow hk₀])
  have hQF : φ Q * F = φ (P p) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hp.le
    have eHp : φ h₂ ^ p * (φ h₂)⁻¹ ^ p = 1 := by rw [← mul_pow, eH, one_pow]
    have eHk : φ h₂ ^ (p + m) * (φ h₂)⁻¹ ^ (p + m) = 1 := by rw [← mul_pow, eH, one_pow]
    -- `Q = g₂ h₂ᵏ (1 - hᵏ)` and `P p = g₁ h₂ᵏ hᵖ`.
    have hQ : φ Q = φ g₂ * φ h₂ ^ (p + m) * (1 - h ^ (p + m)) := by
      simp only [Q, h, hφ, hφX, map_mul, map_sub, map_pow]
      linear_combination (φ g₂ * PowerSeries.X ^ (ν * (p + m)) * φ h₁ ^ (p + m)) * eHk
    have hP : φ (P p) = φ g₁ * φ h₂ ^ (p + m) * h ^ p := by
      simp only [P, h, hφ, hφX, map_mul, map_pow, Nat.add_sub_cancel_left]
      linear_combination (-(φ g₁ * PowerSeries.X ^ (ν * p) * φ h₁ ^ p * φ h₂ ^ m)) * eHp
    rw [hQ, hP, hF]
    simp only [g, hφ]
    linear_combination
      (φ g₁ * φ h₂ ^ (p + m) * h ^ p * ((1 - h ^ (p + m)) * (1 - h ^ (p + m))⁻¹)) * eG +
        (φ g₁ * φ h₂ ^ (p + m) * h ^ p) * eD
  -- Compare the coefficients of `xⁿ` in `Q * F = P p`, where `Q(0) = 1` and `n > deg (P p)`.
  set r := Q.natDegree + ∑ p ∈ Finset.range k, (P p).natDegree + 1 with hr
  have hPdeg : (P p).natDegree < n := by
    have := Finset.single_le_sum (f := fun i ↦ (P i).natDegree) (fun i _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr hp)
    omega
  have hQ0 : Q.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]
    simp [Q, hg₂, hh₂, zero_pow (Nat.mul_ne_zero hν₀ hk₀)]
  have key : PowerSeries.coeff n (φ Q * F) = 0 := by
    rw [hQF, hφn, coeff_eq_zero_of_natDegree_lt hPdeg, Int.cast_zero]
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ PowerSeries.coeff i (φ Q) * PowerSeries.coeff j F)] at key
  have hsplit :
      ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i (φ Q) * PowerSeries.coeff (n - i) F =
        ∑ i ∈ Finset.range (r + 1), PowerSeries.coeff i (φ Q) * PowerSeries.coeff (n - i) F := by
    refine (Finset.sum_subset (fun i hi ↦ ?_) fun i _ hi ↦ ?_).symm
    · simp only [Finset.mem_range] at hi ⊢
      omega
    · simp only [Finset.mem_range, not_lt] at hi
      rw [hφn, coeff_eq_zero_of_natDegree_lt (by omega), Int.cast_zero, zero_mul]
  rw [hsplit, Finset.sum_range_eq_add_Ico _ (by omega : 0 < r + 1),
    Finset.Ico_add_one_right_eq_Icc, hφn, hQ0, Nat.sub_zero] at key
  have hsum : ∑ i ∈ Finset.Icc 1 r, ((-Q.coeff i : ℤ) : ℚ) * PowerSeries.coeff (n - i) F =
      -∑ i ∈ Finset.Icc 1 r, PowerSeries.coeff i (φ Q) * PowerSeries.coeff (n - i) F := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hφn]
    push_cast
    ring
  simp only [ha]
  rw [hsum]
  linear_combination key

end RationalRiordan

end MetaMathlibExt
