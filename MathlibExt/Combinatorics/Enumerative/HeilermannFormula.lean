/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HankelTransform
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section
open scoped BigOperators

variable {K : Type*} [CommRing K]

/-- Sum-reduction identity behind Heilermann's one-step Hankel recursion. With the
convolution law `hconv` (from `G * F 0 = 1`, `G` the reciprocal head) and the tail
coefficients `hg2`, the boundary convolution collapses to `beta 1` times a shifted
Hankel convolution of the tail sequence. -/
private theorem key_sum {K : Type*} [CommRing K] (a b g : ℕ → K) (B1 : K)
    (hg2 : ∀ s, g (s + 2) = -(B1 * b s))
    (hconv : ∀ m, ∑ k ∈ Finset.range (m + 1), g k * a (m - k) = if m = 0 then 1 else 0)
    (i' j' : ℕ) :
    ∑ q ∈ Finset.range (j' + 2), a (i' + 1 + q) * g (j' + 1 - q)
      = B1 * ∑ t ∈ Finset.range (i' + 1), a (i' - t) * b (t + j') := by
  set m0 := i' + j' + 2 with hm0
  have step1 : ∑ q ∈ Finset.range (j' + 2), a (i' + 1 + q) * g (j' + 1 - q)
      = ∑ q ∈ Finset.range (j' + 2), g q * a (m0 - q) := by
    rw [← Finset.sum_range_reflect (fun q => a (i' + 1 + q) * g (j' + 1 - q)) (j' + 2)]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_range] at hq
    have h1 : j' + 2 - 1 - q = j' + 1 - q := by omega
    rw [h1]
    have h2 : j' + 1 - (j' + 1 - q) = q := by omega
    have h3 : i' + 1 + (j' + 1 - q) = m0 - q := by omega
    rw [h2, h3, mul_comm]
  have hfull : ∑ q ∈ Finset.range (m0 + 1), g q * a (m0 - q) = 0 := by
    rw [hconv m0]; simp [hm0]
  have step2 : ∑ q ∈ Finset.range (j' + 2), g q * a (m0 - q)
      = - ∑ q ∈ Finset.Ico (j' + 2) (m0 + 1), g q * a (m0 - q) := by
    have hsplit := Finset.sum_range_add_sum_Ico (fun q => g q * a (m0 - q))
      (show j' + 2 ≤ m0 + 1 by omega)
    rw [hfull] at hsplit
    exact eq_neg_of_add_eq_zero_left hsplit
  have step3 : ∑ q ∈ Finset.Ico (j' + 2) (m0 + 1), g q * a (m0 - q)
      = ∑ t ∈ Finset.range (i' + 1), (-(B1 * b (j' + t))) * a (i' - t) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : m0 + 1 - (j' + 2) = i' + 1 := by omega
    rw [hlen]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    have e1 : j' + 2 + t = (j' + t) + 2 := by omega
    rw [e1, hg2]
    have e2 : m0 - (j' + t + 2) = i' - t := by omega
    rw [e2]
  rw [step1, step2, step3, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  rw [add_comm t j']
  ring

/-- Scaling a sequence by a constant scales its Hankel transform by that constant
to the power of the matrix size. -/
private theorem hankelTransform_const_mul {K : Type*} [CommRing K] (c : K) (f : ℕ → K) (N : ℕ) :
    hankelTransform (fun m => c * f m) N = c ^ (N + 1) * hankelTransform f N := by
  have h : (Matrix.of fun i j : Fin (N + 1) => c * f (i.val + j.val))
        = c • (Matrix.of fun i j : Fin (N + 1) => f (i.val + j.val)) := by
    ext i j; simp [Matrix.smul_apply]
  unfold hankelTransform
  rw [h, Matrix.det_smul, Fintype.card_fin]

/-- Heilermann's one-step reduction: for the coefficient sequences of the head `F 0`
and tail `F 1` of a Jacobi continued fraction, the `(n+2)`-Hankel determinant of the
head equals `beta 1 ^ (n+1)` times the `(n+1)`-Hankel determinant of the tail.
Proved via the Toeplitz column operation `U` (the reciprocal `G = 1 - C (alpha 0) X -
C (beta 1) X^2 (F 1)`), whose action zeroes the first row and exposes a scalar
`beta 1` factor and a lower-triangular Toeplitz times Hankel product. -/
private theorem reduction {K : Type*} [CommRing K] (alpha beta : ℕ → K) (F : ℕ → PowerSeries K)
    (h2 : ∀ i : ℕ,
      (1 - PowerSeries.C (alpha i) * PowerSeries.X -
        PowerSeries.C (beta (i + 1)) * PowerSeries.X ^ 2 * F (i + 1)) * F i = 1)
    (n : ℕ) :
    hankelTransform (fun m => PowerSeries.coeff m (F 0)) (n + 1)
      = beta 1 ^ (n + 1) * hankelTransform (fun m => PowerSeries.coeff m (F 1)) n := by
  set A0 := alpha 0 with hA0
  set B1 := beta 1 with hB1
  set a : ℕ → K := fun m => PowerSeries.coeff m (F 0) with ha
  set b : ℕ → K := fun m => PowerSeries.coeff m (F 1) with hb
  set G : PowerSeries K :=
    1 - PowerSeries.C A0 * PowerSeries.X - PowerSeries.C B1 * PowerSeries.X ^ 2 * F 1 with hG
  set g : ℕ → K := fun s => PowerSeries.coeff s G with hg
  have hGF : G * F 0 = 1 := h2 0
  have hgval : ∀ s : ℕ, g s = (if s = 0 then (1 : K) else 0) - A0 * (if s = 1 then 1 else 0)
      - B1 * (if 2 ≤ s then b (s - 2) else 0) := by
    intro s
    rw [hg]
    simp only [hG, map_sub]
    rw [PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
      mul_assoc (PowerSeries.C B1) (PowerSeries.X ^ 2) (F 1),
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  have hg0 : g 0 = 1 := by simp [hgval]
  have hg2 : ∀ s : ℕ, g (s + 2) = -(B1 * b s) := by intro s; simp [hgval]
  have hconv : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), g k * a (m - k) = if m = 0 then 1 else 0 := by
    intro m
    have := congrArg (PowerSeries.coeff m) hGF
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i G * PowerSeries.coeff j (F 0))] at this
    simpa [hg, ha] using this
  have hGF' : F 0 * G = 1 := by rw [mul_comm]; exact hGF
  have hconv2 : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), a k * g (m - k) = if m = 0 then 1 else 0 := by
    intro m
    have := congrArg (PowerSeries.coeff m) hGF'
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (F 0) * PowerSeries.coeff j G)] at this
    simpa [hg, ha] using this
  have a0 : a 0 = 1 := by
    have := hconv 0
    simpa [hg0] using this
  -- matrices
  set A : Matrix (Fin (n + 2)) (Fin (n + 2)) K :=
    Matrix.of (fun i j => a (i.val + j.val)) with hAdef
  set U : Matrix (Fin (n + 2)) (Fin (n + 2)) K :=
    Matrix.of (fun p j => if p.val ≤ j.val then g (j.val - p.val) else 0) with hUdef
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    Matrix.of (fun i j => b (i.val + j.val)) with hBdef
  set L : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    Matrix.of (fun i t => if t.val ≤ i.val then a (i.val - t.val) else 0) with hLdef
  have hAUentry : ∀ (i j : Fin (n + 2)),
      (A * U) i j = ∑ q ∈ Finset.range (j.val + 1), a (i.val + q) * g (j.val - q) := by
    intro i j
    rw [Matrix.mul_apply]
    simp only [hAdef, hUdef, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range
      (fun p => a (i.val + p) * (if p ≤ j.val then g (j.val - p) else 0)) (n + 2)]
    have hsub : Finset.range (j.val + 1) ⊆ Finset.range (n + 2) := by
      intro x hx; simp only [Finset.mem_range] at *; have := j.isLt; omega
    have hz : ∀ q ∈ Finset.range (n + 2), q ∉ Finset.range (j.val + 1) →
        a (i.val + q) * (if q ≤ j.val then g (j.val - q) else 0) = 0 := by
      intro q _ hq'
      rw [Finset.mem_range] at hq'
      split_ifs with h
      · exact absurd h (by omega)
      · rw [mul_zero]
    rw [← Finset.sum_subset hsub hz]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_range] at hq
    split_ifs with h
    · rfl
    · exact absurd (show q ≤ j.val by omega) h
  have hLBentry : ∀ (i j : Fin (n + 1)),
      (L * B) i j = ∑ t ∈ Finset.range (i.val + 1), a (i.val - t) * b (t + j.val) := by
    intro i j
    rw [Matrix.mul_apply]
    simp only [hLdef, hBdef, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range
      (fun t => (if t ≤ i.val then a (i.val - t) else 0) * b (t + j.val)) (n + 1)]
    have hsub : Finset.range (i.val + 1) ⊆ Finset.range (n + 1) := by
      intro x hx; simp only [Finset.mem_range] at *; have := i.isLt; omega
    have hz : ∀ t ∈ Finset.range (n + 1), t ∉ Finset.range (i.val + 1) →
        (if t ≤ i.val then a (i.val - t) else 0) * b (t + j.val) = 0 := by
      intro t _ ht'
      rw [Finset.mem_range] at ht'
      split_ifs with h
      · exact absurd h (by omega)
      · rw [zero_mul]
    rw [← Finset.sum_subset hsub hz]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    split_ifs with h
    · rfl
    · exact absurd (show t ≤ i.val by omega) h
  have detU : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · have hd : ∀ i : Fin (n + 2), U i i = 1 := by
        intro i; simp [hUdef, hg0]
      simp [hd]
    · intro i j hji
      have hlt : (j : ℕ) < (i : ℕ) := hji
      simp only [hUdef, Matrix.of_apply]
      split_ifs with h
      · exact absurd h (by omega)
      · rfl
  have detL : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · have hd : ∀ i : Fin (n + 1), L i i = 1 := by
        intro i; simp [hLdef, a0]
      simp [hd]
    · intro i j hij
      have hlt : (i : ℕ) < (j : ℕ) := hij
      simp only [hLdef, Matrix.of_apply]
      split_ifs with h
      · exact absurd h (by omega)
      · rfl
  -- reduce the goal to a determinant identity
  have hHa : hankelTransform a (n + 1) = A.det := rfl
  have hHb : hankelTransform b n = B.det := rfl
  rw [hHa, hHb]
  have hdetAU : (A * U).det = A.det := by rw [Matrix.det_mul, detU, mul_one]
  rw [← hdetAU, Matrix.det_succ_row_zero]
  have hrow0 : ∀ j : Fin (n + 2), (A * U) 0 j = if j.val = 0 then 1 else 0 := by
    intro j
    rw [hAUentry]
    simp only [Fin.val_zero, Nat.zero_add]
    exact hconv2 j.val
  rw [Fintype.sum_eq_single (0 : Fin (n + 2))]
  · have e0 : (A * U) 0 0 = 1 := by rw [hrow0]; simp
    rw [e0, Fin.succAbove_zero]
    simp only [Fin.val_zero, pow_zero, one_mul]
    have hM : (A * U).submatrix Fin.succ Fin.succ = B1 • (L * B) := by
      ext i' j'
      rw [Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, hLBentry, hAUentry]
      simp only [Fin.val_succ]
      exact key_sum a b g B1 hg2 hconv i'.val j'.val
    rw [hM, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, detL, one_mul]
  · intro j hj
    rw [hrow0]
    split_ifs with h
    · exact absurd (Fin.val_eq_zero_iff.mp h) hj
    · ring

/-- **Heilermann's formula.** Let $K$ be a commutative ring, let $a$, $\alpha$, $\beta$ be
sequences in $K$ and let $\mu_0 \in K$. Suppose that $a$ has Jacobi fraction data
$(\alpha, \beta, \mu_0)$: there are power series $F_0, F_1, \dots$ over $K$ with
$\sum_{n \ge 0} a_n x^n = \mu_0 F_0$ and $(1 - \alpha_i x - \beta_{i+1} x^2 F_{i+1}) F_i = 1$ for
every $i \ge 0$. Then for every $n \ge 0$ the Hankel transform of $a$ at $n$, the determinant of
the $(n+1) \times (n+1)$ matrix $(a_{i+j})_{0 \le i, j \le n}$, equals
$$\mu_0^{n+1} \prod_{j=0}^{n-1} \beta_{j+1}^{\,n-j},$$
that is, $\mu_0^{n+1} \beta_1^n \beta_2^{n-1} \cdots \beta_n$, which is $\mu_0$ for $n = 0$.

Source: Paul Barry, "From Fibonacci to Robbins: Series Reversion and Hankel
Transforms," Journal of Integer Sequences 24 (2021), Article 21.10.2,
`https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex`, lines 110-117.
Normalized source-text SHA-256 (no terminal newline)
`a838e5996f223ba9e45347f17ad864912efc392f5c3d56ea749bcf62d3289825`; raw
line-span SHA-256 (with terminal newline)
`11385eb5eee1af1081307348d4029cdc74b51d84e8bff2fbe9831891145d998e`.
Concept `jis_dep_heilermann_049f63eb`; grounded `jis_grounded_049f63eb8aadf7377777a597`.
Zero-indexed: `hankelTransform a n` is the determinant of the `(n + 1) x (n + 1)`
Hankel matrix, and the product over `Finset.range n` with shift `beta (j + 1)`
and exponent `n - j` gives `beta_1 ^ n, ..., beta_n ^ 1`; for `n = 0` the empty
product yields `mu0`. Scope: only the determinant identity is stated; the Jacobi
continued fraction data itself is carried by `HasJacobiFraction`.

Proves `Wanted` entry `hankelTransform_eq_prod_of_hasJacobiFraction`.
-/
theorem hankelTransform_eq_prod_of_hasJacobiFraction
    {a alpha beta : ℕ → K} {mu0 : K} {F : ℕ → PowerSeries K}
    (h : HasJacobiFraction a alpha beta mu0 F) (n : ℕ) :
    hankelTransform a n =
      mu0 ^ (n + 1) * ∏ j ∈ Finset.range n, beta (j + 1) ^ (n - j) := by
  induction n generalizing a alpha beta mu0 F with
  | zero =>
    obtain ⟨h1, h2⟩ := h
    have hF0 : PowerSeries.coeff 0 (F 0) = 1 := by
      have := congrArg (PowerSeries.coeff 0) (h2 0)
      simpa [map_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_sub, map_one] using this
    have ha0 : a 0 = mu0 := by
      have := congrArg (PowerSeries.coeff 0) h1
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, hF0, mul_one] at this
      exact this
    simp [hankelTransform, ha0]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := h
    have ha : a = fun m => mu0 * PowerSeries.coeff m (F 0) := by
      funext m
      have := congrArg (PowerSeries.coeff m) h1
      rwa [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul] at this
    have hshift : HasJacobiFraction (fun m => PowerSeries.coeff m (F 1))
        (fun i => alpha (i + 1)) (fun i => beta (i + 1)) 1 (fun i => F (i + 1)) := by
      refine ⟨?_, ?_⟩
      · rw [map_one, one_mul]; ext m; rw [PowerSeries.coeff_mk]
      · intro i; simpa using h2 (i + 1)
    have IHb := ih hshift
    rw [ha, hankelTransform_const_mul, reduction alpha beta F h2 n, IHb]
    rw [one_pow, one_mul]
    congr 1
    rw [Finset.prod_range_succ', mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.succ_sub_succ]

/-- **Hankel transforms of Jacobi fractions do not depend on the linear coefficients.** Let $K$
be a commutative ring. Say that a sequence $a$ in $K$ has Jacobi fraction data
$(\alpha, \beta, \mu_0)$, where $\alpha$, $\beta$ are sequences in $K$ and $\mu_0 \in K$, when there
are power series $F_0, F_1, \dots$ over $K$ with $\sum_{n \ge 0} a_n x^n = \mu_0 F_0$ and
$(1 - \alpha_i x - \beta_{i+1} x^2 F_{i+1}) F_i = 1$ for every $i \ge 0$. If $a$ has Jacobi fraction
data $(\alpha, \beta, \mu_0)$ and $a'$ has Jacobi fraction data $(\alpha', \beta, \mu_0)$, with the
same $\beta$ and $\mu_0$ but arbitrary $\alpha$ and $\alpha'$, then $a$ and $a'$ have the same
Hankel transform: for every $n \ge 0$ the determinants of the $(n+1) \times (n+1)$ matrices
$(a_{i+j})_{0 \le i, j \le n}$ and $(a'_{i+j})_{0 \le i, j \le n}$ are equal.

Source: Paul Barry, "From Fibonacci to Robbins: Series Reversion and Hankel
Transforms," Journal of Integer Sequences 24 (2021), Article 21.10.2,
`https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex`, lines 110-117.
Concept `jis_dep_heilermann_049f63eb`; grounded `jis_grounded_049f63eb8aadf7377777a597`.
Stated over a commutative ring; the source-faithful Wanted entry was stated over a field.

Proves `Wanted` entry `hankelTransform_eq_of_hasJacobiFraction_same_beta`.
-/
theorem hankelTransform_eq_of_hasJacobiFraction_same_beta
    (a a2 alpha alpha2 beta : ℕ → K) (mu0 : K)
    (F F2 : ℕ → PowerSeries K)
    (h1 : HasJacobiFraction a alpha beta mu0 F)
    (h2 : HasJacobiFraction a2 alpha2 beta mu0 F2) :
    hankelTransform a = hankelTransform a2 := by
  funext n
  rw [hankelTransform_eq_prod_of_hasJacobiFraction h1,
    hankelTransform_eq_prod_of_hasJacobiFraction h2]

end

end MetaMathlibExt
