/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Unified Catalan-type polynomials

Statements from M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105.

Every family in the paper is defined by a generating function of the shape
`numerator(t) / (c - α t + β t^m)^λ` with a real exponent `λ`. The denominator factor
`(c - α t + β t^m)^(-λ)` is `trinomialNegPowSeries λ c α β m`, built from Mathlib's binomial
series; the paper's polynomials are coefficients of products of power series in `t`, with
all variables `x, y, z` fixed real numbers. The paper's `P^λ_{r,m}(z)` and `h^λ_{r,m}(z)`
in Theorems 2 and 3 are read as the coefficients of `(1 - m t + z t^m)^(-λ)` and
`(1 - m z t + t^m)^(-λ)` (Definition 5 with `A = 0`), as in the proof of Theorem 2.
The paper's Hermite polynomials `H_n(x)` have the generating function `e^(2xt - t²)`
(Section 1), and `H_n(x, y)` are the Kampé de Fériet polynomials `H^2_n(x, y)` of
Equation (2).
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- The formal expansion of `(c - α t + β t^m)^(-λ)` in powers of `t`, written as
`c^(-λ) (1 + u)^(-λ)` with `u = (-α t + β t^m) / c` and Mathlib's binomial series. For
`c > 0` and `m ≥ 1` this is the denominator factor of every generating function in the
paper (with `c = 1`, `α = m`, `β = x` in Section 2).

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equations (6), (12)
and (15). -/
noncomputable def trinomialNegPowSeries (lam c α β : ℝ) (m : ℕ) : PowerSeries ℝ :=
  C (c ^ (-lam)) *
    (binomialSeries ℝ (-lam)).subst (C (-α / c) * X + C (β / c) * X ^ m : PowerSeries ℝ)

/-- The constant term of `(c - α t + β t^m)^(-λ)` is `c^(-λ)`.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (6). -/
theorem constantCoeff_trinomialNegPowSeries (lam c α β : ℝ) {m : ℕ} (hm : m ≠ 0) :
    constantCoeff (trinomialNegPowSeries lam c α β m) = c ^ (-lam) := by
  set u : PowerSeries ℝ := C (-α / c) * X + C (β / c) * X ^ m with hu_def
  have hu0 : constantCoeff u = 0 := by simp [u, hm]
  have hu : HasSubst u := HasSubst.of_constantCoeff_zero' hu0
  have hone : subst u (1 : PowerSeries ℝ) = 1 := by
    rw [← coe_substAlgHom hu, map_one]
  set b := binomialSeries ℝ (-lam) with hb_def
  have hb0 : constantCoeff (b - 1) = 0 := by simp [b]
  have hsub0 : constantCoeff ((b - 1).subst u) = 0 :=
    constantCoeff_subst_eq_zero hu0 (b - 1) hb0
  have hb : b = 1 + (b - 1) := by ring
  unfold trinomialNegPowSeries
  rw [← hu_def, ← hb_def, map_mul, hb, subst_add hu, map_add, hone, hsub0]
  simp

/-- For `λ = -1` and `c = 1` the series is the trinomial `1 - α t + β t^m` itself.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (6). -/
theorem trinomialNegPowSeries_neg_one (α β : ℝ) {m : ℕ} (hm : m ≠ 0) :
    trinomialNegPowSeries (-1) 1 α β m = 1 - C α * X + C β * X ^ m := by
  set u : PowerSeries ℝ := C (-α / 1) * X + C (β / 1) * X ^ m with hu_def
  have hu0 : constantCoeff u = 0 := by simp [u, hm]
  have hu : HasSubst u := HasSubst.of_constantCoeff_zero' hu0
  have hone : subst u (1 : PowerSeries ℝ) = 1 := by
    rw [← coe_substAlgHom hu, map_one]
  have h1 : (-(-1 : ℝ)) = ((1 : ℕ) : ℝ) := by norm_num
  unfold trinomialNegPowSeries
  rw [← hu_def, h1, binomialSeries_nat, pow_one, subst_add hu, subst_X hu, hone]
  simp [u, map_neg]
  ring

/-- The Kampé de Fériet (two-variable Hermite) polynomial
`H^m_n(x, y) = n! ∑_{r ≤ ⌊n/m⌋} y^r x^(n - m r) / (r! (n - m r)!)`, evaluated in any real
algebra (so that `H_k(x + 2 y t, y)` can be formed in `ℝ⟦t⟧`); `H^2_n = H_n`.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (2). -/
noncomputable def kampeDeFerietHermite {A : Type*} [CommRing A] [Algebra ℝ A] (m n : ℕ)
    (x y : A) : A :=
  ∑ r ∈ Finset.range (n / m + 1),
    ((n.factorial : ℝ) / ((r.factorial : ℝ) * ((n - m * r).factorial : ℝ))) •
      (y ^ r * x ^ (n - m * r))

/-- `H^m_0(x, y) = 1`.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (2). -/
theorem kampeDeFerietHermite_zero {A : Type*} [CommRing A] [Algebra ℝ A] (m : ℕ) (x y : A) :
    kampeDeFerietHermite m 0 x y = 1 := by
  simp [kampeDeFerietHermite]

/-- `H_2(x, y) = x² + 2 y`.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (2). -/
theorem kampeDeFerietHermite_two_two (x y : ℝ) :
    kampeDeFerietHermite 2 2 x y = x ^ 2 + 2 * y := by
  simp [kampeDeFerietHermite, Finset.sum_range_succ, Nat.factorial]

/-- **Theorem 2.** The polynomials `H^{k;λ}_{n,m}(x, y, z)` and `h^{k;λ}_{n,m}(x, y, z)`,
the coefficients of `t^n` in `e^(xt + yt²) H_k(x + 2yt, y) / (1 - m t + z t^m)^λ` and
`e^(xt + yt²) H_k(x + 2yt, y) / (1 - m z t + t^m)^λ` (Definition 3), are
`∑_{r=0}^n H_{n-r+k}(x, y) P^λ_{r,m}(z) / (n - r)!` and
`∑_{r=0}^n H_{n-r+k}(x, y) h^λ_{r,m}(z) / (n - r)!` (Equations (8) and (9)), where
`P^λ_{r,m}(z)` and `h^λ_{r,m}(z)` are the coefficients of `t^r` in the two denominator
factors. Stated for all `m` and real `λ`.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 2
(`integers-2026-A105-thm-2`). -/
public theorem_wanted coeff_hermiteShift_mul_trinomialNegPowSeries (k m n : ℕ)
    (lam x y z : ℝ) :
    let G : PowerSeries ℝ := ((exp ℝ).subst (C x * X + C y * X ^ 2 : PowerSeries ℝ) :
        PowerSeries ℝ) * kampeDeFerietHermite 2 k (C x + C (2 * y) * X) (C y)
    coeff n (G * trinomialNegPowSeries lam 1 m z m) =
        ∑ r ∈ Finset.range (n + 1), kampeDeFerietHermite 2 (n - r + k) x y /
          ((n - r).factorial : ℝ) * coeff r (trinomialNegPowSeries lam 1 m z m) ∧
      coeff n (G * trinomialNegPowSeries lam 1 (m * z) 1 m) =
        ∑ r ∈ Finset.range (n + 1), kampeDeFerietHermite 2 (n - r + k) x y /
          ((n - r).factorial : ℝ) * coeff r (trinomialNegPowSeries lam 1 (m * z) 1 m)

/-- **Theorem 3.** With `F(j, k, y, t) = ∑_n t^(jn+k) H_{jn+k}(y) / (jn + k)!` (Equation (1),
`H_n` the Hermite polynomials of `e^(2yt - t²)`, so `H_n(y) / n!` is the coefficient of
`t^n` in that exponential), the coefficients `F^{j.k;λ}_{r,m}(x, y)` and `f^{j.k;λ}_{r,m}(x, y)`
of `t^r` in `F(j, k, y, t) / (1 - m t + x t^m)^λ` and `F(j, k, y, t) / (1 - m x t + t^m)^λ`
(Equations (10) and (11)) are
`∑_{n ≤ ⌊(r-k)/j⌋} H_{jn+k}(y) P^λ_{r-jn-k,m}(x) / (jn + k)!` and the same sum with
`h^λ_{r-jn-k,m}(x)`. Stated for `k ≤ r` (for `r < k` the paper's sum is empty and both
sides vanish), all `j, m` (the paper takes `j, m ≥ 1`) and real `λ`.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 3
(`integers-2026-A105-thm-3`). -/
public theorem_wanted coeff_nietoHermiteSeries_mul_trinomialNegPowSeries (j k m r : ℕ)
    (lam x y : ℝ) (hkr : k ≤ r) :
    let E : PowerSeries ℝ :=
      ((exp ℝ).subst (C (2 * y) * X - X ^ 2 : PowerSeries ℝ) : PowerSeries ℝ)
    let F : PowerSeries ℝ := PowerSeries.mk fun n ↦ if k ≤ n ∧ j ∣ n - k then coeff n E else 0
    coeff r (F * trinomialNegPowSeries lam 1 m x m) =
        ∑ n ∈ Finset.range ((r - k) / j + 1),
          coeff (j * n + k) E * coeff (r - j * n - k) (trinomialNegPowSeries lam 1 m x m) ∧
      coeff r (F * trinomialNegPowSeries lam 1 (m * x) 1 m) =
        ∑ n ∈ Finset.range ((r - k) / j + 1),
          coeff (j * n + k) E * coeff (r - j * n - k) (trinomialNegPowSeries lam 1 (m * x) 1 m)

/-- **Theorem 6.** For the kernel `R(x, t) = [c - a x t + b t^m (2x - 1)^d]^λ`, the
coefficients `P^{j.k;a,b,c,d,λ,A}_{n,m}(x, y)` of `(S(j, k, yt) + A(x) t) / R(x, t)`
(Equation (15), `S` the pseudo-Bessel function of Equation (5)) satisfy
`P^{j.k;…,λ,A}_{n,m}(x, y) = P^{j.k;…,λ,0}_{n,m}(x, y) + P^{1.0;…,λ,A}_{n,m}(x) -
P^{1.0;…,λ,0}_{n,m}(x)`, where the last two are the `y = 0` specializations with numerators
`1 + A(x) t` and `1`. Stated for `d ∈ ℕ`, `A ∈ ℤ[x]`, all real `a, b, c, λ`; the kernel is the
paper's for `c > 0`.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 6
(`integers-2026-A105-thm-6`). -/
public theorem_wanted coeff_catalanTypeKernel_decomposition (j k m d n : ℕ)
    (a b c lam x y : ℝ) (A : Polynomial ℤ) :
    let K : PowerSeries ℝ := trinomialNegPowSeries lam c (a * x) (b * (2 * x - 1) ^ d) m
    let S : PowerSeries ℝ :=
      PowerSeries.mk fun i ↦ if k ≤ i ∧ j ∣ i - k then y ^ i / (i.factorial : ℝ) else 0
    let At : PowerSeries ℝ := C (Polynomial.aeval x A) * X
    coeff n ((S + At) * K) = coeff n (S * K) + coeff n ((1 + At) * K) - coeff n K

/-- **Theorem 7.** The lower-triangular matrix `P_N^{(m,λ,A)}(x)` with `(i, j)` entry
`P^{λ,A}_{i-j,m}(x)` for `i ≥ j` and `0` otherwise (Equation (18)), where `P^{λ,A}_{n,m}(x)`
is the coefficient of `t^n` in `(1 + A(x) t) / (1 - m t + x t^m)^λ` (Definition 6 at
`y = 0`), has determinant `(P^{λ,A}_{0,m}(x))^(N+1)`. The paper's proviso
`P^{λ,A}_{0,m}(x) ≠ 0` is not needed and is dropped.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 7
(`integers-2026-A105-thm-7`). -/
public theorem_wanted det_catalanTypeLowerTriangular (m N : ℕ) (lam x : ℝ)
    (A : Polynomial ℤ) :
    let P : ℕ → ℝ := fun n ↦
      coeff n ((1 + C (Polynomial.aeval x A) * X) * trinomialNegPowSeries lam 1 m x m)
    (Matrix.of fun i j : Fin (N + 1) ↦ if j ≤ i then P (i - j) else 0).det = P 0 ^ (N + 1)

/-- **Theorem 8.** If the sequence `P^{λ,A}_{n,m}(x)` of Theorem 7 satisfies a linear
recurrence `∑_{k=0}^r c_k P^{λ,A}_{n-k,m}(x) = 0` for all `n ≥ r` with constants `c_k` not all
zero (Equation (22)) and `r ≤ N`, then the Hankel matrix `H_N^{(m,λ,A)}(x)` with `(i, j)`
entry `P^{λ,A}_{i+j,m}(x)` (Equation (20)) is singular. The paper's `1 ≤ r` is dropped
(`r = 0` is vacuous since `P^{λ,A}_{0,m}(x) = 1`), and with it the explicit `N ≥ 1`.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 8
(`integers-2026-A105-thm-8`). -/
public theorem_wanted det_catalanTypeHankel_eq_zero (m N r : ℕ) (lam x : ℝ)
    (A : Polynomial ℤ) (cs : ℕ → ℝ) :
    let P : ℕ → ℝ := fun n ↦
      coeff n ((1 + C (Polynomial.aeval x A) * X) * trinomialNegPowSeries lam 1 m x m)
    r ≤ N → (∃ k ≤ r, cs k ≠ 0) →
      (∀ n, r ≤ n → ∑ k ∈ Finset.range (r + 1), cs k * P (n - k) = 0) →
      (Matrix.of fun i j : Fin (N + 1) ↦ P (i + j)).det = 0

end

end MetaMathlibExt
