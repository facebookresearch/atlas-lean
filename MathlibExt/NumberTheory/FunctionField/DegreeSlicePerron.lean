/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Perron's formula for degree slices of monic polynomials

For a finite field `F`, `fixedDegreeMonic F n` is the finite set `M_n` of monic polynomials of
degree `n` over `F`. For `a : F[X] → ℂ` write `c_m = ∑_{f ∈ M_m} a f`. If `0 < r < 1`, the series
`∑ |c_m| r^m` converges and `A u = ∑ c_m u^m` on the circle `|u| = r`, then
`perron_formula_polynomial_degree_slice` recovers each coefficient as a contour integral:
`c_n = (2πi)⁻¹ ∮_{|u| = r} A(u) / u^{n+1} du`.

The proof integrates the series term by term on the circle (dominated convergence, with the
constant bounds `|c_m| r^{m-n}`) and uses `∮ u^k du = 0` for every integer `k ≠ -1` and
`∮ u⁻¹ du = 2πi`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free
and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Theorem 9.
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/--
**Monic polynomials of fixed degree.** For a finite field $F$ and a natural number $n$, $M_n$ is
the finite set of monic polynomials of degree $n$ over $F$: the polynomials
$X^n + c_{n-1} X^{n-1} + \dots + c_1 X + c_0$ with $c_0, \dots, c_{n-1} \in F$.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public noncomputable def fixedDegreeMonic (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) :
    Finset (Polynomial F) :=
  Finset.univ.image fun c : Fin n → F =>
    X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

/--
**Membership in $M_n$.** Let $F$ be a finite field and $n \in \mathbb{N}$. A polynomial $f$ over
$F$ lies in the set $M_n$ of monic polynomials of degree $n$ over $F$ if and only if there are
$c_0, \dots, c_{n-1} \in F$ with $f = X^n + \sum_{i=0}^{n-1} c_i X^i$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem mem_fixedDegreeMonic_iff (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (f : Polynomial F) :
    f ∈ fixedDegreeMonic F n ↔
      ∃ c : Fin n → F, X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ) = f := by
  simp [fixedDegreeMonic]

/--
**The only monic polynomial of degree zero.** For every finite field $F$, the set $M_0$ of monic
polynomials of degree $0$ over $F$ is $\{1\}$.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem fixedDegreeMonic_zero (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    fixedDegreeMonic F 0 = {1} := by
  ext f
  simp [fixedDegreeMonic]

end

namespace PerronFormulaPolynomialDegreeSlice

open Complex MeasureTheory

/-- For `0 < r`, the contour integral of the single term `c u^m / u^(n+1)` over `|u| = r` is
`2πi c` when `m = n` and `0` otherwise. -/
private theorem circleIntegral_monomial_div_pow {r : ℝ} (hr : 0 < r) (c : ℂ) (m n : ℕ) :
    (∮ u in C(0, r), c * u ^ m / u ^ (n + 1)) =
      if m = n then c * (2 * Real.pi * I) else 0 := by
  have hcongr : (∮ u in C(0, r), c * u ^ m / u ^ (n + 1)) =
      ∮ u in C(0, r), c * (u - 0) ^ ((m : ℤ) - (n + 1)) := by
    refine circleIntegral.integral_congr hr.le fun u hu => ?_
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp only [mem_sphere_iff_norm, sub_zero, norm_zero] at hu
      exact hr.ne hu
    simp only [sub_zero]
    rw [zpow_sub₀ hu0, zpow_natCast, mul_div_assoc]
    norm_cast
  rw [hcongr, circleIntegral.integral_const_mul]
  split_ifs with h
  · subst h
    have : ((m : ℤ) - (m + 1)) = -1 := by ring
    rw [this]
    simp_rw [zpow_neg_one]
    rw [circleIntegral.integral_sub_center_inv 0 hr.ne']
  · have : ((m : ℤ) - (n + 1)) ≠ -1 := by omega
    rw [circleIntegral.integral_sub_zpow_of_ne this, mul_zero]

end PerronFormulaPolynomialDegreeSlice

-- The bound `r < 1` is part of the paper's setting but the contour formula holds for every
-- radius `r > 0`, so the proof does not use `hr₁`.
set_option linter.unusedVariables false in
open Complex MeasureTheory PerronFormulaPolynomialDegreeSlice in
/--
**Perron's formula for degree slices of monic polynomials.** Let $F$ be a finite field,
let $M_m$ be the set of monic polynomials of degree $m$ over $F$, let
$a \colon F[X] \to \mathbb{C}$, and write $c_m = \sum_{f \in M_m} a(f)$. Let $r$ be a real
number with $0 < r < 1$ such that the series $\sum_{m \ge 0} |c_m| r^m$ converges, and let
$A \colon \mathbb{C} \to \mathbb{C}$ satisfy $A(u) = \sum_{m \ge 0} c_m u^m$ for every
complex $u$ with $|u| = r$. Then for every $n \ge 0$,
$$c_n = \frac{1}{2\pi i} \oint_{|u| = r} \frac{A(u)}{u^{n+1}}\, du,$$
where the circle $|u| = r$ is traversed once counterclockwise.

Convergence of $\sum |c_m| r^m$ at the single radius $r$ stands in for the paper's uniform
absolute convergence on the closed disk, and $A$ only has to agree with the series on the
circle, the only values the contour integral sees.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 9.
-/
public theorem perron_formula_polynomial_degree_slice
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (a : Polynomial F → ℂ) (A : ℂ → ℂ) (r : ℝ)
    (hr₀ : 0 < r) (hr₁ : r < 1)
    (hsum : Summable fun n : ℕ =>
      ‖∑ f ∈ fixedDegreeMonic F n, a f‖ * r ^ n)
    (hA : ∀ u : ℂ, ‖u‖ = r → A u = ∑' m : ℕ,
      (∑ f ∈ fixedDegreeMonic F m, a f) * u ^ m)
    (n : ℕ) :
    (∑ f ∈ fixedDegreeMonic F n, a f) =
      (1 / (2 * Real.pi * Complex.I)) *
        ∮ u in C(0, r), A u / u ^ (n + 1) := by
  set c : ℕ → ℂ := fun m => ∑ f ∈ fixedDegreeMonic F m, a f
  -- Term-by-term integration on the circle.
  have hHas : HasSum (fun m : ℕ => ∮ u in C(0, r), c m * u ^ m / u ^ (n + 1))
      (∮ u in C(0, r), A u / u ^ (n + 1)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => r * (‖c m‖ * r ^ m / r ^ (n + 1))) (fun m => ?_) (fun m => ?_) ?_ ?_ ?_
    · apply Continuous.aestronglyMeasurable
      simp only [deriv_circleMap]
      exact (by fun_prop : Continuous fun θ => circleMap 0 r θ * I).smul
        (Continuous.div (by fun_prop) (by fun_prop)
          fun θ => pow_ne_zero _ (circleMap_ne_center hr₀.ne'))
    · refine Filter.Eventually.of_forall fun θ _ => ?_
      simp [abs_of_pos hr₀]
    · exact Filter.Eventually.of_forall fun _ _ =>
        ((hsum.div_const (r ^ (n + 1))).mul_left r)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun θ _ => ?_
      have hnorm : ‖circleMap 0 r θ‖ = r := by simp [abs_of_pos hr₀]
      have hs : Summable fun m => c m * circleMap 0 r θ ^ m := by
        refine Summable.of_norm ?_
        simpa [norm_mul, norm_pow, hnorm] using hsum
      dsimp only
      rw [hA _ hnorm]
      simp only [smul_eq_mul]
      exact (hs.hasSum.div_const _).mul_left _
  have hterm : (fun m : ℕ => ∮ u in C(0, r), c m * u ^ m / u ^ (n + 1)) =
      fun m => if m = n then c n * (2 * Real.pi * I) else 0 := by
    funext m
    rw [circleIntegral_monomial_div_pow hr₀]
    split_ifs with h
    · rw [h]
    · rfl
  rw [hterm] at hHas
  have := (hasSum_ite_eq n (c n * (2 * Real.pi * I))).unique hHas
  rw [← this]
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [one_div, inv_mul_eq_div, mul_div_cancel_right₀ _ h2]

end MetaMathlibExt
