/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.Algebra.Polynomial.BesselPolynomial
import Mathlib.Algebra.Group.PowIterate
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Expansion of `(XV)^n` with Bessel numbers

Statement from Abdelhay Benmoussa, *On the Expansion of `(XV)^n` and Bessel Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.5. `X` is multiplication by `x` and `V` is
the Volterra operator `V f x = ∫_0^x f t dt`; the Bessel numbers are
`a(n, k) = [x^k] y_n(x)`, the coefficients of `MetaMathlibExt.besselPolynomial`.

The main result, `MetaMathlibExt.xMul_volterra_iterate_eq_sum_bessel`, states that for every
`n ≥ 1`, every continuous `f : ℝ → ℝ` and every real `x`,
`(XV)^n f(x) = ∑_{k=0}^{n-1} (-1)^k a(n-1, k) x^{n-k} (V^{n+k} f)(x)`.

The proof works in the ring of linear endomorphisms of `C(ℝ, ℝ)`. The fundamental theorem of
calculus gives the commutation relation `V X = X V - V²`, hence `V^j X = X V^j - j V^{j+1}`.
Induction on `n`, using the recurrence `a(m+1, j+1) = a(m, j+1) + (m+j+1) a(m, j)` of the Bessel
numbers, then gives the expansion of `(XV)^n` in any real algebra with this commutation relation.
-/

namespace MetaMathlibExt

@[expose] public section

namespace VolterraBesselExpansion

/-- The coefficients of the Bessel polynomial: `a(m, k) = (m+k)! / (2^k k! (m-k)!)` for `k ≤ m`,
and `0` for `k > m`. -/
private theorem coeff_besselPolynomial (m k : ℕ) :
    (besselPolynomial m).coeff k =
      if k ≤ m then (Nat.factorial (m + k) : ℚ) /
        ((2 ^ k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (m - k) : ℚ)) else 0 := by
  simp [besselPolynomial]

private theorem coeff_besselPolynomial_of_le {m k : ℕ} (h : k ≤ m) :
    (besselPolynomial m).coeff k = (Nat.factorial (m + k) : ℚ) /
        ((2 ^ k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (m - k) : ℚ)) := by
  rw [coeff_besselPolynomial, ite_eq_left h]

private theorem coeff_besselPolynomial_of_lt {m k : ℕ} (h : m < k) :
    (besselPolynomial m).coeff k = 0 := by
  rw [coeff_besselPolynomial, ite_eq_right (Nat.not_le.mpr h)]

private theorem coeff_besselPolynomial_zero_right (m : ℕ) :
    (besselPolynomial m).coeff 0 = 1 := by
  rw [coeff_besselPolynomial_of_le (Nat.zero_le m)]
  simp [Nat.factorial_ne_zero]

/-- The recurrence `a(m+1, j+1) = a(m, j+1) + (m + j + 1) a(m, j)` of the Bessel numbers. -/
private theorem coeff_besselPolynomial_succ_succ (m j : ℕ) :
    (besselPolynomial (m + 1)).coeff (j + 1) =
      (besselPolynomial m).coeff (j + 1) +
        ((m + j + 1 : ℕ) : ℚ) * (besselPolynomial m).coeff j := by
  rcases lt_trichotomy j m with hjm | rfl | hjm
  · obtain ⟨d, rfl⟩ : ∃ d, m = j + 1 + d := ⟨m - (j + 1), by omega⟩
    rw [coeff_besselPolynomial_of_le (by omega), coeff_besselPolynomial_of_le (by omega),
      coeff_besselPolynomial_of_le (by omega),
      show j + 1 + d + 1 + (j + 1) = j + 1 + d + j + 1 + 1 by omega,
      show j + 1 + d + 1 - (j + 1) = d + 1 by omega,
      show j + 1 + d + (j + 1) = j + 1 + d + j + 1 by omega,
      show j + 1 + d - (j + 1) = d by omega, show j + 1 + d - j = d + 1 by omega]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · rw [coeff_besselPolynomial_of_lt (Nat.lt_add_one j), coeff_besselPolynomial_of_le le_rfl,
      coeff_besselPolynomial_of_le le_rfl, show j + 1 + (j + 1) = j + j + 1 + 1 by omega,
      Nat.sub_self, Nat.sub_self]
    simp only [Nat.factorial_succ, Nat.factorial_zero]
    push_cast
    field_simp
    ring
  · rw [coeff_besselPolynomial_of_lt (by omega), coeff_besselPolynomial_of_lt (by omega),
      coeff_besselPolynomial_of_lt hjm, mul_zero, add_zero]

/-- From `V X = X V - V²` one gets `V^j X = X V^j - j V^{j+1}`. -/
private theorem pow_mul_eq {R : Type*} [Ring R] [Algebra ℝ R] {X V : R}
    (h : V * X = X * V - V * V) (j : ℕ) :
    V ^ j * X = X * V ^ j - (j : ℝ) • V ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc V ^ (j + 1) * X = V ^ j * X * V - V ^ j * (V * V) := by
          rw [pow_succ, mul_assoc, h, mul_sub, mul_assoc]
      _ = (X * V ^ j - (j : ℝ) • V ^ (j + 1)) * V - V ^ j * (V * V) := by rw [ih]
      _ = X * V ^ (j + 1) - ((j + 1 : ℕ) : ℝ) • V ^ (j + 1 + 1) := by
        simp only [pow_succ, sub_mul, smul_mul_assoc, mul_assoc, Nat.cast_succ, add_smul,
          one_smul]
        abel

/-- The expansion `(XV)^{m+1} = ∑_{k ≤ m} (-1)^k a(m, k) X^{m+1-k} V^{m+1+k}` in any real algebra
in which `V X = X V - V²`. -/
private theorem mul_pow_succ_eq_sum {R : Type*} [Ring R] [Algebra ℝ R] {X V : R}
    (h : V * X = X * V - V * V) (m : ℕ) :
    (X * V) ^ (m + 1) = ∑ k ∈ Finset.range (m + 1),
      ((-1 : ℝ) ^ k * ((besselPolynomial m).coeff k : ℝ)) •
        (X ^ (m + 1 - k) * V ^ (m + 1 + k)) := by
  induction m with
  | zero => simp [besselPolynomial_zero]
  | succ m ih =>
    obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ,
        c = fun k => (-1 : ℝ) ^ k * ((besselPolynomial m).coeff k : ℝ) := ⟨_, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : ℕ → R,
        T = fun k => X ^ (m + 1 + 1 - k) * V ^ (m + 1 + 1 + k) := ⟨_, rfl⟩
    have ih' : (X * V) ^ (m + 1) =
        ∑ k ∈ Finset.range (m + 1), c k • (X ^ (m + 1 - k) * V ^ (m + 1 + k)) := by
      rw [ih, hc]
    have hstep : ∀ k ∈ Finset.range (m + 1),
        (c k • (X ^ (m + 1 - k) * V ^ (m + 1 + k))) * (X * V) =
          c k • T k - (c k * ((m + 1 + k : ℕ) : ℝ)) • T (k + 1) := by
      intro k hk
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [hT]
      rw [show m + 1 + 1 - k = m + 1 - k + 1 by omega,
        show m + 1 + 1 - (k + 1) = m + 1 - k by omega,
        show m + 1 + 1 + (k + 1) = m + 1 + k + 1 + 1 by omega,
        show m + 1 + 1 + k = m + 1 + k + 1 by omega]
      rw [smul_mul_assoc, mul_assoc, ← mul_assoc (V ^ (m + 1 + k)), pow_mul_eq h, sub_mul,
        mul_sub, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ V (m + 1 + k + 1),
        pow_succ V (m + 1 + k), pow_succ X (m + 1 - k)]
      simp only [mul_assoc]
    have hR : ∑ k ∈ Finset.range (m + 1 + 1),
        ((-1 : ℝ) ^ k * ((besselPolynomial (m + 1)).coeff k : ℝ)) •
          (X ^ (m + 1 + 1 - k) * V ^ (m + 1 + 1 + k)) =
        ∑ k ∈ Finset.range (m + 1), (c (k + 1) - c k * ((m + 1 + k : ℕ) : ℝ)) • T (k + 1) +
          c 0 • T 0 := by
      rw [Finset.sum_range_succ']
      subst hc hT
      simp only [coeff_besselPolynomial_succ_succ, coeff_besselPolynomial_zero_right]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      push_cast
      ring
    have hlast : c (m + 1) = 0 := by
      simp only [hc]
      rw [coeff_besselPolynomial_of_lt (Nat.lt_add_one m)]
      simp
    have hsplit : ∑ k ∈ Finset.range (m + 1), c k • T k =
        ∑ k ∈ Finset.range (m + 1), c (k + 1) • T (k + 1) + c 0 • T 0 := by
      rw [← Finset.sum_range_succ' (fun k => c k • T k), Finset.sum_range_succ _ (m + 1), hlast,
        zero_smul, add_zero]
    rw [pow_succ, ih', Finset.sum_mul, Finset.sum_congr rfl hstep, hR, Finset.sum_sub_distrib,
      hsplit]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel

/-- The Volterra operator `g ↦ (y ↦ ∫_0^y g)` as a linear endomorphism of `C(ℝ, ℝ)`. -/
private noncomputable def volterra : Module.End ℝ C(ℝ, ℝ) where
  toFun g := ⟨fun y => ∫ t in (0 : ℝ)..y, g t,
    intervalIntegral.continuous_primitive (fun _ _ => g.continuous.intervalIntegrable _ _) 0⟩
  map_add' f g := by
    ext y
    exact intervalIntegral.integral_add (f.continuous.intervalIntegrable _ _)
      (g.continuous.intervalIntegrable _ _)
  map_smul' c g := by
    ext y
    simp [intervalIntegral.integral_const_mul]

/-- Multiplication by the identity function, as a linear endomorphism of `C(ℝ, ℝ)`. -/
private def mulX : Module.End ℝ C(ℝ, ℝ) where
  toFun g := ⟨fun y => y * g y, by fun_prop⟩
  map_add' f g := by
    ext y
    simp [mul_add]
  map_smul' c g := by
    ext y
    simp only [ContinuousMap.coe_smul, ContinuousMap.coe_mk, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

private theorem volterra_apply (g : C(ℝ, ℝ)) (y : ℝ) : volterra g y = ∫ t in (0 : ℝ)..y, g t :=
  rfl

private theorem mulX_apply (g : C(ℝ, ℝ)) (y : ℝ) : mulX g y = y * g y :=
  rfl

private theorem mulX_pow_apply (j : ℕ) (g : C(ℝ, ℝ)) (y : ℝ) : (mulX ^ j) g y = y ^ j * g y := by
  induction j generalizing g with
  | zero => simp
  | succ j ih => rw [pow_succ, mul_apply_eq_comp, ih, mulX_apply, pow_succ, mul_assoc]

/-- Integration by parts: `V X = X V - V²` on `C(ℝ, ℝ)`. -/
private theorem volterra_mul_mulX : volterra * mulX = mulX * volterra - volterra * volterra := by
  ext g y
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, ContinuousMap.sub_apply, volterra_apply,
    mulX_apply]
  have hG : Continuous fun u => ∫ t in (0 : ℝ)..u, g t :=
    intervalIntegral.continuous_primitive (fun _ _ => g.continuous.intervalIntegrable _ _) 0
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) y,
      HasDerivAt (fun u => u * (∫ t in (0 : ℝ)..u, g t) -
        ∫ v in (0 : ℝ)..u, ∫ t in (0 : ℝ)..v, g t) (s * g s) s := by
    intro s _
    have h1 := ((hasDerivAt_id' s).fun_mul
      (g.continuous.integral_hasStrictDerivAt 0 s).hasDerivAt).fun_sub
      (hG.integral_hasStrictDerivAt 0 s).hasDerivAt
    convert h1 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_id.mul g.continuous).intervalIntegrable _ _)]
  simp

end VolterraBesselExpansion

open VolterraBesselExpansion in
/-- **Expansion of $(XV)^n$ in Bessel numbers.** Let $X$ and $V$ be the operators on functions
$\mathbb{R} \to \mathbb{R}$ given by $(Xg)(y) = y \, g(y)$ and $(Vg)(y) = \int_0^y g(t) \, dt$,
write $(XV)^n$ and $V^m$ for iterated composition, and let $a(m, k)$ be the coefficient of $x^k$
in the Bessel polynomial $y_m$. For every natural number $n \ge 1$, every continuous function
$f : \mathbb{R} \to \mathbb{R}$ and every real number $x$,

$$(XV)^n f(x) = \sum_{k=0}^{n-1} (-1)^k \, a(n-1, k) \, x^{n-k} \, (V^{n+k} f)(x).$$

Source: Abdelhay Benmoussa, *On the Expansion of `(XV)^n` and Bessel Numbers*, Journal of
Integer Sequences 29 (2026), Article 26.3.5, Theorem 1 (`jis-2026-26.3.5-thm-1`). -/
public theorem xMul_volterra_iterate_eq_sum_bessel (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ)
    (hf : Continuous f) (x : ℝ) :
    (fun g : ℝ → ℝ => fun y => y * ∫ t in (0 : ℝ)..y, g t)^[n] f x =
      ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * ((besselPolynomial (n - 1)).coeff k : ℝ) *
        x ^ (n - k) * (fun g : ℝ → ℝ => fun y => ∫ t in (0 : ℝ)..y, g t)^[n + k] f x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set F : C(ℝ, ℝ) := ⟨f, hf⟩
  have hXV : Function.Semiconj (fun g : C(ℝ, ℝ) => (g : ℝ → ℝ)) ⇑(mulX * volterra)
      (fun g : ℝ → ℝ => fun y => y * ∫ t in (0 : ℝ)..y, g t) := fun _ => rfl
  have hV : Function.Semiconj (fun g : C(ℝ, ℝ) => (g : ℝ → ℝ)) ⇑volterra
      (fun g : ℝ → ℝ => fun y => ∫ t in (0 : ℝ)..y, g t) := fun _ => rfl
  have h1 : (fun g : ℝ → ℝ => fun y => y * ∫ t in (0 : ℝ)..y, g t)^[m + 1] f x =
      ((mulX * volterra) ^ (m + 1)) F x := by
    rw [pow_apply_eq_iterate]
    exact (congrFun (hXV.iterate_right (m + 1) F) x).symm
  have h2 : ∀ j, (fun g : ℝ → ℝ => fun y => ∫ t in (0 : ℝ)..y, g t)^[j] f x =
      (volterra ^ j) F x := by
    intro j
    rw [pow_apply_eq_iterate]
    exact (congrFun (hV.iterate_right j F) x).symm
  rw [h1, mul_pow_succ_eq_sum volterra_mul_mulX m, Nat.add_sub_cancel]
  simp only [LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
    ContinuousMap.coe_sum, ContinuousMap.coe_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_apply_eq_comp, mulX_pow_apply, h2]
  ring

end

end MetaMathlibExt
