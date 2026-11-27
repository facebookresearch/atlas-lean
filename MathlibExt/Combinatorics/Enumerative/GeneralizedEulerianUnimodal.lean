/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GeneralizedEulerianGamma
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Unimodality of the generalized Eulerian polynomials

For natural cycle and fixed-point weights, the coefficients increase up to the middle
and decrease thereafter. We differentiate the generating series in a basis whose
specialization at zero consists of shifted binomial polynomials with a common center.
-/

namespace MetaMathlibExt
namespace generalizedEulerianP_unimodal

open PowerSeries

private abbrev Series := PowerSeries ℚ
private abbrev Point := {x : ℚ // x ≠ 1}

private noncomputable def expAt (a : ℚ) : Series := rescale a (exp ℚ)

private lemma const_expAt (a : ℚ) : constantCoeff (expAt a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, expAt, coeff_rescale]
  simp

private lemma deriv_expAt (a : ℚ) : derivative (expAt a) = C a * expAt a := by
  ext n
  have h := congrArg (coeff n) (derivative_exp ℚ)
  rw [coeff_derivative] at h
  simp only [expAt, coeff_derivative, coeff_rescale, coeff_C_mul, pow_succ]
  linear_combination a ^ n * a * h

private noncomputable def den (x : Point) : Series := C x.val * exp ℚ - expAt x.val
private noncomputable def base (x : Point) : Series := C (x.val - 1) * (den x)⁻¹
private noncomputable def slope (x : Point) : Series := -derivative (den x) * (den x)⁻¹

private lemma const_den (x : Point) : constantCoeff (den x) = x.val - 1 := by
  simp [den, const_expAt]

private lemma const_base (x : Point) : constantCoeff (base x) = 1 := by
  simp [base, constantCoeff_inv, const_den, sub_ne_zero.mpr x.property]

private lemma deriv_den (x : Point) : derivative (den x) =
    C x.val * exp ℚ - C x.val * expAt x.val := by
  simp [den, derivative_exp, deriv_expAt]

private lemma const_slope (x : Point) : constantCoeff (slope x) = 0 := by
  simp [slope, deriv_den, const_expAt]

-- The denominator is a linear combination of exponentials with rates 1 and x.
-- Its second-order equation gives a Riccati equation for slope = −den′ / den.
private lemma deriv_slope (x : Point) : derivative (slope x) =
    slope x ^ 2 + C (x.val + 1) * slope x + C x.val := by
  have hd : derivative (derivative (den x)) =
      C (x.val + 1) * derivative (den x) - C x.val * den x := by
    rw [deriv_den, den]
    simp [derivative_exp, deriv_expAt]
    ring
  have hu := PowerSeries.mul_inv_cancel (den x) (by rw [const_den]; exact sub_ne_zero.mpr x.prop)
  simp only [slope, Derivation.leibniz, map_neg, derivative_inv', hd, smul_eq_mul]
  linear_combination C x.val * hu

private lemma deriv_base (x : Point) : derivative (base x) = base x * slope x := by
  simp only [base, slope, Derivation.leibniz, derivative_C, derivative_inv', smul_eq_mul]
  ring

private noncomputable def gen (q t : ℕ) (x : Point) : Series :=
  base x ^ q * expAt ((x.val + 1) * q * t)

private lemma gen_eq (q t : ℕ) (x : Point) : generalizedEulerianSeries q t x.val 1 = gen q t x := by
  have hs : HasSubst (base x - 1) := HasSubst.of_constantCoeff_zero' (by simp [const_base])
  simp only [generalizedEulerianSeries, rescale_one, RingHom.id_apply, map_one, one_mul]
  change ((binomialSeries ℚ (q : ℚ)).subst (base x - 1) : Series) * _ = _
  rw [binomialSeries_nat, ← coe_substAlgHom hs, map_pow, map_add, map_one, substAlgHom_X]
  simp [gen, expAt]

private lemma const_gen (q t : ℕ) (x : Point) : constantCoeff (gen q t x) = 1 := by
  simp [gen, const_base, const_expAt]

private lemma deriv_gen (q t : ℕ) (x : Point) : derivative (gen q t x) =
    C (q : ℚ) * (slope x * gen q t x) + C ((q * t : ℕ) : ℚ) *
      (C (x.val + 1) * gen q t x) := by
  cases q with
  | zero => simp [gen, deriv_expAt]
  | succ q =>
    rw [gen, Derivation.leibniz, derivative_pow]
    simp only [Nat.add_one_sub_one,
      deriv_base, deriv_expAt, smul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      map_mul, map_add, map_natCast, map_one, pow_succ]
    ring

-- Give the slope and x+1 weight one, and x weight two. The differential equations
-- express each derivative as a nonnegative combination of terms one weight higher.
private inductive Expansion (q t : ℕ) : ℕ → (Point → Series) → Prop
  | initial : Expansion q t 0 (gen q t)
  | add {d f g} : Expansion q t d f → Expansion q t d g →
      Expansion q t d (fun x => f x + g x)
  | scale {d f} (r : ℕ) : Expansion q t d f → Expansion q t d (fun x => C (r : ℚ) * f x)
  | linear {d f} : Expansion q t d f → Expansion q t (d + 1) (fun x => C (x.val + 1) * f x)
  | shift {d f} : Expansion q t d f → Expansion q t (d + 2) (fun x => C x.val * f x)
  | logDeriv {d f} : Expansion q t d f → Expansion q t (d + 1) (fun x => slope x * f x)

private lemma Expansion.differentiate {q t d f} (h : Expansion q t d f) :
    Expansion q t (d + 1) (fun x => derivative (f x)) := by
  induction h with
  | initial =>
    simp_rw [deriv_gen]
    exact .add (.scale q (.logDeriv .initial)) (.scale (q * t) (.linear .initial))
  | add hf hg ihf ihg =>
    simp only [map_add]
    exact .add ihf ihg
  | scale r hf ih =>
    simpa using ih.scale r
  | linear hf ih =>
    simpa using ih.linear
  | shift hf ih =>
    simpa using ih.shift
  | @logDeriv d f hf ih =>
    have he (x : Point) : derivative (slope x * f x) =
        slope x * (slope x * f x) + C (x.val + 1) * (slope x * f x) +
          C x.val * f x + slope x * derivative (f x) := by
      rw [Derivation.leibniz, deriv_slope]
      simp only [smul_eq_mul]
      ring
    simp_rw [he]
    exact .add (.add (.add hf.logDeriv.logDeriv hf.logDeriv.linear) hf.shift) ih.logDeriv

private def PeaksAtMiddle (d : ℕ) (p : Polynomial ℚ) : Prop :=
  (∀ i < d / 2, p.coeff i ≤ p.coeff (i + 1)) ∧
    ∀ i, d / 2 ≤ i → p.coeff (i + 1) ≤ p.coeff i

private lemma basis_peaks (b k : ℕ) :
    PeaksAtMiddle (b + 2 * k) (Polynomial.X ^ k * (Polynomial.X + 1) ^ b) := by
  simp only [PeaksAtMiddle, Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_add_one_pow]
  constructor
  · intro i hi
    split_ifs with h₁ h₂ h₂
    · rw [show i + 1 - k = (i - k) + 1 by omega]
      exact_mod_cast Nat.choose_le_succ_of_lt_half_left (show i - k < b / 2 by omega)
    · omega
    · positivity
    · rfl
  · intro i hi
    have hk : k ≤ i := by omega
    rw [ite_eq_left (by omega), ite_eq_left hk, show i + 1 - k = (i - k) + 1 by omega]
    exact_mod_cast (show b.choose (i - k + 1) ≤ b.choose (i - k) by
      apply Nat.le_of_mul_le_mul_right _ (Nat.succ_pos (i - k))
      rw [Nat.choose_succ_right_eq]
      exact Nat.mul_le_mul_left _ (by omega))

-- At z = 0 the slope vanishes. Every surviving term, including the factors
-- already stripped off in the induction, is a shifted binomial with the same center.
private lemma Expansion.specialize {q t d f} (h : Expansion q t d f) (b k : ℕ) :
    ∃ p : Polynomial ℚ, (∀ x : Point, p.eval x.val =
      x.val ^ k * (x.val + 1) ^ b * constantCoeff (f x)) ∧ PeaksAtMiddle (d + b + 2 * k) p := by
  induction h generalizing b k with
  | initial =>
    exact ⟨Polynomial.X ^ k * (Polynomial.X + 1) ^ b, fun x => by simp [const_gen],
      by simpa using basis_peaks b k⟩
  | add hf hg ihf ihg =>
    obtain ⟨p, hp, up⟩ := ihf b k
    obtain ⟨r, hr, ur⟩ := ihg b k
    refine ⟨p + r, fun x => by simp [hp, hr, mul_add], ?_, ?_⟩
    · exact fun i hi => by simpa using add_le_add (up.1 i hi) (ur.1 i hi)
    · exact fun i hi => by simpa using add_le_add (up.2 i hi) (ur.2 i hi)
  | scale a hf ih =>
    obtain ⟨p, hp, up⟩ := ih b k
    refine ⟨Polynomial.C (a : ℚ) * p, fun x => by simp [hp]; ring, ?_, ?_⟩
    · exact fun i hi => by simpa using mul_le_mul_of_nonneg_left (up.1 i hi) (Nat.cast_nonneg a)
    · exact fun i hi => by simpa using mul_le_mul_of_nonneg_left (up.2 i hi) (Nat.cast_nonneg a)
  | linear hf ih =>
    obtain ⟨p, hp, up⟩ := ih (b + 1) k
    exact ⟨p, fun x => by simp [hp, pow_succ]; ring, by convert up using 1; omega⟩
  | shift hf ih =>
    obtain ⟨p, hp, up⟩ := ih b (k + 1)
    exact ⟨p, fun x => by simp [hp, pow_succ]; ring, by convert up using 1; omega⟩
  | logDeriv hf ih =>
    exact ⟨0, fun x => by simp [const_slope], by simp [PeaksAtMiddle]⟩

end generalizedEulerianP_unimodal

open generalizedEulerianP_unimodal PowerSeries

/-- **Unimodality of the generalized Eulerian polynomials.** Let $P_n(q, t; x, y)$ be the
generalized Eulerian polynomial. For all natural numbers $q$, $t$ and $n$ there are a polynomial
$p$ with rational coefficients $p_0, p_1, p_2, \dots$ and an index $m$ such that
$p(x) = P_n(q, t; x, 1)$ for every rational $x \ne 1$, $p_i \le p_{i+1}$ for every $i < m$, and
$p_{i+1} \le p_i$ for every $i \ge m$. That is, $P_n(q, t; x, 1)$ is a unimodal polynomial in $x$.

Only unimodality is asserted, not symmetry of the coefficients.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Corollary 5
(`jis-2024-24.1.5-cor-5`). -/
public theorem generalizedEulerianP_unimodal (q t n : ℕ) :
    ∃ p : Polynomial ℚ, (∀ x : ℚ, x ≠ 1 → p.eval x = generalizedEulerianP q t x 1 n) ∧
      ∃ m : ℕ, (∀ i < m, p.coeff i ≤ p.coeff (i + 1)) ∧
        ∀ i, m ≤ i → p.coeff (i + 1) ≤ p.coeff i := by
  have h (d : ℕ) : Expansion q t d (fun x => derivative^[d] (gen q t x)) := by
    induction d with
    | zero => exact .initial
    | succ d ih => simpa only [Function.iterate_succ_apply'] using ih.differentiate
  obtain ⟨p, hp, up⟩ := (h n).specialize 0 0
  refine ⟨p, fun x hx => ?_, n / 2, by simpa [PeaksAtMiddle] using up⟩
  simpa [generalizedEulerianP, gen_eq q t ⟨x, hx⟩, constantCoeff_iterate_derivative]
    using hp ⟨x, hx⟩

end MetaMathlibExt
