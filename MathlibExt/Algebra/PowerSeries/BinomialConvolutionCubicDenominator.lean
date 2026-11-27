/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.BinomialProductGeometric
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Binomial products with a common cubic denominator

Expand the two series in geometric series, then group the binomial product by diagonal and
complementary pairs of roots. The complementary pair omitting `α i` has sum `-A - α i`,
which accounts for the factor `1 / (1 + A * X)`.
-/

namespace MetaMathlibExt

open PowerSeries

namespace BinomialConvolutionCubicDenominator

variable {K : Type*} [Field K]

private noncomputable def factor (a : K) : K⟦X⟧ := 1 - C a * X

private noncomputable def polyFactor (a : K) : Polynomial K :=
  1 - Polynomial.C a * Polynomial.X

private theorem coe_polyFactor (a : K) : (polyFactor a : K⟦X⟧) = factor a := by
  simp [polyFactor, factor]

private theorem constantCoeff_factor (a : K) : constantCoeff (factor a) = 1 := by
  simp [factor]

private noncomputable def geomSum (a w : Fin 3 → K) : K⟦X⟧ :=
  ∑ i, C (w i) * (factor (a i))⁻¹

private noncomputable def numerator (a w : Fin 3 → K) : Polynomial K :=
  Polynomial.C (w 0) * polyFactor (a 1) * polyFactor (a 2) +
  Polynomial.C (w 1) * polyFactor (a 0) * polyFactor (a 2) +
  Polynomial.C (w 2) * polyFactor (a 0) * polyFactor (a 1)

private theorem natDegree_polyFactor (a : K) : (polyFactor a).natDegree ≤ 1 := by
  unfold polyFactor
  exact Polynomial.natDegree_sub_le_of_le (m := 1) (n := 1) (by simp)
    (Polynomial.natDegree_mul_le.trans (by simp))

private theorem natDegree_numerator (a w : Fin 3 → K) : (numerator a w).natDegree ≤ 2 := by
  have h (x y z : K) : (Polynomial.C x * polyFactor y * polyFactor z).natDegree ≤ 2 :=
    Polynomial.natDegree_mul_le.trans
      (add_le_add (Polynomial.natDegree_mul_le.trans (by simpa using natDegree_polyFactor y))
        (natDegree_polyFactor z))
  exact Polynomial.natDegree_add_le_of_le
    (Polynomial.natDegree_add_le_of_le (h ..) (h ..)) (h ..)

private theorem geomSum_mul (a w : Fin 3 → K) :
    geomSum a w * (∏ i, factor (a i)) = (numerator a w : K⟦X⟧) := by
  have hi (x : K) : (factor x)⁻¹ * factor x = 1 :=
    PowerSeries.inv_mul_cancel _ (by simp [constantCoeff_factor])
  rw [geomSum, Fin.sum_univ_three, Fin.prod_univ_three]
  simp only [numerator, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, coe_polyFactor,
    add_mul]
  congr 1
  · congr 1
    · calc
        _ = (C (w 0) * ((factor (a 0))⁻¹ * factor (a 0))) * factor (a 1) * factor (a 2) := by
          ac_rfl
        _ = _ := by rw [hi, mul_one]
    · calc
        _ = (C (w 1) * ((factor (a 1))⁻¹ * factor (a 1))) * factor (a 0) * factor (a 2) := by
          ac_rfl
        _ = _ := by rw [hi, mul_one]
  · calc
      _ = (C (w 2) * ((factor (a 2))⁻¹ * factor (a 2))) * factor (a 0) * factor (a 1) := by
        ac_rfl
      _ = _ := by rw [hi, mul_one]

private theorem geomSum_eq_mul_inv (a w : Fin 3 → K) :
    geomSum a w = (numerator a w : K⟦X⟧) * (∏ i, factor (a i))⁻¹ := by
  rw [← geomSum_mul, mul_assoc, PowerSeries.mul_inv_cancel, mul_one]
  simp [constantCoeff_factor, Fin.prod_univ_three]

private theorem eval_polyFactor_self {a : K} (ha : a ≠ 0) :
    (polyFactor a).eval a⁻¹ = 0 := by
  simp [polyFactor, ha]

private theorem eval_polyFactor_ne_zero {a b : K} (ha : a ≠ 0) (hab : a ≠ b) :
    (polyFactor b).eval a⁻¹ ≠ 0 := by
  simp only [polyFactor, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, sub_ne_zero]
  intro h
  apply hab
  simpa [mul_assoc, ha] using congrArg (· * a) h

private theorem exists_geomSum (a : Fin 3 → K) (ha : ∀ i, a i ≠ 0)
    (hinj : Function.Injective a) (p : Polynomial K) (hp : p.degree < 3) (f : K⟦X⟧)
    (hf : f * ∏ i, factor (a i) = (p : K⟦X⟧)) : ∃ w, f = geomSum a w := by
  let w : Fin 3 → K := ![p.eval (a 0)⁻¹ / ((polyFactor (a 1)).eval (a 0)⁻¹ *
      (polyFactor (a 2)).eval (a 0)⁻¹),
    p.eval (a 1)⁻¹ / ((polyFactor (a 0)).eval (a 1)⁻¹ * (polyFactor (a 2)).eval (a 1)⁻¹),
    p.eval (a 2)⁻¹ / ((polyFactor (a 0)).eval (a 2)⁻¹ * (polyFactor (a 1)).eval (a 2)⁻¹)]
  have hz (i j : Fin 3) (h : i ≠ j) : (polyFactor (a j)).eval (a i)⁻¹ ≠ 0 :=
    eval_polyFactor_ne_zero (ha i) (hinj.ne h)
  have hself (i : Fin 3) : (polyFactor (a i)).eval (a i)⁻¹ = 0 :=
    eval_polyFactor_self (ha i)
  have hn : numerator a w = p := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _
      (inv_injective.comp hinj : Function.Injective (fun i ↦ (a i)⁻¹))
    · intro i
      fin_cases i <;>
        simp [numerator, w, hself, div_eq_mul_inv, hz,
          mul_left_comm, mul_comm]
    · have hp' : p.natDegree < 3 := by
        by_cases h : p = 0
        · simp [h]
        · exact (Polynomial.natDegree_lt_iff_degree_lt h).mpr hp
      simpa using max_lt (lt_of_le_of_lt (natDegree_numerator a w) (show 2 < 3 by decide)) hp'
  refine ⟨w, ?_⟩
  apply mul_right_cancel₀ (b := ∏ i, factor (a i))
  · exact fun h ↦ by
      have h0 := congrArg constantCoeff h
      simp [Fin.prod_univ_three, constantCoeff_factor] at h0
  · rw [hf, geomSum_mul, hn]

private theorem cubic_expansion (a b c : K) :
    factor a * factor b * factor c =
      1 - C (a + b + c) * X + C (a * b + a * c + b * c) * X ^ 2 -
        C (a * b * c) * X ^ 3 := by
  simp only [factor, map_add, map_mul]
  ring

private theorem binomialProduct_add_left (f g h : K⟦X⟧) :
    binomialProduct (f + g) h = binomialProduct f h + binomialProduct g h := by
  ext n
  simp only [coeff_binomialProduct, map_add, add_mul, mul_add, Finset.sum_add_distrib]

private theorem binomialProduct_add_right (f g h : K⟦X⟧) :
    binomialProduct f (g + h) = binomialProduct f g + binomialProduct f h := by
  ext n
  simp only [coeff_binomialProduct, map_add, mul_add, Finset.sum_add_distrib]

variable [CharZero K]

private theorem binomialProduct_weighted_geom (a b x y : K) :
    binomialProduct (C x * (factor a)⁻¹) (C y * (factor b)⁻¹) =
      C (x * y) * (factor (a + b))⁻¹ := by
  have h : binomialProduct (factor a)⁻¹ (factor b)⁻¹ = (factor (a + b))⁻¹ := by
    simpa [factor] using binomialProduct_X_pow_mul_inv_pow 0 0 a b
  rw [← h]
  ext n
  simp only [coeff_binomialProduct, coeff_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem binomialProduct_geomSum (a x y : Fin 3 → K) (A : K)
    (hA : A = -(a 0 + a 1 + a 2)) :
    binomialProduct (geomSum a x) (geomSum a y) =
      geomSum (fun i ↦ 2 * a i) (fun i ↦ x i * y i) +
        binomialProduct (factor (-A))⁻¹
          (geomSum (fun i ↦ -a i)
            ![x 1 * y 2 + x 2 * y 1, x 0 * y 2 + x 2 * y 0, x 0 * y 1 + x 1 * y 0]) := by
  rw [← one_mul ((factor (-A))⁻¹), ← (map_one (C : K →+* K⟦X⟧))]
  have h01 : -A + -a 2 = a 0 + a 1 := by rw [hA]; ring
  have h02 : -A + -a 1 = a 0 + a 2 := by rw [hA]; ring
  have h12 : -A + -a 0 = a 1 + a 2 := by rw [hA]; ring
  simp only [geomSum, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, binomialProduct_add_left,
    binomialProduct_add_right,
    binomialProduct_weighted_geom, one_mul, h01, h02, h12, two_mul, map_add, add_mul]
  rw [add_comm (a 1) (a 0), add_comm (a 2) (a 0), add_comm (a 2) (a 1)]
  ring

end BinomialConvolutionCubicDenominator

open BinomialConvolutionCubicDenominator

/-- **Binomial products of series with a cubic denominator.** Let $K$ be a field of characteristic
$0$, let $A, B, C \in K$ with $C \ne 0$, and let $D(x) = 1 + Ax + Bx^2 + Cx^3$. Suppose that
$D(x) = \prod_{i=1}^{3} (1 - \alpha_i x)$ with $\alpha_1, \alpha_2, \alpha_3 \in K$ and that
$2\alpha_i \ne \alpha_j + \alpha_k$ whenever $i, j, k \in \{1, 2, 3\}$ are not all equal. Let $r$
and $s$ be power series over $K$ such that $r D$ and $s D$ are polynomials of degree less than $3$.
Then there are polynomials $u$, $v$ over $K$ of degree at most $2$ such that

$$r \odot s = \frac{u(x)}{D(2x)} + \frac{1}{1 + Ax} \odot \frac{v(x)}{D(-x)},$$

where $\odot$ is the binomial product.

The second term uses the factor $1/(1 + Ax)$; with $1/(1 - Ax)$ in its place the statement already
fails for the tribonacci series $x/(1 - x - x^2 - x^3)$, where $A = -1$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 12 (`jis-2024-24.1.3-thm-12`). -/
public theorem binomialProduct_cubic_denominator {K : Type*} [Field K] [CharZero K]
    (A B C' : K) (hC : C' ≠ 0) (α : Fin 3 → K)
    (hD : 1 + C A * X + C B * X ^ 2 + C C' * X ^ 3 = ∏ i, (1 - C (α i) * X))
    (hα : ∀ i j k, ¬(i = j ∧ j = k) → 2 * α i ≠ α j + α k)
    (r s : PowerSeries K) (pr ps : Polynomial K) (hpr : pr.degree < 3) (hps : ps.degree < 3)
    (hr : r * (1 + C A * X + C B * X ^ 2 + C C' * X ^ 3) = (pr : PowerSeries K))
    (hs : s * (1 + C A * X + C B * X ^ 2 + C C' * X ^ 3) = (ps : PowerSeries K)) :
    ∃ u v : Polynomial K, u.natDegree ≤ 2 ∧ v.natDegree ≤ 2 ∧
      binomialProduct r s =
        (u : PowerSeries K) * (1 + C (2 * A) * X + C (4 * B) * X ^ 2 + C (8 * C') * X ^ 3)⁻¹ +
          binomialProduct (1 + C A * X)⁻¹
            ((v : PowerSeries K) * (1 - C A * X + C B * X ^ 2 - C C' * X ^ 3)⁻¹) := by
  have hFac : 1 + C A * X + C B * X ^ 2 + C C' * X ^ 3 = ∏ i, factor (α i) := hD
  have hExp := hFac
  rw [Fin.prod_univ_three, cubic_expansion] at hExp
  have hCoeff (n : ℕ) := congrArg (coeff n) hExp
  simp only [map_add (coeff _), map_sub (coeff _), coeff_C_mul, coeff_X, coeff_X_pow,
    coeff_one] at hCoeff
  have hA : A = -(α 0 + α 1 + α 2) := by simpa using hCoeff 1
  have hB : B = α 0 * α 1 + α 0 * α 2 + α 1 * α 2 := by simpa using hCoeff 2
  have hC' : C' = -(α 0 * α 1 * α 2) := by simpa using hCoeff 3
  have hnz : α 0 * α 1 * α 2 ≠ 0 := by simpa [hC'] using hC
  have hne (i : Fin 3) : α i ≠ 0 := by
    obtain ⟨h01, h2⟩ := mul_ne_zero_iff.mp hnz
    obtain ⟨h0, h1⟩ := mul_ne_zero_iff.mp h01
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hinj : Function.Injective α := by
    intro i j h
    by_contra hij
    exact hα i i j (fun he ↦ hij he.2) (by rw [← h, two_mul])
  obtain ⟨x, hx⟩ := exists_geomSum α hne hinj pr hpr r (hFac ▸ hr)
  obtain ⟨y, hy⟩ := exists_geomSum α hne hinj ps hps s (hFac ▸ hs)
  have hDouble : (∏ i, factor (2 * α i)) =
      1 + C (2 * A) * X + C (4 * B) * X ^ 2 + C (8 * C') * X ^ 3 := by
    rw [Fin.prod_univ_three, cubic_expansion, hA, hB, hC']
    simp only [map_add, map_mul, map_neg, map_ofNat]
    ring
  have hNeg : (∏ i, factor (-α i)) = 1 - C A * X + C B * X ^ 2 - C C' * X ^ 3 := by
    rw [Fin.prod_univ_three, cubic_expansion, hA, hB, hC']
    simp only [map_add, map_mul, map_neg]
    ring
  have hShift : factor (-A) = 1 + C A * X := by simp [factor, sub_eq_add_neg]
  rw [hx, hy, binomialProduct_geomSum α x y A hA, geomSum_eq_mul_inv,
    geomSum_eq_mul_inv (fun i ↦ -α i), hDouble, hNeg, hShift]
  exact ⟨_, _, natDegree_numerator .., natDegree_numerator .., rfl⟩

end MetaMathlibExt
