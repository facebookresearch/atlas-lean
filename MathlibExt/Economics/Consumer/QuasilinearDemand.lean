/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.TwoGood
public import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.BigOperators.Fin
/-!
# Quasilinear demand with an interior/corner solution

For the quasilinear utility `u(x) = 2 √x₀ + x₁` (concave in good `0`, linear in the numeraire
good `1`) with positive prices and nonnegative wealth, the demand is piecewise: the interior
solution `x₀ = (p₁ / p₀)²`, `x₁ = (w - p₁² / p₀) / p₁` when wealth covers the satiation spending
`p₁² / p₀` on good `0`, and otherwise the corner `x₀ = w / p₀`, `x₁ = 0`.

## Main definitions

* `quasilinearSqrt`: the utility `2 √x₀ + x₁`.
* `quasilinearSqrtDemand p w`: the piecewise bundle.

## Main results

* `isMarshallianDemand_quasilinearSqrt`: the piecewise bundle is a Marshallian demand on the
  nonnegative orthant.

The square root is chosen over the logarithm because `Real.log 0 = 0` in Mathlib would make the
corner comparison false at `x₀ = 0`.

Atlas roadmap target EC03.T02.

## References

* H. R. Varian, *Intermediate Microeconomics*, 9th ed., Norton (2014), ch. 5.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), ch. 3.
-/

@[expose] public section

namespace MathlibExt.Economics.Consumer

open Matrix

/-- The quasilinear utility `u(x) = 2 √x₀ + x₁`: concave in good `0`, linear in the
numeraire good `1`. -/
noncomputable def quasilinearSqrt (x : Fin 2 → ℝ) : ℝ :=
  2 * Real.sqrt (x 0) + x 1

/-- The piecewise demand for `quasilinearSqrt`: the interior solution
`x₀ = (p₁ / p₀)²`, `x₁ = (w - p₁² / p₀) / p₁` when wealth covers the satiation spending
`p₁² / p₀` on good `0`, and otherwise the corner `x₀ = w / p₀`, `x₁ = 0`. -/
noncomputable def quasilinearSqrtDemand (p : Fin 2 → ℝ) (w : ℝ) : Fin 2 → ℝ :=
  if p 1 ^ 2 / p 0 ≤ w then ![(p 1 / p 0) ^ 2, (w - p 1 ^ 2 / p 0) / p 1]
  else ![w / p 0, 0]

/-- **Quasilinear demand.** With positive prices and nonnegative wealth, the piecewise
interior/corner bundle maximizes `quasilinearSqrt` over the budget set in the nonnegative
orthant. -/
theorem isMarshallianDemand_quasilinearSqrt {w : ℝ} {p : Fin 2 → ℝ} (hp : ∀ i, 0 < p i)
    (hw : 0 ≤ w) :
    IsMarshallianDemand quasilinearSqrt twoGoodSet p w (quasilinearSqrtDemand p w) := by
  have hp0 : 0 < p 0 := hp 0
  have hp1 : 0 < p 1 := hp 1
  have hp0ne : p 0 ≠ 0 := ne_of_gt hp0
  have hp1ne : p 1 ≠ 0 := ne_of_gt hp1
  have hs : 0 < p 1 / p 0 := by positivity
  have hsne : p 1 / p 0 ≠ 0 := div_ne_zero hp1ne hp0ne
  have amgm : ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, 0 < s → 2 * Real.sqrt t ≤ t / s + s := by
    intro t ht s hs'
    have hsq : (0:ℝ) ≤ (Real.sqrt t - s) ^ 2 := sq_nonneg _
    rw [sub_sq, Real.sq_sqrt ht] at hsq
    have h2 : 2 * Real.sqrt t * s ≤ t + s ^ 2 := by linarith
    have hsne' : s ≠ 0 := ne_of_gt hs'
    calc 2 * Real.sqrt t = (2 * Real.sqrt t * s) / s := by field_simp
      _ ≤ (t + s ^ 2) / s := by
          rw [div_le_iff₀ hs', div_mul_cancel₀ _ hsne']
          exact h2
      _ = t / s + s := by field_simp
  unfold quasilinearSqrtDemand
  split_ifs with h
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · change ∀ i, 0 ≤ ![((p 1 / p 0) ^ 2), ((w - p 1 ^ 2 / p 0) / p 1)] i
        rw [Fin.forall_fin_two]
        constructor
        · simp only [Matrix.cons_val_zero]
          positivity
        · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
          exact div_nonneg (by linarith) (le_of_lt hp1)
      · have hdot : p ⬝ᵥ ![((p 1 / p 0) ^ 2), ((w - p 1 ^ 2 / p 0) / p 1)] = w := by
          simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one]
          field_simp
          ring
        exact hdot.le
    · intro y hy
      obtain ⟨hyX, hybud⟩ := hy
      have hy0 : 0 ≤ y 0 := hyX 0
      simp only [dotProduct, Fin.sum_univ_two] at hybud
      have key := amgm (y 0) hy0 (p 1 / p 0) hs
      have hdiv : (p 0 * y 0 + p 1 * y 1) / p 1 ≤ w / p 1 := by
        rw [div_le_iff₀ hp1, div_mul_cancel₀ _ hp1ne]
        exact hybud
      have hcomb : y 0 / (p 1 / p 0) + y 1 = (p 0 * y 0 + p 1 * y 1) / p 1 := by
        field_simp
      have hux : quasilinearSqrt ![((p 1 / p 0) ^ 2), ((w - p 1 ^ 2 / p 0) / p 1)]
          = w / p 1 + p 1 / p 0 := by
        simp only [quasilinearSqrt, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [Real.sqrt_sq (by positivity : (0:ℝ) ≤ p 1 / p 0)]
        field_simp
        ring
      rw [hux]
      change 2 * Real.sqrt (y 0) + y 1 ≤ w / p 1 + p 1 / p 0
      calc 2 * Real.sqrt (y 0) + y 1
          ≤ (y 0 / (p 1 / p 0) + p 1 / p 0) + y 1 := by linarith [key]
        _ = (y 0 / (p 1 / p 0) + y 1) + p 1 / p 0 := by ring
        _ = (p 0 * y 0 + p 1 * y 1) / p 1 + p 1 / p 0 := by rw [hcomb]
        _ ≤ w / p 1 + p 1 / p 0 := by linarith [hdiv]
  · replace h : w < p 1 ^ 2 / p 0 := lt_of_not_ge h
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · change ∀ i, 0 ≤ ![w / p 0, 0] i
        rw [Fin.forall_fin_two]
        constructor
        · simp only [Matrix.cons_val_zero]
          exact div_nonneg hw (le_of_lt hp0)
        · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
          exact le_rfl
      · have hdot : p ⬝ᵥ ![w / p 0, 0] = w := by
          simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one]
          field_simp
          ring
        exact hdot.le
    · intro y hy
      obtain ⟨hyX, hybud⟩ := hy
      have hy0 : 0 ≤ y 0 := hyX 0
      simp only [dotProduct, Fin.sum_univ_two] at hybud
      have hW : 0 ≤ w / p 0 := div_nonneg hw (le_of_lt hp0)
      have hy0le : y 0 ≤ w / p 0 := by
        have h2 : 0 ≤ p 1 * y 1 := mul_nonneg (le_of_lt hp1) (hyX 1)
        have h1 : p 0 * y 0 ≤ w := by linarith
        rw [le_div_iff₀ hp0, mul_comm (y 0) (p 0)]
        exact h1
      have hy1le : y 1 ≤ (w - p 0 * y 0) / p 1 := by
        rw [le_div_iff₀ hp1, mul_comm (y 1) (p 1)]
        linarith [hybud]
      have hcon : (w - p 0 * y 0) / p 1 = (w / p 0 - y 0) / (p 1 / p 0) := by
        field_simp
      have hWs : w / p 0 < (p 1 / p 0) ^ 2 := by
        have e1 : (p 1 / p 0) ^ 2 = (p 1 ^ 2 / p 0) / p 0 := by
          field_simp
        rw [e1, div_lt_iff₀ hp0, div_mul_cancel₀ _ hp0ne]
        exact h
      have hbs : Real.sqrt (w / p 0) < p 1 / p 0 := by
        have hlt := Real.sqrt_lt_sqrt hW hWs
        rwa [Real.sqrt_sq (le_of_lt hs)] at hlt
      have hab : Real.sqrt (y 0) ≤ Real.sqrt (w / p 0) := Real.sqrt_le_sqrt hy0le
      have hsq : (p 1 / p 0 - Real.sqrt (w / p 0)) ^ 2
          ≤ (p 1 / p 0 - Real.sqrt (y 0)) ^ 2 :=
        sq_le_sq' (by linarith [hab, hbs]) (by linarith [hab])
      have hkey : 2 * Real.sqrt (y 0) + (w / p 0 - y 0) / (p 1 / p 0)
          ≤ 2 * Real.sqrt (w / p 0) := by
        have hsq2 : (0:ℝ) ≤ (p 1 / p 0 - Real.sqrt (y 0)) ^ 2
            - (p 1 / p 0 - Real.sqrt (w / p 0)) ^ 2 := by linarith [hsq]
        rw [sub_sq, sub_sq, Real.sq_sqrt hy0, Real.sq_sqrt hW] at hsq2
        have hmul : 2 * Real.sqrt (y 0) * (p 1 / p 0) + (w / p 0 - y 0)
            ≤ 2 * Real.sqrt (w / p 0) * (p 1 / p 0) := by linarith [hsq2]
        have hdiv2 : (2 * Real.sqrt (y 0) * (p 1 / p 0) + (w / p 0 - y 0))
            / (p 1 / p 0)
            ≤ (2 * Real.sqrt (w / p 0) * (p 1 / p 0)) / (p 1 / p 0) := by
          rw [div_le_iff₀ hs, div_mul_cancel₀ _ hsne]
          exact hmul
        have e1 : (2 * Real.sqrt (y 0) * (p 1 / p 0) + (w / p 0 - y 0))
            / (p 1 / p 0)
            = 2 * Real.sqrt (y 0) + (w / p 0 - y 0) / (p 1 / p 0) := by
          field_simp
        have e2 : (2 * Real.sqrt (w / p 0) * (p 1 / p 0)) / (p 1 / p 0)
            = 2 * Real.sqrt (w / p 0) := by
          field_simp
        rw [e1, e2] at hdiv2
        exact hdiv2
      have hux0 : quasilinearSqrt ![w / p 0, 0] = 2 * Real.sqrt (w / p 0) := by
        simp only [quasilinearSqrt, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      rw [hux0]
      change 2 * Real.sqrt (y 0) + y 1 ≤ 2 * Real.sqrt (w / p 0)
      calc 2 * Real.sqrt (y 0) + y 1
          ≤ 2 * Real.sqrt (y 0) + (w - p 0 * y 0) / p 1 := by linarith [hy1le]
        _ = 2 * Real.sqrt (y 0) + (w / p 0 - y 0) / (p 1 / p 0) := by rw [hcon]
        _ ≤ 2 * Real.sqrt (w / p 0) := hkey

end MathlibExt.Economics.Consumer
