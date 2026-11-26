/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Ordered dot-product error bound

The ideal output `y = ∑ k, h k * x k` is computed by an exact
zero-initialized left fold whose inputs, coefficients, products and
accumulation steps carry additive perturbations bounded by
`ex, eh, ep, ea`. The accumulated error satisfies

`|ŷ - y| ≤ ex * ∑ k, |h k| + eh * ∑ k, |x k| + m * eh * ex + m * ep + m * ea`,

with the coefficient/input cross term `m * eh * ex` retained: each
perturbed product is `(h k + dh k) * (x k + dx k)`, expanded exactly,
not linearized. The fold is summed in index order; no reordering or
floating-point rounding model is introduced.
-/

@[expose] public section

namespace MathlibExt.Analysis.Numerical.OrderedDotProductError

/-- Perturbed input: xhat_k = x_k + dx_k. -/
def inputPerturbed (m : ℕ) (x dx : Fin m → ℝ) (k : Fin m) : ℝ :=
  x k + dx k

/-- Perturbed coefficient: hhat_k = h_k + dh_k. -/
def coeffPerturbed (m : ℕ) (h dh : Fin m → ℝ) (k : Fin m) : ℝ :=
  h k + dh k

/-- Perturbed product: phat_k = hhat_k * xhat_k + dp_k. -/
def productPerturbed (m : ℕ) (h dh x dx dp : Fin m → ℝ) (k : Fin m) : ℝ :=
  coeffPerturbed m h dh k * inputPerturbed m x dx k + dp k

/-- Exact left fold with zero initialization:
accumulator p d 0 = 0 and
accumulator p d (n+1) = accumulator p d n + p n + d n. -/
def accumulator (p d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => accumulator p d n + p n + d n

/-- Lift f : Fin m -> R to N -> R, zero outside the range. -/
def extend (m : ℕ) (f : Fin m → ℝ) : ℕ → ℝ :=
  fun i => if h : i < m then f ⟨i, h⟩ else 0

/-- Perturbed output yhat = ahat_m for the exact left fold. -/
def outputPerturbed (m : ℕ) (h dh x dx dp da : Fin m → ℝ) : ℝ :=
  accumulator (extend m (productPerturbed m h dh x dx dp)) (extend m da) m

/-- Ideal output y = sum_k (h_k * x_k). -/
def outputIdeal (m : ℕ) (h x : Fin m → ℝ) : ℝ :=
  ∑ k : Fin m, h k * x k

/-- The fold starts at exactly zero. -/
theorem accumulator_zero (p d : ℕ → ℝ) :
    accumulator p d 0 = 0 := by
  rfl

/-- One step of the exact left fold: `s (n + 1) = s n + p n + d n`. -/
theorem accumulator_succ (p d : ℕ → ℝ) (n : ℕ) :
    accumulator p d (n + 1) = accumulator p d n + p n + d n := by
  rfl

/-- extend agrees with f inside the range. -/
theorem extend_apply_of_lt (m : ℕ) (f : Fin m → ℝ) (i : ℕ) (hi : i < m) :
    extend m f i = f ⟨i, hi⟩ := by
  simp [extend, hi]

theorem accumulator_eq_sum_range (p d : ℕ → ℝ) (n : ℕ) :
    accumulator p d n = ∑ i ∈ Finset.range n, (p i + d i) := by
  induction n with
  | zero =>
    rw [accumulator_zero, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [accumulator_succ, ih, Finset.sum_range_succ]
    exact add_assoc _ _ _

/-- The m-step fold is the finite sum of its per-index increments. -/
theorem accumulator_extend_eq_sum (m : ℕ) (p d : Fin m → ℝ) :
    accumulator (extend m p) (extend m d) m = ∑ k : Fin m, (p k + d k) := by
  rw [accumulator_eq_sum_range]
  refine Finset.sum_bij (fun a ha => (⟨a, Finset.mem_range.mp ha⟩ : Fin m)) ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_univ _
  · intro a₁ _ a₂ _ h
    exact congrArg Fin.val h
  · intro b _
    exact ⟨b.val, Finset.mem_range.mpr b.isLt, Fin.eta b _⟩
  · intro a ha
    rw [extend_apply_of_lt m p a (Finset.mem_range.mp ha),
      extend_apply_of_lt m d a (Finset.mem_range.mp ha)]

/-- Product-error expansion, with the cross term dh_k * dx_k retained:
phat_k - h_k * x_k = h_k * dx_k + dh_k * x_k + dh_k * dx_k + dp_k. -/
theorem product_sub (m : ℕ) (h dh x dx dp : Fin m → ℝ) (k : Fin m) :
    productPerturbed m h dh x dx dp k - h k * x k
      = h k * dx k + dh k * x k + dh k * dx k + dp k := by
  simp only [productPerturbed, coeffPerturbed, inputPerturbed]
  rw [add_mul (h k) (dh k) (x k + dx k),
    mul_add (h k) (x k) (dx k),
    mul_add (dh k) (x k) (dx k),
    add_assoc (h k * x k) (h k * dx k) (dh k * x k + dh k * dx k),
    add_assoc (h k * x k) (h k * dx k + (dh k * x k + dh k * dx k)) (dp k),
    add_sub_cancel_left (h k * x k)
      (h k * dx k + (dh k * x k + dh k * dx k) + dp k),
    ← add_assoc (h k * dx k) (dh k * x k) (dh k * dx k)]

/-- Finite filter and fixed-point error composition:
|yhat - y| <= ex * sum |h| + eh * sum |x| + m * eh * ex + m * ep + m * ea,
with yhat the m-step zero-initialized left fold and y = sum h_k * x_k. -/
theorem orderedDotProduct_error_bound (m : ℕ) (h dh x dx dp da : Fin m → ℝ)
    (ex eh ep ea : ℝ)
    (hex : 0 ≤ ex) (heh : 0 ≤ eh) (hep : 0 ≤ ep) (hea : 0 ≤ ea)
    (hdx : ∀ k : Fin m, |dx k| ≤ ex)
    (hdh : ∀ k : Fin m, |dh k| ≤ eh)
    (hdp : ∀ k : Fin m, |dp k| ≤ ep)
    (hda : ∀ k : Fin m, |da k| ≤ ea) :
    |outputPerturbed m h dh x dx dp da - outputIdeal m h x|
      ≤ ex * (∑ k : Fin m, |h k|) + eh * (∑ k : Fin m, |x k|)
        + (m : ℝ) * eh * ex + (m : ℝ) * ep + (m : ℝ) * ea := by
  have _ := hex
  have _ := hep
  have _ := hea
  have hfold : outputPerturbed m h dh x dx dp da
      = ∑ k : Fin m, (productPerturbed m h dh x dx dp k + da k) := by
    unfold outputPerturbed
    exact accumulator_extend_eq_sum m _ _
  have hterm : ∀ k : Fin m,
      (productPerturbed m h dh x dx dp k + da k - h k * x k)
        = h k * dx k + dh k * x k + dh k * dx k + dp k + da k := by
    intro k
    rw [add_sub_right_comm, product_sub m h dh x dx dp k]
  have hdiff : outputPerturbed m h dh x dx dp da - outputIdeal m h x
      = ∑ k : Fin m, (h k * dx k + dh k * x k + dh k * dx k + dp k + da k) := by
    rw [hfold]
    unfold outputIdeal
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => hterm k)
  have hbound : ∀ k : Fin m,
      |h k * dx k + dh k * x k + dh k * dx k + dp k + da k|
        ≤ |h k| * ex + eh * |x k| + eh * ex + ep + ea := by
    intro k
    have e1 := abs_add_le (h k * dx k + dh k * x k + dh k * dx k + dp k) (da k)
    have e2 := abs_add_le (h k * dx k + dh k * x k + dh k * dx k) (dp k)
    have e3 := abs_add_le (h k * dx k + dh k * x k) (dh k * dx k)
    have e4 := abs_add_le (h k * dx k) (dh k * x k)
    have b1 : |h k * dx k| ≤ |h k| * ex := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hdx k) (abs_nonneg _)
    have b2 : |dh k * x k| ≤ eh * |x k| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hdh k) (abs_nonneg _)
    have b3 : |dh k * dx k| ≤ eh * ex := by
      rw [abs_mul]
      exact mul_le_mul (hdh k) (hdx k) (abs_nonneg _) heh
    have b4 : |dp k| ≤ ep := hdp k
    have b5 : |da k| ≤ ea := hda k
    refine le_trans e1 ?_
    refine le_trans (add_le_add e2 (le_refl _)) ?_
    refine le_trans (add_le_add (add_le_add e3 (le_refl _)) (le_refl _)) ?_
    refine le_trans
      (add_le_add (add_le_add (add_le_add e4 (le_refl _)) (le_refl _)) (le_refl _)) ?_
    exact add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5
  have hsum : ∑ k : Fin m, (|h k| * ex + eh * |x k| + eh * ex + ep + ea)
      = ex * (∑ k : Fin m, |h k|) + eh * (∑ k : Fin m, |x k|)
        + (m : ℝ) * eh * ex + (m : ℝ) * ep + (m : ℝ) * ea := by
    have sA : ∑ k : Fin m, |h k| * ex = ex * (∑ k : Fin m, |h k|) := by
      rw [← Finset.sum_mul, mul_comm (∑ k : Fin m, |h k|) ex]
    have sB : ∑ k : Fin m, eh * |x k| = eh * (∑ k : Fin m, |x k|) :=
      (Finset.mul_sum _ _ _).symm
    have sC : ∑ k : Fin m, eh * ex = (m : ℝ) * eh * ex := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← mul_assoc]
    have sD : (∑ k : Fin m, ep) = (m : ℝ) * ep := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have sE : (∑ k : Fin m, ea) = (m : ℝ) * ea := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, sA, sB, sC, sD, sE]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun k _ => hbound k)) ?_
  rw [hsum]

end MathlibExt.Analysis.Numerical.OrderedDotProductError
