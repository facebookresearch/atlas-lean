/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Weighted quadrature rules

A quadrature rule approximates a weighted integral on `(a, b)` by a finite sum of
values at nodes in `[a, b]`. The weight is independent of the nodes and coefficients
and is defined only on `(a, b)`, so it may be unbounded near the endpoints.
Exactness through degree `m` is equivalent to matching the moments of orders `0` through `m`.

## Reference

* D. Levy, *Introduction to Numerical Analysis*, University of Maryland, 4 January 2021,
  §§6.2, 6.4.1, and 6.6 (formula (6.27)). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace MetaMathlibExt

/-- A continuous, nonnegative weight on a nondegenerate open interval `(a, b)` with
finite positive mass. No extension to the endpoints is required. -/
structure QuadratureWeight (a b : ℝ) where
  /-- The interval has positive length. -/
  lt : a < b
  /-- The weight on the open interval. -/
  weight : Ioo a b → ℝ
  /-- The weight is continuous on the open interval. -/
  continuous_weight : Continuous weight
  /-- The weight is nonnegative on the open interval. -/
  weight_nonneg (x : Ioo a b) : 0 ≤ weight x
  /-- The integral of the weight is positive. -/
  weight_mass_pos : 0 < ∫ x, weight x ∂(Measure.comap Subtype.val (volume : Measure ℝ))

namespace QuadratureWeight

variable {a b : ℝ}

/-- The constant-one weight gives ordinary Lebesgue integration on `(a, b)`. -/
noncomputable def one (hab : a < b) : QuadratureWeight a b where
  lt := hab
  weight _ := 1
  continuous_weight := continuous_const
  weight_nonneg _ := zero_le_one
  weight_mass_pos := by
    rw [integral_const, smul_eq_mul, mul_one, measureReal_def,
      comap_subtype_coe_apply measurableSet_Ioo, image_univ, Subtype.range_coe,
      ← measureReal_def, Real.volume_real_Ioo_of_le hab.le]
    exact sub_pos.mpr hab

variable (W : QuadratureWeight a b)

/-- The weight is integrable: a nonintegrable function has Bochner integral zero. -/
theorem integrable_weight : Integrable W.weight (Measure.comap Subtype.val (volume : Measure ℝ)) :=
  Integrable.of_integral_ne_zero W.weight_mass_pos.ne'

/-- The integral of `f` times the weight over the open interval. As with the Bochner integral,
this is defined to be zero when the product is not integrable. -/
noncomputable def weightedIntegral (f : ℝ → ℝ) : ℝ :=
  ∫ x : Ioo a b, f x * W.weight x ∂(Measure.comap Subtype.val (volume : Measure ℝ))

/-- If `w` agrees with the weight on the open interval, the weighted integral can be
written as a set integral using `w`, independently of its values outside the open interval. -/
theorem weightedIntegral_eq_setIntegral (f w : ℝ → ℝ) (hw : ∀ x : Ioo a b, w x = W.weight x) :
    W.weightedIntegral f = ∫ x in Ioo a b, f x * w x := by
  rw [← integral_subtype_comap measurableSet_Ioo (fun x ↦ f x * w x)]
  unfold weightedIntegral
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ congrArg (f x * ·) (hw x).symm)

/-- A function continuous on the closed interval is integrable against the weight:
its restriction to the open interval is measurable and bounded, even when the weight is not. -/
theorem integrable_mul_weight_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    Integrable (fun x : Ioo a b ↦ f x * W.weight x)
      (Measure.comap Subtype.val (volume : Measure ℝ)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hf.norm
  have hcont : Continuous (fun x : Ioo a b ↦ f x) :=
    continuousOn_iff_continuous_domRestrict.mp (hf.mono Ioo_subset_Icc_self)
  exact W.integrable_weight.bdd_mul hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ hC (mem_image_of_mem _ (Ioo_subset_Icc_self x.property)))

/-- Every real polynomial is integrable against the weight on the open interval. -/
theorem integrable_eval_mul_weight (p : Polynomial ℝ) :
    Integrable (fun x : Ioo a b ↦ p.eval (x : ℝ) * W.weight x)
      (Measure.comap Subtype.val (volume : Measure ℝ)) :=
  W.integrable_mul_weight_of_continuousOn p.continuousOn

end QuadratureWeight

/-- An `n`-node quadrature formula on `[a, b]`, usable with any `QuadratureWeight a b`.
Nodes may include the endpoints, and neither node distinctness nor coefficient positivity
is required. -/
structure QuadratureRule (a b : ℝ) (n : ℕ) where
  /-- The evaluation nodes. -/
  node : Fin n → ℝ
  /-- All nodes lie in the closed interval. -/
  node_mem (i : Fin n) : node i ∈ Icc a b
  /-- The real quadrature coefficients. -/
  coeff : Fin n → ℝ

namespace QuadratureRule

variable {a b : ℝ} {n : ℕ} (Q : QuadratureRule a b n)

/-- The finite weighted sum of the values of `f` at the quadrature nodes. -/
noncomputable def eval (f : ℝ → ℝ) : ℝ :=
  ∑ i, Q.coeff i * f (Q.node i)

variable (W : QuadratureWeight a b)

/-- The rule agrees with the integral for weight `W` on all real polynomials of degree at most `m`.
-/
def ExactUpTo (m : ℕ) : Prop :=
  ∀ p : Polynomial ℝ, p.natDegree ≤ m → Q.eval p.eval = W.weightedIntegral p.eval

/-- A quadrature rule is exact through degree `m` for weight `W` if and only if its moments of
orders `0` through `m` agree with the corresponding weighted integrals of `x ^ k`. -/
theorem exactUpTo_iff_moments {m : ℕ} : Q.ExactUpTo W m ↔
    ∀ k ≤ m, Q.eval (fun x ↦ x ^ k) = W.weightedIntegral (fun x ↦ x ^ k) := by
  constructor
  · intro h k hk
    simpa only [Polynomial.eval_X_pow] using
      h ((Polynomial.X : Polynomial ℝ) ^ k) ((Polynomial.natDegree_X_pow k).trans_le hk)
  · intro h p hp
    let s := Finset.range (m + 1)
    have hexpand (x : ℝ) : p.eval x = ∑ k ∈ s, p.coeff k * x ^ k :=
      Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp) x
    calc
      Q.eval p.eval = ∑ k ∈ s, p.coeff k * Q.eval (fun x ↦ x ^ k) := by
        simp only [hexpand, eval, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ mul_left_comm _ _ _
      _ = ∑ k ∈ s, p.coeff k * W.weightedIntegral (fun x ↦ x ^ k) := by
        exact Finset.sum_congr rfl fun k hk ↦ congrArg (p.coeff k * ·)
          (h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
      _ = W.weightedIntegral p.eval := by
        simp only [hexpand, QuadratureWeight.weightedIntegral, Finset.sum_mul, mul_assoc]
        rw [integral_finsetSum]
        · simp only [integral_const_mul]
        · intro k _
          have hk := W.integrable_mul_weight_of_continuousOn (continuous_id.pow k).continuousOn
          exact hk.const_mul _

end QuadratureRule
end MetaMathlibExt
