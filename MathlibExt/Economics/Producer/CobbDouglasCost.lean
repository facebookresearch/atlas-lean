/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.MeanInequalities

/-!
# The Cobb–Douglas cost function

For the constant-returns Cobb–Douglas technology `A ∏ᵢ xᵢ ^ aᵢ` with `A > 0`, `aᵢ > 0`,
`∑ᵢ aᵢ = 1`, input prices `wᵢ > 0` and target output `q ≥ 0`, the least cost of producing at
least `q` with nonnegative inputs is `(q / A) ∏ᵢ (wᵢ / aᵢ) ^ aᵢ`, attained at the conditional
factor demands `xᵢ = (aᵢ / wᵢ) · cost`. The lower bound is weighted AM–GM
(`Real.geom_mean_le_arith_mean_weighted`); no first-order conditions are used. Technologies
with `∑ᵢ aᵢ ≠ 1` have a different formula and are not covered.

## Main results

* `Economics.Producer.cobbDouglasCost_le_dotProduct`
* `Economics.Producer.cobbDouglas_cobbDouglasDemand`
* `Economics.Producer.isLeast_cobbDouglasCost`

## References

* H. R. Varian, *Microeconomic Analysis*, 3rd ed., Norton (1992), Chapter 4.

Atlas roadmap target EC07.T01.
-/

@[expose] public section

namespace Economics.Producer

/-- Cobb–Douglas production function `A ∏ᵢ xᵢ ^ aᵢ` (real powers). -/
noncomputable def cobbDouglas {ι : Type*} [Fintype ι] (A : ℝ) (a x : ι → ℝ) : ℝ :=
  A * ∏ i, x i ^ a i

/-- The stated Cobb–Douglas cost formula `(q / A) ∏ᵢ (wᵢ / aᵢ) ^ aᵢ`. -/
noncomputable def cobbDouglasCost {ι : Type*} [Fintype ι] (A : ℝ) (a w : ι → ℝ) (q : ℝ) : ℝ :=
  q / A * ∏ i, (w i / a i) ^ a i

/-- Conditional factor demand `xᵢ* = (aᵢ / wᵢ) · c(w, q)`. -/
noncomputable def cobbDouglasDemand {ι : Type*} [Fintype ι] (A : ℝ) (a w : ι → ℝ) (q : ℝ) :
    ι → ℝ :=
  fun i => a i / w i * cobbDouglasCost A a w q

/-- Every nonnegative input bundle producing at least `q` costs at least the stated formula. -/
theorem cobbDouglasCost_le_dotProduct {ι : Type*} [Fintype ι] {A q : ℝ} {a w x : ι → ℝ}
    (hA : 0 < A) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1) (hw : ∀ i, 0 < w i)
    (hx : ∀ i, 0 ≤ x i) (hout : q ≤ cobbDouglas A a x) :
    cobbDouglasCost A a w q ≤ w ⬝ᵥ x := by
  have hdot : w ⬝ᵥ x = ∑ i, w i * x i := by simp only [dotProduct]
  have hpt : ∀ i, a i * (w i * x i / a i) = w i * x i := by
    intro i
    have hai : a i ≠ 0 := ne_of_gt (ha i)
    field_simp
  have hsum_eq : (∑ i, a i * (w i * x i / a i)) = ∑ i, w i * x i :=
    Finset.sum_congr rfl (fun i _ => hpt i)
  have hfactor : ∀ i, (w i * x i / a i) ^ a i = (w i / a i) ^ a i * x i ^ a i := by
    intro i
    have heq : w i * x i / a i = (w i / a i) * x i := by ring
    rw [heq]
    exact Real.mul_rpow (le_of_lt (div_pos (hw i) (ha i))) (hx i)
  have hprod_eq : (∏ i, (w i * x i / a i) ^ a i)
      = (∏ i, (w i / a i) ^ a i) * ∏ i, x i ^ a i := by
    simp only [hfactor, Finset.prod_mul_distrib]
  have hP_nonneg : 0 ≤ ∏ i, (w i / a i) ^ a i :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (le_of_lt (div_pos (hw i) (ha i))) _)
  have hqA' : q / A ≤ ∏ i, x i ^ a i := by
    apply (div_le_iff₀ hA).mpr
    have h := hout
    unfold cobbDouglas at h
    rwa [mul_comm A] at h
  have hamgm : (∏ i, (w i * x i / a i) ^ a i) ≤ ∑ i, a i * (w i * x i / a i) :=
    Real.geom_mean_le_arith_mean_weighted Finset.univ a (fun i => w i * x i / a i)
      (fun i _ => le_of_lt (ha i)) hsum
      (fun i _ => div_nonneg (mul_nonneg (le_of_lt (hw i)) (hx i)) (le_of_lt (ha i)))
  unfold cobbDouglasCost
  calc q / A * (∏ i, (w i / a i) ^ a i)
      ≤ (∏ i, x i ^ a i) * ∏ i, (w i / a i) ^ a i :=
        mul_le_mul_of_nonneg_right hqA' hP_nonneg
    _ = (∏ i, (w i / a i) ^ a i) * ∏ i, x i ^ a i := mul_comm _ _
    _ = ∏ i, (w i * x i / a i) ^ a i := hprod_eq.symm
    _ ≤ ∑ i, a i * (w i * x i / a i) := hamgm
    _ = ∑ i, w i * x i := hsum_eq
    _ = w ⬝ᵥ x := hdot.symm

/-- The conditional factor demands are nonnegative. -/
theorem cobbDouglasDemand_nonneg {ι : Type*} [Fintype ι] {A q : ℝ} {a w : ι → ℝ}
    (hA : 0 < A) (ha : ∀ i, 0 < a i) (hw : ∀ i, 0 < w i) (hq : 0 ≤ q) (i : ι) :
    0 ≤ cobbDouglasDemand A a w q i := by
  show 0 ≤ a i / w i * cobbDouglasCost A a w q
  refine mul_nonneg (le_of_lt (div_pos (ha i) (hw i))) ?_
  show 0 ≤ q / A * ∏ j, (w j / a j) ^ a j
  refine mul_nonneg (div_nonneg hq (le_of_lt hA)) ?_
  exact Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (le_of_lt (div_pos (hw j) (ha j))) _)

/-- The conditional factor demands produce exactly the target output. -/
theorem cobbDouglas_cobbDouglasDemand {ι : Type*} [Fintype ι] {A q : ℝ} {a w : ι → ℝ}
    (hA : 0 < A) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1) (hw : ∀ i, 0 < w i)
    (hq : 0 ≤ q) :
    cobbDouglas A a (cobbDouglasDemand A a w q) = q := by
  have hC : 0 ≤ cobbDouglasCost A a w q := by
    show 0 ≤ q / A * ∏ j, (w j / a j) ^ a j
    refine mul_nonneg (div_nonneg hq (le_of_lt hA)) ?_
    exact Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (le_of_lt (div_pos (hw j) (ha j))) _)
  have hsplit : ∀ i, (cobbDouglasDemand A a w q i) ^ a i
      = (a i / w i) ^ a i * (cobbDouglasCost A a w q) ^ a i := by
    intro i
    have hdi : cobbDouglasDemand A a w q i
        = (a i / w i) * cobbDouglasCost A a w q := rfl
    rw [hdi]
    exact Real.mul_rpow (le_of_lt (div_pos (ha i) (hw i))) hC
  have hCpow : (∏ i, (cobbDouglasCost A a w q) ^ a i) = cobbDouglasCost A a w q := by
    have h := Real.rpow_sum_of_nonneg hC (s := Finset.univ) (f := a)
      (fun i _ => le_of_lt (ha i))
    rw [hsum, Real.rpow_one] at h
    exact h.symm
  have hprod : ∏ i, (cobbDouglasDemand A a w q i) ^ a i
      = (∏ i, (a i / w i) ^ a i) * cobbDouglasCost A a w q := by
    simp only [hsplit, Finset.prod_mul_distrib, hCpow]
  have hQP : (∏ i, (a i / w i) ^ a i) * (∏ i, (w i / a i) ^ a i) = 1 := by
    have e : ∀ i, (a i / w i) ^ a i * (w i / a i) ^ a i = 1 := by
      intro i
      rw [← Real.mul_rpow (le_of_lt (div_pos (ha i) (hw i)))
        (le_of_lt (div_pos (hw i) (ha i)))]
      have h1 : (a i / w i) * (w i / a i) = 1 := by
        have hwi : w i ≠ 0 := ne_of_gt (hw i)
        have hai : a i ≠ 0 := ne_of_gt (ha i)
        field_simp
      rw [h1, Real.one_rpow]
    rw [← Finset.prod_mul_distrib]
    simp only [e, Finset.prod_const_one]
  unfold cobbDouglas
  rw [hprod]
  unfold cobbDouglasCost
  have hA' : A ≠ 0 := ne_of_gt hA
  calc A * ((∏ i, (a i / w i) ^ a i) * (q / A * ∏ i, (w i / a i) ^ a i))
      = ((∏ i, (a i / w i) ^ a i) * ∏ i, (w i / a i) ^ a i) * (A * (q / A)) := by ring
    _ = 1 * (A * (q / A)) := by rw [hQP]
    _ = q := by field_simp

/-- The conditional factor demands cost exactly the stated formula. -/
theorem dotProduct_cobbDouglasDemand {ι : Type*} [Fintype ι] {A q : ℝ} {a w : ι → ℝ}
    (hsum : ∑ i, a i = 1) (hw : ∀ i, 0 < w i) :
    w ⬝ᵥ cobbDouglasDemand A a w q = cobbDouglasCost A a w q := by
  have hdot : w ⬝ᵥ cobbDouglasDemand A a w q
      = ∑ i, w i * cobbDouglasDemand A a w q i := by simp only [dotProduct]
  have e : ∀ i, w i * cobbDouglasDemand A a w q i
      = a i * cobbDouglasCost A a w q := by
    intro i
    have hdi : cobbDouglasDemand A a w q i
        = (a i / w i) * cobbDouglasCost A a w q := rfl
    rw [hdi]
    have hwi : w i ≠ 0 := ne_of_gt (hw i)
    field_simp
  rw [hdot]
  simp only [e, ← Finset.sum_mul, hsum, one_mul]

/-- **Cobb–Douglas cost formula.** The stated formula is the least cost of producing at least
`q` with nonnegative inputs. -/
theorem isLeast_cobbDouglasCost {ι : Type*} [Fintype ι] {A q : ℝ} {a w : ι → ℝ}
    (hA : 0 < A) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1) (hw : ∀ i, 0 < w i)
    (hq : 0 ≤ q) :
    IsLeast {c | ∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ q ≤ cobbDouglas A a x ∧ c = w ⬝ᵥ x}
      (cobbDouglasCost A a w q) := by
  refine ⟨?_, ?_⟩
  · exact ⟨cobbDouglasDemand A a w q, cobbDouglasDemand_nonneg hA ha hw hq,
      le_of_eq (cobbDouglas_cobbDouglasDemand hA ha hsum hw hq).symm,
      (dotProduct_cobbDouglasDemand hsum hw).symm⟩
  · intro c hc
    simp only [Set.mem_ofPred_eq] at hc
    obtain ⟨x, hx, hout, rfl⟩ := hc
    exact cobbDouglasCost_le_dotProduct hA ha hsum hw hx hout

end Economics.Producer
