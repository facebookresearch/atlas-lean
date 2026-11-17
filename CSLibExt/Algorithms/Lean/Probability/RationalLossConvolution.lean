/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Algebra.MonoidAlgebra.Defs

@[expose] public section

/-!
# Exact rational convolution of finite loss laws

A normalized finite rational loss law (`RationalLossLaw`, finitely supported
rational masses on `Nat`) convolves exactly by grouping products of masses
at loss sums (`convWeights`, `convLaw`), and decodes to the native `PMF` by
casting masses to `ENNReal` (`decode`). The endpoint
`decode_convLaw_eq_bind_map` says decoding a convolution is the independent
sum: `PMF.bind` over the first law of `PMF.map (a + .)` over the second.
-/

namespace Cslib.Algorithms.Lean.Probability.RationalLossConvolution

/-- A normalized finite rational loss law: finitely supported rational
masses on nonnegative integer losses, pointwise nonnegative, total mass 1.
The Finsupp representation consolidates duplicate support entries. -/
structure RationalLossLaw where
  /-- Finite-support rational masses on losses. -/
  weights : ℕ →₀ ℚ
  /-- Every loss mass is nonnegative. -/
  nonneg : ∀ n, 0 ≤ weights n
  /-- Total rational mass is 1. -/
  normalized : weights.sum (fun _ q => q) = 1

/-- Exact rational convolution of finite mass functions: the mass at a
total loss is the finite sum of products of masses at summand losses,
grouped by Finsupp.single at a + b. -/
noncomputable def convWeights (w1 w2 : ℕ →₀ ℚ) : ℕ →₀ ℚ :=
  w1.sum fun a x => w2.sum fun b y => Finsupp.single (a + b) (x * y)

private theorem finsupp_sum_bridge (f : ℕ →₀ ℚ) (g : ℕ → ℚ → ℚ) :
    f.sum g = ∑ a ∈ f.support, g a (f a) := rfl

private theorem single_apply_eq (a b n : ℕ) (v : ℚ) :
    Finsupp.single (a + b) v n = if n = a + b then v else 0 := by
  rw [Finsupp.single_apply]
  by_cases h : a + b = n
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem convWeights_apply (w1 w2 : ℕ →₀ ℚ) (n : ℕ) :
    convWeights w1 w2 n
      = ∑ a ∈ w1.support, ∑ b ∈ w2.support,
        if n = a + b then w1 a * w2 b else 0 := by
  unfold convWeights
  simp only [Finsupp.sum_apply, finsupp_sum_bridge, single_apply_eq]

private theorem sum_sum_id (f : ℕ →₀ ℚ) (g : ℕ → ℚ → ℕ →₀ ℚ) :
    (f.sum g).sum (fun _ q => q)
      = f.sum fun a x => (g a x).sum (fun _ q => q) :=
  Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)

private theorem single_sum_id (c : ℕ) (v : ℚ) :
    (Finsupp.single c v).sum (fun _ q => q) = v :=
  Finsupp.sum_single_index rfl

private theorem cast_nonneg (L : RationalLossLaw) (a : ℕ) :
    0 ≤ ((L.weights a : ℚ) : ℝ) :=
  Rat.cast_nonneg.mpr (L.nonneg a)

private theorem finsupp_sum_id_eq (w : ℕ →₀ ℚ) :
    w.sum (fun _ q => q) = ∑ n ∈ w.support, w n := rfl

private theorem ite_mul_nonneg (L1 L2 : RationalLossLaw) (a b n : ℕ) :
    0 ≤ (if n = a + b then ((L1.weights a : ℚ) : ℝ) * ((L2.weights b : ℚ) : ℝ)
      else 0) := by
  split_ifs with h
  · exact mul_nonneg (cast_nonneg L1 a) (cast_nonneg L2 b)
  · exact le_rfl

theorem convWeights_nonneg (L1 L2 : RationalLossLaw) (n : ℕ) :
    0 ≤ convWeights L1.weights L2.weights n := by
  rw [convWeights_apply]
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split_ifs with h
  · exact mul_nonneg (L1.nonneg a) (L2.nonneg b)
  · exact le_rfl

theorem convWeights_normalized (L1 L2 : RationalLossLaw) :
    (convWeights L1.weights L2.weights).sum (fun _ q => q) = 1 := by
  unfold convWeights
  simp only [sum_sum_id, single_sum_id]
  have h2 : ∀ x : ℚ, L2.weights.sum (fun _ y => x * y) = x := by
    intro x
    rw [← Finsupp.mul_sum, L2.normalized, mul_one]
  simp only [h2]
  exact L1.normalized

theorem convWeights_eq_addMonoidAlgebra_mul (w1 w2 : ℕ →₀ ℚ) :
    convWeights w1 w2
      = (AddMonoidAlgebra.ofCoeff w1 * AddMonoidAlgebra.ofCoeff w2).coeff := by
  ext n
  rw [convWeights_apply, AddMonoidAlgebra.coeff_mul]
  simp only [finsupp_sum_bridge]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a + b = n
  · rw [ite_eq_left h.symm, ite_eq_left h]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

/-- Convolution of two normalized rational loss laws, as a normalized
rational loss law. -/
noncomputable def convLaw (L1 L2 : RationalLossLaw) : RationalLossLaw where
  weights := convWeights L1.weights L2.weights
  nonneg := convWeights_nonneg L1 L2
  normalized := convWeights_normalized L1 L2

theorem decode_sum_eq_one (L : RationalLossLaw) :
    ∑ n ∈ L.weights.support,
      ENNReal.ofReal ((L.weights n : ℚ) : ℝ) = 1 := by
  have hreal : (∑ n ∈ L.weights.support, ((L.weights n : ℚ) : ℝ)) = 1 := by
    have h : ((L.weights.sum (fun _ q => q) : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      rw [L.normalized]
    rw [finsupp_sum_id_eq, Rat.cast_sum, Rat.cast_one] at h
    exact h
  have hof : ENNReal.ofReal (∑ n ∈ L.weights.support, ((L.weights n : ℚ) : ℝ))
      = ∑ n ∈ L.weights.support, ENNReal.ofReal ((L.weights n : ℚ) : ℝ) :=
    ENNReal.ofReal_sum_of_nonneg (fun n _ => cast_nonneg L n)
  rw [← hof, hreal, ENNReal.ofReal_one]

theorem decode_apply_eq_zero_of_not_mem (L : RationalLossLaw) (a : ℕ)
    (ha : a ∉ L.weights.support) :
    ENNReal.ofReal ((L.weights a : ℚ) : ℝ) = 0 := by
  have h0 : L.weights a = 0 := Finsupp.notMem_support_iff.mp ha
  simp [h0]

/-- Decode a rational loss law to the native PMF on Nat by casting each
rational mass to ENNReal. -/
noncomputable def decode (L : RationalLossLaw) : PMF ℕ :=
  PMF.ofFinset (fun n => ENNReal.ofReal ((L.weights n : ℚ) : ℝ))
    L.weights.support (decode_sum_eq_one L)
    (fun a ha => decode_apply_eq_zero_of_not_mem L a ha)

@[simp] theorem decode_apply (L : RationalLossLaw) (n : ℕ) :
    decode L n = ENNReal.ofReal ((L.weights n : ℚ) : ℝ) := by
  unfold decode
  rw [PMF.ofFinset_apply]

@[simp] theorem convLaw_weights (L1 L2 : RationalLossLaw) :
    (convLaw L1 L2).weights = convWeights L1.weights L2.weights := rfl

private theorem inner_tsum_eq (L2 : RationalLossLaw) (a n : ℕ) :
    (∑' b, if n = a + b then ENNReal.ofReal ((L2.weights b : ℚ) : ℝ)
      else 0)
      = ∑ b ∈ L2.weights.support, if n = a + b then
        ENNReal.ofReal ((L2.weights b : ℚ) : ℝ) else 0 := by
  apply tsum_eq_sum
  intro b hb
  change (if n = a + b then ENNReal.ofReal ((L2.weights b : ℚ) : ℝ)
    else 0) = 0
  split_ifs with h
  · exact decode_apply_eq_zero_of_not_mem L2 b hb
  · rfl

private theorem outer_tsum_eq (L1 L2 : RationalLossLaw) (n : ℕ) :
    (∑' a, ENNReal.ofReal ((L1.weights a : ℚ) : ℝ)
        * (∑ b ∈ L2.weights.support, if n = a + b then
          ENNReal.ofReal ((L2.weights b : ℚ) : ℝ) else 0))
      = ∑ a ∈ L1.weights.support, ENNReal.ofReal ((L1.weights a : ℚ) : ℝ)
        * (∑ b ∈ L2.weights.support, if n = a + b then
          ENNReal.ofReal ((L2.weights b : ℚ) : ℝ) else 0) := by
  apply tsum_eq_sum
  intro a ha
  change ENNReal.ofReal ((L1.weights a : ℚ) : ℝ) * _ = 0
  rw [decode_apply_eq_zero_of_not_mem L1 a ha, zero_mul]

private theorem ofReal_double_sum (L1 L2 : RationalLossLaw) (n : ℕ) :
    ENNReal.ofReal (((∑ a ∈ L1.weights.support, ∑ b ∈ L2.weights.support,
        if n = a + b then L1.weights a * L2.weights b else 0 : ℚ)) : ℝ)
      = ∑ a ∈ L1.weights.support, ∑ b ∈ L2.weights.support,
        if n = a + b then ENNReal.ofReal ((L1.weights a : ℚ) : ℝ)
          * ENNReal.ofReal ((L2.weights b : ℚ) : ℝ) else 0 := by
  have hcast : (((∑ a ∈ L1.weights.support, ∑ b ∈ L2.weights.support,
      if n = a + b then L1.weights a * L2.weights b else 0 : ℚ)) : ℝ)
      = ∑ a ∈ L1.weights.support, ∑ b ∈ L2.weights.support,
        if n = a + b then ((L1.weights a : ℚ) : ℝ)
          * ((L2.weights b : ℚ) : ℝ) else 0 := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : n = a + b
    · rw [ite_eq_left h, ite_eq_left h, Rat.cast_mul]
    · rw [ite_eq_right h, ite_eq_right h, Rat.cast_zero]
  rw [hcast]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun a _ => Finset.sum_nonneg
      fun b _ => ite_mul_nonneg L1 L2 a b n)]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun b _ => ite_mul_nonneg L1 L2 a b n)]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : n = a + b
  · rw [ite_eq_left h, ite_eq_left h,
      ENNReal.ofReal_mul (cast_nonneg L1 a)]
  · rw [ite_eq_right h, ite_eq_right h, ENNReal.ofReal_zero]

theorem decode_convLaw_eq_bind_map (L1 L2 : RationalLossLaw) :
    decode (convLaw L1 L2)
      = (decode L1).bind (fun a => (decode L2).map (a + ·)) := by
  apply PMF.ext
  intro n
  have hLHS : decode (convLaw L1 L2) n
      = ∑ a ∈ L1.weights.support, ∑ b ∈ L2.weights.support,
        if n = a + b then ENNReal.ofReal ((L1.weights a : ℚ) : ℝ)
          * ENNReal.ofReal ((L2.weights b : ℚ) : ℝ) else 0 := by
    rw [decode_apply, convLaw_weights, convWeights_apply,
      ofReal_double_sum]
  have hRHS : ((decode L1).bind (fun a => (decode L2).map (a + ·))) n
      = ∑ a ∈ L1.weights.support, ∑ b ∈ L2.weights.support,
        if n = a + b then ENNReal.ofReal ((L1.weights a : ℚ) : ℝ)
          * ENNReal.ofReal ((L2.weights b : ℚ) : ℝ) else 0 := by
    rw [PMF.bind_apply]
    simp only [PMF.map_apply, decode_apply, inner_tsum_eq, outer_tsum_eq]
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  exact hLHS.trans hRHS.symm

end Cslib.Algorithms.Lean.Probability.RationalLossConvolution
