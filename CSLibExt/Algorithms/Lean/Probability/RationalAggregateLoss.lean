/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Probability.RationalLossConvolution

@[expose] public section

/-!
# Finite count-mixture (aggregate loss) law

The deterministic-count law `iterLaw S n` is the `n`-fold convolution of a
rational severity law `S` starting at the unit point mass at `0`, and
`aggregateLaw C S` mixes these with a normalized rational count law `C`.
The endpoint `decode_aggregateLaw_eq_bind` says decoding the mixture is the
independent random-sum law: `PMF.bind` over `decode C` of the native
`n`-fold sum of i.i.d. `decode S` draws.
-/

open Cslib.Algorithms.Lean.Probability.RationalLossConvolution

namespace Cslib.Algorithms.Lean.Probability.RationalAggregateLoss

private theorem finsupp_sum_bridge (f : ℕ →₀ ℚ) (g : ℕ → ℚ → ℚ) :
    f.sum g = ∑ a ∈ f.support, g a (f a) := rfl

theorem unit_weights_nonneg (n : ℕ) :
    0 ≤ Finsupp.single (0 : ℕ) (1 : ℚ) n := by
  simp only [Finsupp.single_apply]
  split_ifs <;> norm_num

theorem unit_weights_normalized :
    (Finsupp.single (0 : ℕ) (1 : ℚ)).sum (fun _ q => q) = 1 := by
  exact Finsupp.sum_single_index rfl

/-- The unit point mass at loss 0, as a rational loss law. -/
noncomputable def unitLaw : RationalLossLaw where
  weights := Finsupp.single 0 1
  nonneg := unit_weights_nonneg
  normalized := unit_weights_normalized

/-- The weights of the unit law are the point mass at 0. -/
@[simp] theorem unitLaw_weights :
    unitLaw.weights = Finsupp.single 0 1 := rfl

/-- The deterministic-count law: sum of `n` i.i.d. severities `S`, by
iterated convolution starting at the unit point mass at 0. -/
noncomputable def iterLaw (S : RationalLossLaw) : ℕ → RationalLossLaw
  | 0 => unitLaw
  | n + 1 => convLaw (iterLaw S n) S

/-- The deterministic-count law at count 0 is the unit law. -/
@[simp] theorem iterLaw_zero (S : RationalLossLaw) :
    iterLaw S 0 = unitLaw := rfl

/-- The deterministic-count law at count `n + 1` convolves the count-`n`
law with the severity law. -/
@[simp] theorem iterLaw_succ (S : RationalLossLaw) (n : ℕ) :
    iterLaw S (n + 1) = convLaw (iterLaw S n) S := rfl

private theorem smul_apply_eq (q : ℚ) (w : ℕ →₀ ℚ) (m : ℕ) :
    (q • w) m = q * w m := by
  rw [Finsupp.smul_apply, smul_eq_mul]

private theorem mixture_apply (C S : RationalLossLaw) (m : ℕ) :
    (C.weights.sum fun k q => q • (iterLaw S k).weights) m
      = ∑ k ∈ C.weights.support, C.weights k * (iterLaw S k).weights m := by
  rw [Finsupp.sum_apply]
  simp only [smul_apply_eq, finsupp_sum_bridge]

private theorem sum_sum_id (f : ℕ →₀ ℚ) (g : ℕ → ℚ → ℕ →₀ ℚ) :
    (f.sum g).sum (fun _ q => q)
      = f.sum fun a x => (g a x).sum (fun _ q => q) :=
  Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)

private theorem smul_sum_id (q : ℚ) (w : ℕ →₀ ℚ) :
    (q • w).sum (fun _ q => q) = q * w.sum (fun _ q => q) := by
  rw [Finsupp.sum_smul_index (fun _ => rfl), Finsupp.mul_sum]

theorem aggregate_weights_nonneg (C S : RationalLossLaw) (n : ℕ) :
    0 ≤ (C.weights.sum fun k q => q • (iterLaw S k).weights) n := by
  rw [mixture_apply]
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (C.nonneg k) ((iterLaw S k).nonneg n)

theorem aggregate_weights_normalized (C S : RationalLossLaw) :
    (C.weights.sum fun k q => q • (iterLaw S k).weights).sum
      (fun _ q => q) = 1 := by
  rw [sum_sum_id]
  have hiter : ∀ k : ℕ, (iterLaw S k).weights.sum (fun _ q => q) = 1 :=
    fun k => (iterLaw S k).normalized
  simp only [smul_sum_id, hiter, mul_one]
  exact C.normalized

/-- The finite count-mixture (aggregate loss) law: mix the
deterministic-count laws `iterLaw S k` with the rational count masses
of `C`. -/
noncomputable def aggregateLaw (C S : RationalLossLaw) : RationalLossLaw where
  weights := C.weights.sum fun k q => q • (iterLaw S k).weights
  nonneg := aggregate_weights_nonneg C S
  normalized := aggregate_weights_normalized C S

/-- The weights of the aggregate law mix the deterministic-count laws
with the count masses. -/
@[simp] theorem aggregateLaw_weights (C S : RationalLossLaw) :
    (aggregateLaw C S).weights
      = C.weights.sum fun k q => q • (iterLaw S k).weights := rfl

/-- Pointwise evaluation of the aggregate law weights: the mass at `m`
is the count-weighted mixture of the deterministic-count masses at `m`. -/
@[simp] theorem aggregateLaw_weights_apply (C S : RationalLossLaw) (m : ℕ) :
    (aggregateLaw C S).weights m
      = C.weights.sum (fun k q => q * (iterLaw S k).weights m) := by
  rw [aggregateLaw_weights, Finsupp.sum_apply]
  simp only [smul_apply_eq]

private theorem cast_nonneg (L : RationalLossLaw) (a : ℕ) :
    0 ≤ ((L.weights a : ℚ) : ℝ) :=
  Rat.cast_nonneg.mpr (L.nonneg a)

/-- Decoding the unit law is the point mass at 0. -/
@[simp] theorem decode_unitLaw : decode unitLaw = PMF.pure 0 := by
  apply PMF.ext
  intro m
  have hsingle : unitLaw.weights m = Finsupp.single (0 : ℕ) (1 : ℚ) m := rfl
  rw [decode_apply, hsingle, Finsupp.single_apply, PMF.pure_apply]
  by_cases h : m = 0
  · subst h
    simp
  · have h' : ¬ (0 : ℕ) = m := fun hh => h hh.symm
    simp [h, h']

/-- Decoding the deterministic-count law `iterLaw S n` is the native
`n`-fold independent sum of `decode S` draws: iterating
`q ↦ q.bind (fun a => (decode S).map (a + ·))` `n` times from `PMF.pure 0`. -/
theorem decode_iterLaw_eq_iterate (S : RationalLossLaw) (n : ℕ) :
    decode (iterLaw S n)
      = (fun q : PMF ℕ => q.bind (fun a => (decode S).map (a + ·)))^[n]
        (PMF.pure 0) := by
  induction n with
  | zero =>
    rw [iterLaw_zero, decode_unitLaw, Function.iterate_zero_apply]
  | succ n ih =>
    rw [iterLaw_succ, decode_convLaw_eq_bind_map, ih]
    exact (Function.iterate_succ_apply'
      (fun q : PMF ℕ => q.bind (fun a => (decode S).map (a + ·))) n
      (PMF.pure 0)).symm

private theorem ofReal_mixture_sum (C S : RationalLossLaw) (m : ℕ) :
    ENNReal.ofReal (((∑ k ∈ C.weights.support,
        C.weights k * (iterLaw S k).weights m : ℚ)) : ℝ)
      = ∑ k ∈ C.weights.support, ENNReal.ofReal ((C.weights k : ℚ) : ℝ)
        * ENNReal.ofReal (((iterLaw S k).weights m : ℚ) : ℝ) := by
  have hcast : (((∑ k ∈ C.weights.support,
      C.weights k * (iterLaw S k).weights m : ℚ)) : ℝ)
      = ∑ k ∈ C.weights.support, ((C.weights k : ℚ) : ℝ)
        * (((iterLaw S k).weights m : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Rat.cast_mul]
  rw [hcast]
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ =>
    mul_nonneg (cast_nonneg C k) (cast_nonneg (iterLaw S k) m))]
  apply Finset.sum_congr rfl
  intro k _
  rw [ENNReal.ofReal_mul (cast_nonneg C k)]

private theorem bind_tsum_eq (C S : RationalLossLaw) (m : ℕ) :
    (∑' n, ENNReal.ofReal ((C.weights n : ℚ) : ℝ)
        * ENNReal.ofReal (((iterLaw S n).weights m : ℚ) : ℝ))
      = ∑ n ∈ C.weights.support, ENNReal.ofReal ((C.weights n : ℚ) : ℝ)
        * ENNReal.ofReal (((iterLaw S n).weights m : ℚ) : ℝ) := by
  apply tsum_eq_sum
  intro n hn
  change ENNReal.ofReal ((C.weights n : ℚ) : ℝ) * _ = 0
  rw [decode_apply_eq_zero_of_not_mem C n hn, zero_mul]

theorem decode_aggregateLaw_eq_bind (C S : RationalLossLaw) :
    decode (aggregateLaw C S)
      = (decode C).bind (fun n =>
          (fun q : PMF ℕ => q.bind (fun a => (decode S).map (a + ·)))^[n]
            (PMF.pure 0)) := by
  apply PMF.ext
  intro m
  have hLHS : decode (aggregateLaw C S) m
      = ∑ k ∈ C.weights.support, ENNReal.ofReal ((C.weights k : ℚ) : ℝ)
        * ENNReal.ofReal (((iterLaw S k).weights m : ℚ) : ℝ) := by
    rw [decode_apply, aggregateLaw_weights, mixture_apply,
      ofReal_mixture_sum]
  have hRHS : ((decode C).bind (fun n =>
        (fun q : PMF ℕ => q.bind (fun a => (decode S).map (a + ·)))^[n]
          (PMF.pure 0))) m
      = ∑ k ∈ C.weights.support, ENNReal.ofReal ((C.weights k : ℚ) : ℝ)
        * ENNReal.ofReal (((iterLaw S k).weights m : ℚ) : ℝ) := by
    rw [PMF.bind_apply]
    simp only [← decode_iterLaw_eq_iterate, decode_apply, bind_tsum_eq]
  exact hLHS.trans hRHS.symm

end Cslib.Algorithms.Lean.Probability.RationalAggregateLoss
