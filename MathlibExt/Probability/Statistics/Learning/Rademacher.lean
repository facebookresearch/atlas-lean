/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Linarith

/-!
# Empirical Rademacher complexity of a finite set of vectors (frozen convention)

Coordinator freeze (L5-18 gate, discharged as this definitions file). For a finite set
`A : Finset (Fin n → ℝ)` of vectors (a function class evaluated on a sample of size `n`),

`empiricalRademacher A = 2⁻ⁿ ∑_{σ : Fin n → Bool} max_{a ∈ A} (1/n) ∑ᵢ σᵢ aᵢ`,

where the sign of `σ i` is `if σ i then 1 else -1`, the expectation over independent uniform
signs is the uniform average over all `2 ^ n` sign vectors (`(∑ σ, _) / 2 ^ n`), the
normalization `(n : ℝ)⁻¹` sits inside the maximum, and the maximum is one-sided
(`Finset.sup'`, no absolute value). The empty set has complexity `0` (the value of `{0}`).
These are the conventions of `massart_finite_class` and `rademacher_finite_class` in
`MathlibExt.Probability.LearningTheory.Rademacher(Bound)`: same sign encoding, same
`Finset.sup'`, same `/ 2 ^ n` average; their left sides are `n * empiricalRademacher A`
(general vectors) and `empiricalRademacher` of the `±1` image (Boolean classes), see
`empiricalRademacher_eq_sum_sup'_div` and `empiricalRademacher_image_sign`.

The Euclidean norm used by the Massart bound is written out as `Real.sqrt (∑ i, a i ^ 2)`;
the norm `‖a‖` of `a : Fin n → ℝ` in Mathlib is the sup norm and is not used.

Reserved for the follow-up slice (stated here as the freeze, not proved in this file): the
finite-class Massart lemma with explicit `1/n` normalization, for `A.Nonempty`,
`empiricalRademacher A ≤ A.sup' hA (fun v => Real.sqrt (∑ i, v i ^ 2)) *
  Real.sqrt (2 * Real.log A.card) / n`.
-/

@[expose] public section

open Finset

namespace ProbabilityTheory

/-- Empirical Rademacher complexity of a finite set `A` of vectors in `ℝⁿ`: the average over
all `2 ^ n` sign vectors `σ` of the largest normalized correlation
`(1/n) ∑ᵢ σᵢ aᵢ` over `a ∈ A` (one-sided, no absolute value). The empty set has
complexity `0`. -/
noncomputable def empiricalRademacher {n : ℕ} (A : Finset (Fin n → ℝ)) : ℝ :=
  if hA : A.Nonempty then
    (∑ σ : Fin n → Bool,
      A.sup' hA (fun a => (n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * a i)) / 2 ^ n
  else 0

private def signFlip (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun σ := fun i => !(σ i)
  invFun σ := fun i => !(σ i)
  left_inv σ := by funext i; change (!(!(σ i))) = σ i; cases σ i <;> rfl
  right_inv σ := by funext i; change (!(!(σ i))) = σ i; cases σ i <;> rfl

private theorem signFlip_apply (n : ℕ) (σ : Fin n → Bool) (i : Fin n) :
    signFlip n σ i = !(σ i) := rfl

private theorem sign_flip (b : Bool) :
    (if !b then (1 : ℝ) else -1) = -((if b then (1 : ℝ) else -1)) := by
  cases b <;> simp

private theorem sum_sign_mul_self_eq_zero (n : ℕ) (a : Fin n → ℝ) :
    ∑ σ : Fin n → Bool, ∑ i, (if σ i then (1 : ℝ) else -1) * a i = 0 := by
  have h : (∑ σ : Fin n → Bool, ∑ i, (if σ i then (1 : ℝ) else -1) * a i) =
      -∑ σ : Fin n → Bool, ∑ i, (if σ i then (1 : ℝ) else -1) * a i := by
    conv_lhs => rw [← Equiv.sum_comp (signFlip n) _]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [signFlip_apply, sign_flip, neg_mul]
  linarith

/-- Equation lemma for a nonempty set. -/
theorem empiricalRademacher_eq_sup' {n : ℕ} {A : Finset (Fin n → ℝ)} (hA : A.Nonempty) :
    empiricalRademacher A =
      (∑ σ : Fin n → Bool,
        A.sup' hA (fun a => (n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * a i)) / 2 ^ n := by
  unfold empiricalRademacher
  simp [hA]

/-- Equation lemma for the empty set: the zero-function convention. -/
theorem empiricalRademacher_empty {n : ℕ} :
    empiricalRademacher (∅ : Finset (Fin n → ℝ)) = 0 := by
  unfold empiricalRademacher
  simp

/-- Bridge to the unnormalized Massart form: the left side of `massart_finite_class`
divided by `n`. Holds for every `n`, including `n = 0` (both sides `0`). -/
theorem empiricalRademacher_eq_sum_sup'_div {n : ℕ} {A : Finset (Fin n → ℝ)}
    (hA : A.Nonempty) :
    empiricalRademacher A =
      (∑ σ : Fin n → Bool,
        A.sup' hA (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i)) / 2 ^ n / n := by
  have hc : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  rw [empiricalRademacher_eq_sup' hA]
  have per : ∀ σ : Fin n → Bool,
      A.sup' hA (fun a => (n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * a i) =
        (n : ℝ)⁻¹ * A.sup' hA (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i) := by
    intro σ
    exact (Finset.apply_sup'_eq_sup'_comp hA (fun x => (n : ℝ)⁻¹ * x)
      (fun x y => mul_max_of_nonneg x y hc)).symm
  have hsum : (∑ σ : Fin n → Bool,
        A.sup' hA (fun a => (n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * a i)) =
      (n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
        A.sup' hA (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i) := by
    rw [Finset.mul_sum _ _ _]
    exact Finset.sum_congr rfl (fun σ _ => per σ)
  rw [hsum, div_eq_mul_inv _ ((n : ℝ)), mul_div_assoc, mul_comm _ ((n : ℝ)⁻¹)]

/-- A single vector has complexity `0` (one-sided convention; the signs average out). -/
theorem empiricalRademacher_singleton {n : ℕ} (a : Fin n → ℝ) :
    empiricalRademacher ({a} : Finset (Fin n → ℝ)) = 0 := by
  rw [empiricalRademacher_eq_sum_sup'_div (Finset.singleton_nonempty a)]
  simp only [Finset.sup'_singleton, sum_sign_mul_self_eq_zero, zero_div]

theorem empiricalRademacher_nonneg {n : ℕ} (A : Finset (Fin n → ℝ)) :
    0 ≤ empiricalRademacher A := by
  by_cases hA : A.Nonempty
  · have hA' := hA
    obtain ⟨a, ha⟩ := hA
    rw [empiricalRademacher_eq_sum_sup'_div hA']
    apply div_nonneg _ (Nat.cast_nonneg n)
    apply div_nonneg _ (by positivity)
    rw [← sum_sign_mul_self_eq_zero n a]
    apply Finset.sum_le_sum
    intro σ _
    exact Finset.le_sup' (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i) ha
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA, empiricalRademacher_empty]

theorem empiricalRademacher_mono {n : ℕ} {A B : Finset (Fin n → ℝ)} (hAB : A ⊆ B) :
    empiricalRademacher A ≤ empiricalRademacher B := by
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · rw [empiricalRademacher_eq_sup' hA, empiricalRademacher_eq_sup' hB]
      rw [div_eq_mul_inv _ ((2 : ℝ) ^ n), div_eq_mul_inv _ ((2 : ℝ) ^ n)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.sup'_mono _ hAB hA
    · obtain ⟨a, ha⟩ := hA
      have hb := hAB ha
      rw [Finset.not_nonempty_iff_eq_empty.mp hB] at hb
      simp at hb
  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    rw [hAe, empiricalRademacher_empty]
    exact empiricalRademacher_nonneg B

/-- Reflection invariance: `-A` has the same complexity as `A`. -/
theorem empiricalRademacher_image_neg {n : ℕ} (A : Finset (Fin n → ℝ)) :
    empiricalRademacher (A.image fun a => -a) = empiricalRademacher A := by
  by_cases hA : A.Nonempty
  · have hAI : (A.image fun a => -a).Nonempty := hA.image _
    rw [empiricalRademacher_eq_sup' hAI, empiricalRademacher_eq_sup' hA]
    congr 1
    conv_lhs => rw [← Equiv.sum_comp (signFlip n) _]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [Finset.sup'_image]
    have hpt : ((fun b : Fin n → ℝ =>
          (n : ℝ)⁻¹ * ∑ i, (if signFlip n σ i then (1 : ℝ) else -1) * b i) ∘
        (fun a : Fin n → ℝ => -a)) =
        fun a : Fin n → ℝ => (n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * a i := by
      funext a
      simp only [Function.comp_apply, Pi.neg_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [signFlip_apply, sign_flip, neg_mul_neg]
    rw [hpt]
  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    rw [hAe]
    simp [Finset.image_empty, empiricalRademacher_empty]

private theorem empiricalRademacher_image_smul_of_nonneg {n : ℕ} (A : Finset (Fin n → ℝ))
    {c : ℝ} (hc : 0 ≤ c) :
    empiricalRademacher (A.image fun a => c • a) = c * empiricalRademacher A := by
  by_cases hA : A.Nonempty
  · have hAI : (A.image fun a => c • a).Nonempty := hA.image _
    rw [empiricalRademacher_eq_sup' hAI, empiricalRademacher_eq_sup' hA]
    have per : ∀ σ : Fin n → Bool,
        (A.image fun a => c • a).sup' hAI
            (fun b => (n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * b i) =
          c * A.sup' hA (fun a => (n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * a i) := by
      intro σ
      simp only [Finset.sup'_image]
      have hpt : ((fun b : Fin n → ℝ => (n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * b i) ∘
          (fun a : Fin n → ℝ => c • a)) =
          fun a : Fin n → ℝ => c * ((n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * a i) := by
        funext a
        simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
        have hsum : (∑ i, (if σ i then (1 : ℝ) else -1) * (c * a i)) =
            c * ∑ i, (if σ i then (1 : ℝ) else -1) * a i := by
          rw [Finset.mul_sum _ _ _]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hsum]
        ring
      rw [hpt]
      exact (Finset.apply_sup'_eq_sup'_comp hA (fun x => c * x)
        (fun x y => mul_max_of_nonneg x y hc)).symm
    have hsum : (∑ σ : Fin n → Bool, (A.image fun a => c • a).sup' hAI
          (fun b => (n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * b i)) =
        c * ∑ σ : Fin n → Bool, A.sup' hA
          (fun a => (n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * a i) := by
      rw [Finset.mul_sum _ _ _]
      exact Finset.sum_congr rfl (fun σ _ => per σ)
    rw [hsum, mul_div_assoc]
  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    rw [hAe]
    simp [Finset.image_empty, empiricalRademacher_empty]

/-- Scaling: `c • A` has complexity `|c|` times that of `A`. -/
theorem empiricalRademacher_image_smul {n : ℕ} (A : Finset (Fin n → ℝ)) (c : ℝ) :
    empiricalRademacher (A.image fun a => c • a) = |c| * empiricalRademacher A := by
  by_cases hc : 0 ≤ c
  · rw [empiricalRademacher_image_smul_of_nonneg A hc, abs_of_nonneg hc]
  · have hc' : c < 0 := lt_of_not_ge hc
    have hfun : (fun a : Fin n → ℝ => c • a) =
        (fun b : Fin n → ℝ => |c| • b) ∘ (fun a : Fin n → ℝ => -a) := by
      funext a
      change c • a = |c| • -a
      funext i
      simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      rw [abs_of_neg hc']
      ring
    rw [hfun, ← Finset.image_image,
      empiricalRademacher_image_smul_of_nonneg _ (abs_nonneg c),
      empiricalRademacher_image_neg]

/-- Bridge to the Boolean form: the left side of `rademacher_finite_class` is the empirical
Rademacher complexity of the `±1` image of the class. -/
theorem empiricalRademacher_image_sign {m : ℕ} {H : Finset (Fin m → Bool)}
    (hH : H.Nonempty) :
    empiricalRademacher (H.image fun h i => if h i then (1 : ℝ) else -1) =
      (∑ σ : Fin m → Bool,
        H.sup' hH (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
          (if h i then (1 : ℝ) else -1))) / 2 ^ m / m := by
  rw [empiricalRademacher_eq_sum_sup'_div (hH.image _)]
  simp only [Finset.sup'_image]
  rfl

end ProbabilityTheory
