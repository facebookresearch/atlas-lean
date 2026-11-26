/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_AlgebraicCurve_absLogHeight_root_le_coeff.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.NumberTheory.Height.RootHeightBound

@[expose] public section

open AlgebraicCurve Polynomial

/-- exactSource consumer: the source's statement, through the pair height, follows with the
original binders from the canonical bound and the pair-height equality. -/
example {p : Polynomial (AlgebraicClosure ℚ)} (hmonic : p.Monic)
    {z : AlgebraicClosure ℚ} (hroot : p.eval z = 0) :
    absLogHeight ![z, 1]
      ≤ absLogHeight (fun k : Fin (p.natDegree + 1) => p.coeff k)
        + Real.log (Real.sqrt (p.natDegree + 1)) := by
  rw [AlgebraicCurve.absLogHeight_pair_eq_absLogHeight₁]
  exact AlgebraicCurve.absLogHeight₁_root_le_coeff hmonic hroot

/-- The canonical bound applied to the root `0` of the monic polynomial `X`. -/
example :
    NumberField.absLogHeight₁ (0 : AlgebraicClosure ℚ)
      ≤ absLogHeight (fun k : Fin ((X : Polynomial (AlgebraicClosure ℚ)).natDegree + 1) =>
          (X : Polynomial (AlgebraicClosure ℚ)).coeff k)
        + Real.log (Real.sqrt ((X : Polynomial (AlgebraicClosure ℚ)).natDegree + 1)) :=
  AlgebraicCurve.absLogHeight₁_root_le_coeff (monic_X) (by simp)

/-- Consumer of the canonical equality: the pair height is Mathlib's absolute height. -/
example (z : AlgebraicClosure ℚ) : absLogHeight ![z, 1] = NumberField.absLogHeight₁ z :=
  AlgebraicCurve.absLogHeight_pair_eq_absLogHeight₁ z

/-- Consumer of the canonical bound: the original binders apply verbatim. -/
example {p : Polynomial (AlgebraicClosure ℚ)} (hmonic : p.Monic)
    {z : AlgebraicClosure ℚ} (hroot : p.eval z = 0) :
    NumberField.absLogHeight₁ z
      ≤ absLogHeight (fun k : Fin (p.natDegree + 1) => p.coeff k)
        + Real.log (Real.sqrt (p.natDegree + 1)) :=
  AlgebraicCurve.absLogHeight₁_root_le_coeff hmonic hroot

namespace RootHeightBoundTest

/-- In a number field `K`, a square root `t` of `2` has logarithmic height `[K : ℚ] * log √2`:
`t` is an algebraic integer, and every archimedean place sends it to `√2`. -/
private theorem logHeight_sqrt_two {K : Type*} [Field K] [NumberField K] {t : K}
    (ht : t ^ 2 = 2) :
    Height.logHeight ![t, 1] = Module.finrank ℚ K * Real.log (Real.sqrt 2) := by
  have hint : IsIntegral ℤ t := by
    refine IsIntegral.of_pow two_pos ?_
    rw [ht, show (2 : K) = algebraMap ℤ K 2 by simp]
    exact isIntegral_algebraMap
  have hw (w : NumberField.InfinitePlace K) : w t = Real.sqrt 2 := by
    have h2 : w t ^ 2 = 2 := by
      rw [← map_pow, ht]
      exact_mod_cast w.map_natCast 2
    rw [← h2, Real.sqrt_sq (apply_nonneg w t)]
  have hv (v : NumberField.FinitePlace K) : Real.posLog (v t) = 0 := by
    let t' : NumberField.RingOfIntegers K := ⟨t, hint⟩
    have h1 : v t ≤ 1 :=
      NumberField.FinitePlace.norm_embedding_eq v (t' : K) ▸
        NumberField.FinitePlace.norm_le_one K v.maximalIdeal t'
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (apply_nonneg v t)]
    exact h1
  rw [← Height.logHeight₁_eq_logHeight, NumberField.logHeight₁_eq]
  simp_rw [hw, hv]
  rw [finsum_zero, add_zero, ← Finset.sum_mul, ← Nat.cast_sum,
    NumberField.InfinitePlace.sum_mult_eq,
    Real.posLog_eq_log (by rw [abs_of_nonneg (Real.sqrt_nonneg 2)]; simp)]

/-- The tuple height of a reindexing of `![s, 1]`, where `s ^ 2 = 2`, is `log 2 / 2`. The proof
unfolds `absLogHeight` and computes in the field that the tuple generates, so it pins the
normalisation by the degree of that field. -/
private theorem absLogHeight_sqrt_two {ι : Type*} [Fintype ι] (e : ι ≃ Fin 2)
    {s : AlgebraicClosure ℚ} (hs : s ^ 2 = 2) (x : ι → AlgebraicClosure ℚ)
    (hx : ∀ i, x i = ![s, 1] (e i)) :
    absLogHeight x = Real.log 2 / 2 := by
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range x)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral
  have : NumberField (IntermediateField.adjoin ℚ (Set.range x)) := {}
  have hsK : s ∈ IntermediateField.adjoin ℚ (Set.range x) := by
    have h := IntermediateField.subset_adjoin ℚ (Set.range x) ⟨e.symm 0, rfl⟩
    rwa [hx, Equiv.apply_symm_apply] at h
  let t : IntermediateField.adjoin ℚ (Set.range x) := ⟨s, hsK⟩
  have ht : t ^ 2 = 2 := Subtype.ext (by simp [t, hs]; rfl)
  have htuple : (fun i => (⟨x i, IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
      IntermediateField.adjoin ℚ (Set.range x))) = ![t, 1] ∘ e := by
    funext i
    refine Subtype.ext ?_
    change x i = ((![t, 1] ∘ e) i : AlgebraicClosure ℚ)
    rw [hx, Function.comp_apply]
    generalize e i = j
    fin_cases j <;> rfl
  have hd : (0 : ℝ) < Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range x)) := by
    exact_mod_cast Module.finrank_pos
  unfold absLogHeight
  rw [htuple, Height.logHeight_comp_equiv, logHeight_sqrt_two ht,
    Real.log_sqrt (by norm_num)]
  field_simp

/-- The tuple height of the zero tuple is `0`. -/
private theorem absLogHeight_zero {ι : Type*} [Fintype ι] :
    absLogHeight (0 : ι → AlgebraicClosure ℚ) = 0 := by
  have : FiniteDimensional ℚ
      (IntermediateField.adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ))) :=
    IntermediateField.finiteDimensional_adjoin fun y _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral
  have : NumberField (IntermediateField.adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ))) := {}
  have h0 : (fun i => (⟨(0 : ι → AlgebraicClosure ℚ) i,
      IntermediateField.subset_adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)) ⟨i, rfl⟩⟩ :
        IntermediateField.adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)))) = 0 :=
    funext fun _ => Subtype.ext rfl
  unfold absLogHeight
  rw [h0, Height.logHeight_zero, mul_zero]

/-- Concrete value at an element of degree two: `h(√2) = log 2 / 2`. The normalisation by the
degree matters here: without it the tuple height of `![√2, 1]` would be `log 2`. -/
example {s : AlgebraicClosure ℚ} (hs : s ^ 2 = 2) : absLogHeight ![s, 1] = Real.log 2 / 2 :=
  absLogHeight_sqrt_two (Equiv.refl _) hs _ fun _ => rfl

/-- The tuple height is projective: `![1, √2]` has the height of `![√2, 1]`. -/
example {s : AlgebraicClosure ℚ} (hs : s ^ 2 = 2) : absLogHeight ![1, s] = Real.log 2 / 2 :=
  absLogHeight_sqrt_two (Equiv.swap 0 1) hs _ fun i => by fin_cases i <;> rfl

/-- The index type may live in a higher universe: `ULift.{1} (Fin 2)` gives the same height. -/
example {s : AlgebraicClosure ℚ} (hs : s ^ 2 = 2) :
    absLogHeight (fun i : ULift.{1} (Fin 2) => ![s, 1] i.down) = Real.log 2 / 2 :=
  absLogHeight_sqrt_two Equiv.ulift hs _ fun _ => rfl

/-- Through the canonical equality, Mathlib's `NumberField.absLogHeight₁` of a square root of `2`
is `log 2 / 2`. -/
example {s : AlgebraicClosure ℚ} (hs : s ^ 2 = 2) :
    NumberField.absLogHeight₁ s = Real.log 2 / 2 := by
  rw [← absLogHeight_pair_eq_absLogHeight₁]
  exact absLogHeight_sqrt_two (Equiv.refl _) hs _ fun _ => rfl

/-- The canonical bound at the root `√2` of `X ^ 2 - 2`: the left side is `log 2 / 2`. -/
example {s : AlgebraicClosure ℚ} (hs : s ^ 2 = 2) :
    Real.log 2 / 2
      ≤ absLogHeight (fun k : Fin ((X ^ 2 - C 2 : (AlgebraicClosure ℚ)[X]).natDegree + 1) =>
          (X ^ 2 - C 2 : (AlgebraicClosure ℚ)[X]).coeff k)
        + Real.log (Real.sqrt ((X ^ 2 - C 2 : (AlgebraicClosure ℚ)[X]).natDegree + 1)) := by
  rw [← absLogHeight_sqrt_two (Equiv.refl _) hs ![s, 1] fun _ => rfl,
    absLogHeight_pair_eq_absLogHeight₁]
  exact absLogHeight₁_root_le_coeff (monic_X_pow_sub_C 2 two_ne_zero) (by simp [hs])

/-- Boundary: monicity cannot be dropped. The zero polynomial is not monic and vanishes at a
square root `s` of `2`, but its side of the bound is `0`, while the height of `s` is
`log 2 / 2`. -/
example : ¬ ∀ (p : Polynomial (AlgebraicClosure ℚ)) (z : AlgebraicClosure ℚ), p.eval z = 0 →
    absLogHeight ![z, 1]
      ≤ absLogHeight (fun k : Fin (p.natDegree + 1) => p.coeff k)
        + Real.log (Real.sqrt (p.natDegree + 1)) := by
  intro h
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : AlgebraicClosure ℚ) two_pos
  have h0 := h 0 s (eval_zero)
  have hc : (fun k : Fin ((0 : Polynomial (AlgebraicClosure ℚ)).natDegree + 1) =>
      (0 : Polynomial (AlgebraicClosure ℚ)).coeff k) = 0 :=
    funext fun _ => coeff_zero _
  rw [absLogHeight_sqrt_two (Equiv.refl _) hs ![s, 1] fun _ => rfl, hc, absLogHeight_zero] at h0
  norm_num at h0
  linarith [Real.log_pos (one_lt_two : (1 : ℝ) < 2)]

end RootHeightBoundTest
