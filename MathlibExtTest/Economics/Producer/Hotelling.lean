/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Producer.Hotelling
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

@[expose] public section

open Filter Topology

/-! Two goods. A smooth technology `y₀ ≤ -y₁²` at prices `(1, 2)` has profit `p₁² / (4 p₀)`, optimal
net supply `(-1, 1)`, and price gradient `(-1, 1)`. A two-point technology `{(1, 0), (0, 1)}` has
the kinked profit `max p₀ p₁`, with two optimal net supplies at `(1, 1)`, so the uniqueness
theorem shows the profit function is not differentiable there. -/

namespace MathlibExtTest.Economics.Producer.Hotelling

open _root_.Economics.Producer

theorem smooth_isLUB (p : Fin 2 → ℝ) (hp0 : 0 < p 0) :
    IsLUB ((fun y => p ⬝ᵥ y) '' {y : Fin 2 → ℝ | y 0 ≤ -(y 1) ^ 2})
      ((p 1) ^ 2 / (4 * p 0)) := by
  have hp0ne : p 0 ≠ 0 := ne_of_gt hp0
  have h2ne : (2 : ℝ) * p 0 ≠ 0 := mul_ne_zero (by norm_num) hp0ne
  have h4ne : (4 : ℝ) * p 0 ≠ 0 := mul_ne_zero (by norm_num) hp0ne
  set t : ℝ := p 1 / (2 * p 0) with ht
  set ys : Fin 2 → ℝ := ![-t ^ 2, t] with hys
  have e0 : ys 0 = -t ^ 2 := by simp [hys]
  have e1 : ys 1 = t := by simp [hys]
  have hysmem : ys ∈ {y : Fin 2 → ℝ | y 0 ≤ -(y 1) ^ 2} := by
    show ys 0 ≤ -(ys 1) ^ 2
    rw [e0, e1]
  have hatt : p ⬝ᵥ ys = (p 1) ^ 2 / (4 * p 0) := by
    have hdot : p ⬝ᵥ ys = p 0 * ys 0 + p 1 * ys 1 := by
      simp [dotProduct, Fin.sum_univ_two]
    rw [hdot, e0, e1, ht]
    field_simp
    ring
  have hub : (p 1) ^ 2 / (4 * p 0) ∈
      upperBounds ((fun y => p ⬝ᵥ y) '' {y : Fin 2 → ℝ | y 0 ≤ -(y 1) ^ 2}) := by
    rw [mem_upperBounds]
    intro s hs
    obtain ⟨y, hymem, rfl⟩ := hs
    show p ⬝ᵥ y ≤ (p 1) ^ 2 / (4 * p 0)
    have hymem2 : y 0 ≤ -(y 1) ^ 2 := hymem
    have hdot : p ⬝ᵥ y = p 0 * y 0 + p 1 * y 1 := by
      simp [dotProduct, Fin.sum_univ_two]
    rw [hdot]
    have hle1 : p 0 * y 0 ≤ p 0 * (-(y 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hymem2 (le_of_lt hp0)
    have h4pos : 0 < 4 * p 0 := by positivity
    have hsq : p 0 * (-(y 1) ^ 2) + p 1 * y 1 ≤ (p 1) ^ 2 / (4 * p 0) := by
      rw [le_div_iff₀ h4pos]
      nlinarith [sq_nonneg (p 1 - 2 * p 0 * y 1)]
    calc p 0 * y 0 + p 1 * y 1
        ≤ p 0 * (-(y 1) ^ 2) + p 1 * y 1 := by linarith
      _ ≤ (p 1) ^ 2 / (4 * p 0) := hsq
  exact IsGreatest.isLUB ⟨⟨ys, hysmem, hatt⟩, hub⟩

theorem smooth_eventually :
    ∀ᶠ p in 𝓝 (![1, 2] : Fin 2 → ℝ),
      IsLUB ((fun y => p ⬝ᵥ y) '' {y : Fin 2 → ℝ | y 0 ≤ -(y 1) ^ 2})
        ((p 1) ^ 2 / (4 * p 0)) := by
  have hcont : ContinuousAt (fun p : Fin 2 → ℝ => p 0) ![1, 2] :=
    (continuous_apply 0).continuousAt
  have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 (((![1, 2] : Fin 2 → ℝ)) 0) :=
    Ioi_mem_nhds (by norm_num [Matrix.cons_val_zero])
  filter_upwards [hcont hmem] with p hp
  exact smooth_isLUB p hp

theorem smooth_y0_mem :
    (![-1, 1] : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | y 0 ≤ -(y 1) ^ 2} := by
  have e0 : (![-1, 1] : Fin 2 → ℝ) 0 = -1 := by simp
  have e1 : (![-1, 1] : Fin 2 → ℝ) 1 = 1 := by simp
  show (![-1, 1] : Fin 2 → ℝ) 0 ≤ -((![-1, 1] : Fin 2 → ℝ) 1) ^ 2
  rw [e0, e1]
  norm_num

theorem smooth_attainment :
    (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![-1, 1] =
      (((![1, 2] : Fin 2 → ℝ)) 1) ^ 2 / (4 * (((![1, 2] : Fin 2 → ℝ)) 0)) := by
  simp [dotProduct, Fin.sum_univ_two]
  norm_num

theorem smooth_hasFDerivAt :
    HasFDerivAt (fun p : Fin 2 → ℝ => (p 1) ^ 2 / (4 * p 0))
      ((ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) -
        (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ)) ![1, 2] := by
  have hproj1 : HasFDerivAt (fun p : Fin 2 → ℝ => p 1)
      (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) ![1, 2] :=
    (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun p => (ContinuousLinearMap.proj_apply 1 p).symm)
  have hproj0 : HasFDerivAt (fun p : Fin 2 → ℝ => p 0)
      (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) ![1, 2] :=
    (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun p => (ContinuousLinearMap.proj_apply 0 p).symm)
  have hnum := hproj1.pow 2
  have hden := hproj0.const_mul (4 : ℝ)
  have hne : (4 : ℝ) * (((![1, 2] : Fin 2 → ℝ)) 0) ≠ 0 := by
    norm_num [Matrix.cons_val_zero]
  have hinv0 := hasFDerivAt_inv hne
  have hinv := HasFDerivAt.comp (![1, 2] : Fin 2 → ℝ) hinv0 hden
  have hinv' : HasFDerivAt (fun p : Fin 2 → ℝ => (4 * p 0)⁻¹) _ ![1, 2] :=
    hinv.congr_of_eventuallyEq (Eventually.of_forall fun p => rfl)
  have hmul := hnum.mul hinv'
  have hdiv : HasFDerivAt (fun p : Fin 2 → ℝ => (p 1) ^ 2 / (4 * p 0)) _ ![1, 2] :=
    hmul.congr_of_eventuallyEq
      (Eventually.of_forall fun p => by simp [Pi.mul_apply, div_eq_mul_inv])
  convert hdiv using 2
  ext v
  simp only [sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  ring

theorem smooth_conclusion :
    ∀ v : Fin 2 → ℝ,
      ((ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) -
        (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ)) v = -v 0 + v 1 := by
  have h := hasFDerivAt_profit_eq_netSupply (Y := {y : Fin 2 → ℝ | y 0 ≤ -(y 1) ^ 2})
    (p₀ := (![1, 2] : Fin 2 → ℝ)) (y₀ := (![-1, 1] : Fin 2 → ℝ))
    smooth_eventually smooth_y0_mem smooth_attainment smooth_hasFDerivAt
  intro v
  rw [h v]
  have hdot : (![-1, 1] : Fin 2 → ℝ) ⬝ᵥ v = -v 0 + v 1 := by
    simp [dotProduct, Fin.sum_univ_two]
  exact hdot

theorem kinked_isLUB (p : Fin 2 → ℝ) :
    IsLUB ((fun y => p ⬝ᵥ y) '' ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)))
      (max (p 0) (p 1)) := by
  have e1 : p ⬝ᵥ (![1, 0] : Fin 2 → ℝ) = p 0 := by simp [dotProduct, Fin.sum_univ_two]
  have e2 : p ⬝ᵥ (![0, 1] : Fin 2 → ℝ) = p 1 := by simp [dotProduct, Fin.sum_univ_two]
  rw [Set.image_pair, e1, e2]
  refine IsGreatest.isLUB ⟨?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact max_choice _ _
  · rw [mem_upperBounds]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _

theorem kinked_eventually :
    ∀ᶠ p in 𝓝 (![1, 1] : Fin 2 → ℝ),
      IsLUB ((fun y => p ⬝ᵥ y) '' ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)))
        (max (p 0) (p 1)) :=
  Eventually.of_forall kinked_isLUB

theorem kinked_opt1 :
    (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] =
      max (((![1, 1] : Fin 2 → ℝ)) 0) (((![1, 1] : Fin 2 → ℝ)) 1) := by
  simp [dotProduct, Fin.sum_univ_two]

theorem kinked_opt2 :
    (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] =
      max (((![1, 1] : Fin 2 → ℝ)) 0) (((![1, 1] : Fin 2 → ℝ)) 1) := by
  simp [dotProduct, Fin.sum_univ_two]

theorem kinked_not_differentiable :
    ¬ DifferentiableAt ℝ (fun p : Fin 2 → ℝ => max (p 0) (p 1)) ![1, 1] := by
  intro hdiff
  have h := hdiff.hasFDerivAt
  have mem1 : (![1, 0] : Fin 2 → ℝ) ∈ ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) := by simp
  have mem2 : (![0, 1] : Fin 2 → ℝ) ∈ ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) := by simp
  have heq := netSupply_unique_of_hasFDerivAt (Y := ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)))
    (p₀ := (![1, 1] : Fin 2 → ℝ)) (y₀ := (![1, 0] : Fin 2 → ℝ)) (y₁ := (![0, 1] : Fin 2 → ℝ))
    kinked_eventually mem1 kinked_opt1 mem2 kinked_opt2 h
  have hcon := congrArg (fun v : Fin 2 → ℝ => v 0) heq
  simp at hcon

end MathlibExtTest.Economics.Producer.Hotelling

/-! The smooth technology again, through the canonical gradient form: the derivative of profit at
`(1, 2)` is `Real.dotL (-1, 1)`. -/

namespace MathlibExtTest.Economics.Producer.Hotelling.DotL

open _root_.Economics.Producer

example : (((-1 : ℝ) • ContinuousLinearMap.proj 0 + (1 : ℝ) • ContinuousLinearMap.proj 1 :
    (Fin 2 → ℝ) →L[ℝ] ℝ)) = Real.dotL ![-1, 1] := by
  have hπ : ∀ᶠ p in 𝓝 (![1, 2] : Fin 2 → ℝ),
      IsLUB ((fun y => p ⬝ᵥ y) '' {y : Fin 2 → ℝ | y 0 ≤ -(y 1) ^ 2})
        ((p 1) ^ 2 / (4 * p 0)) := by
    have hpos : ∀ᶠ p : Fin 2 → ℝ in 𝓝 ![1, 2], 0 < p 0 := by
      have hopen : IsOpen {p : Fin 2 → ℝ | 0 < p 0} :=
        isOpen_lt continuous_const (continuous_apply 0)
      have hmem : (![1, 2] : Fin 2 → ℝ) ∈ {p : Fin 2 → ℝ | 0 < p 0} := by
        show (0 : ℝ) < ![1, 2] 0
        simp only [Matrix.cons_val_zero]
        norm_num
      exact eventually_of_mem (hopen.mem_nhds hmem) (fun p hp => hp)
    filter_upwards [hpos] with p hp0
    have hne : p 0 ≠ 0 := ne_of_gt hp0
    have h4 : (4 : ℝ) * p 0 ≠ 0 := mul_ne_zero (by norm_num) hne
    have h2 : (2 : ℝ) * p 0 ≠ 0 := mul_ne_zero (by norm_num) hne
    set ystar : Fin 2 → ℝ := ![-(p 1 / (2 * p 0)) ^ 2, p 1 / (2 * p 0)] with hystar
    have hystar_mem : ystar ∈ {y : Fin 2 → ℝ | y 0 ≤ -(y 1) ^ 2} := by
      show ystar 0 ≤ -(ystar 1) ^ 2
      simp only [hystar, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact le_refl _
    have hub : ∀ y ∈ {y : Fin 2 → ℝ | y 0 ≤ -(y 1) ^ 2},
        p ⬝ᵥ y ≤ (p 1) ^ 2 / (4 * p 0) := by
      intro y hy
      have hy' : y 0 ≤ -(y 1) ^ 2 := hy
      have hdecomp : (p 1) ^ 2 / (4 * p 0) - (p 0 * y 0 + p 1 * y 1)
          = (2 * p 0 * y 1 - p 1) ^ 2 / (4 * p 0) + p 0 * (-(y 1) ^ 2 - y 0) := by
        field_simp
        ring
      have hnn1 : 0 ≤ (2 * p 0 * y 1 - p 1) ^ 2 / (4 * p 0) :=
        div_nonneg (sq_nonneg _) (by positivity)
      have hnn2 : 0 ≤ p 0 * (-(y 1) ^ 2 - y 0) :=
        mul_nonneg (le_of_lt hp0) (sub_nonneg.mpr hy')
      have hnn := add_nonneg hnn1 hnn2
      simp only [dotProduct, Fin.sum_univ_two]
      linarith
    have hval : p ⬝ᵥ ystar = (p 1) ^ 2 / (4 * p 0) := by
      simp only [dotProduct, Fin.sum_univ_two, hystar, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      field_simp
      ring
    have hmax : IsGreatest ((fun y => p ⬝ᵥ y) '' {y : Fin 2 → ℝ | y 0 ≤ -(y 1) ^ 2})
        (p ⬝ᵥ ystar) := by
      refine ⟨Set.mem_image_of_mem _ hystar_mem, ?_⟩
      intro x hx
      obtain ⟨y, hyY, rfl⟩ := hx
      rw [hval]
      exact hub y hyY
    have hlub := hmax.isLUB
    rwa [hval] at hlub
  have hy₀ : (![-1, 1] : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | y 0 ≤ -(y 1) ^ 2} := by
    show (![-1, 1] : Fin 2 → ℝ) 0 ≤ -((![-1, 1] : Fin 2 → ℝ) 1) ^ 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hprofit : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![-1, 1]
      = ((![1, 2] : Fin 2 → ℝ) 1) ^ 2 / (4 * (![1, 2] : Fin 2 → ℝ) 0) := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hdiff : HasFDerivAt (fun p : Fin 2 → ℝ => (p 1) ^ 2 / (4 * p 0))
      (((-1 : ℝ) • ContinuousLinearMap.proj 0 + (1 : ℝ) • ContinuousLinearMap.proj 1 :
        (Fin 2 → ℝ) →L[ℝ] ℝ)) ![1, 2] := by
    have h1 : HasFDerivAt (fun p : Fin 2 → ℝ => p 1)
        (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) ![1, 2] := by
      refine HasFDerivAt.congr_of_eventuallyEq
        ((ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)).hasFDerivAt ?_
      exact Eventually.of_forall (fun p => (ContinuousLinearMap.proj_apply 1 p).symm)
    have h0 : HasFDerivAt (fun p : Fin 2 → ℝ => p 0)
        (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) ![1, 2] := by
      refine HasFDerivAt.congr_of_eventuallyEq
        ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ)).hasFDerivAt ?_
      exact Eventually.of_forall (fun p => (ContinuousLinearMap.proj_apply 0 p).symm)
    have h1sq := h1.mul h1
    have h4 := h0.const_mul 4
    have hne : (4 : ℝ) * (![1, 2] : Fin 2 → ℝ) 0 ≠ 0 := by
      simp only [Matrix.cons_val_zero]
      norm_num
    have hinv := HasFDerivAt.comp ![1, 2] (hasFDerivAt_inv hne) h4
    have hcomb := h1sq.mul hinv
    refine HasFDerivAt.congr_of_eventuallyEq (hcomb.congr_fderiv ?hder) ?hEq
    · ext v
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Pi.mul_apply,
        Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
      ring
    · exact Eventually.of_forall (fun p => by
        simp only [Pi.mul_apply, Function.comp_apply, div_eq_mul_inv, pow_two])
  exact hasFDerivAt_profit_eq_dotL hπ hy₀ hprofit hdiff

end MathlibExtTest.Economics.Producer.Hotelling.DotL
