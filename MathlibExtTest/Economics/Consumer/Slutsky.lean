/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.Slutsky
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

open Filter Topology

/-! Leontief utility `min y₀ y₁` on `ℝ²₊` with target utility `1` at prices `(1, 2)`: Marshallian
demand `w / (p₀ + p₁)` in each good, constant Hicksian demand `(1, 1)`, and expenditure
`p₀ + p₁`. All hypotheses of the Slutsky equation hold, and its conclusion reads
`0 = -1/3 + 1/3 · 1`: the price and income effects cancel. -/

namespace MathlibExtTest.Economics.Consumer.Slutsky

open _root_.Economics.Consumer

theorem test_slutsky_numeric (i j : Fin 2) : (0:ℝ) = -1/3 + 1/3 * 1 := by
  have hp00 : ((![1, 2] : Fin 2 → ℝ) 0) = 1 := by simp
  have hp01 : ((![1, 2] : Fin 2 → ℝ) 1) = 2 := by simp
  have hdot : ∀ a b : Fin 2 → ℝ, a ⬝ᵥ b = a 0 * b 0 + a 1 * b 1 := by
    intro a b
    simp [dotProduct, Fin.sum_univ_two]
  have hpos0 : ∀ᶠ p : Fin 2 → ℝ in 𝓝 (![1, 2] : Fin 2 → ℝ), (0:ℝ) < p 0 := by
    have hlt : (0:ℝ) < (fun p : Fin 2 → ℝ => p 0) ![1, 2] := by
      show (0:ℝ) < (![1, 2] : Fin 2 → ℝ) 0
      rw [hp00]; norm_num
    have h := Filter.Tendsto.eventually
      (continuousAt_apply (0 : Fin 2) (![1, 2] : Fin 2 → ℝ)) (Ioi_mem_nhds hlt)
    simpa using h
  have hpos1 : ∀ᶠ p : Fin 2 → ℝ in 𝓝 (![1, 2] : Fin 2 → ℝ), (0:ℝ) < p 1 := by
    have hlt : (0:ℝ) < (fun p : Fin 2 → ℝ => p 1) ![1, 2] := by
      show (0:ℝ) < (![1, 2] : Fin 2 → ℝ) 1
      rw [hp01]; norm_num
    have h := Filter.Tendsto.eventually
      (continuousAt_apply (1 : Fin 2) (![1, 2] : Fin 2 → ℝ)) (Ioi_mem_nhds hlt)
    simpa using h
  have hexp : ∀ᶠ p : Fin 2 → ℝ in 𝓝 (![1, 2] : Fin 2 → ℝ),
      expenditure (fun (y : Fin 2 → ℝ) => min (y 0) (y 1))
        {y : Fin 2 → ℝ | 0 ≤ y} p 1 = p 0 + p 1 := by
    filter_upwards [hpos0, hpos1] with p hp0 hp1
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨(fun _ : Fin 2 => (1:ℝ)), ⟨?_, ?_⟩, ?_⟩
      · show (0 : Fin 2 → ℝ) ≤ fun _ => 1
        intro k
        exact zero_le_one
      · show (1:ℝ) ≤ (fun (y : Fin 2 → ℝ) => min (y 0) (y 1)) (fun _ => 1)
        simp
      · show p ⬝ᵥ (fun _ => (1:ℝ)) = p 0 + p 1
        rw [hdot]
        simp
    · intro b hb
      obtain ⟨y, ⟨yX, yu⟩, rfl⟩ := hb
      show p 0 + p 1 ≤ p ⬝ᵥ y
      rw [hdot]
      have hy0 : (1:ℝ) ≤ y 0 := (le_min_iff.mp yu).1
      have hy1 : (1:ℝ) ≤ y 1 := (le_min_iff.mp yu).2
      have g0 : p 0 * 1 ≤ p 0 * y 0 :=
        mul_le_mul_of_nonneg_left hy0 (le_of_lt hp0)
      have g1 : p 1 * 1 ≤ p 1 * y 1 :=
        mul_le_mul_of_nonneg_left hy1 (le_of_lt hp1)
      rw [mul_one] at g0
      rw [mul_one] at g1
      exact add_le_add g0 g1
  have hexp0 : expenditure (fun (y : Fin 2 → ℝ) => min (y 0) (y 1))
      {y : Fin 2 → ℝ | 0 ≤ y} ![1, 2] 1 = 3 := by
    have h := hexp.self_of_nhds
    rw [hp00, hp01] at h
    linarith
  have hbdd : ∀ᶠ p : Fin 2 → ℝ in 𝓝 (![1, 2] : Fin 2 → ℝ),
      BddBelow ((fun y => p ⬝ᵥ y) '' {y | y ∈ ({y : Fin 2 → ℝ | 0 ≤ y} : Set (Fin 2 → ℝ)) ∧
        (1:ℝ) ≤ (fun (y : Fin 2 → ℝ) => min (y 0) (y 1)) y}) := by
    filter_upwards [hpos0, hpos1] with p hp0 hp1
    refine ⟨0, ?_⟩
    rw [mem_lowerBounds]
    intro b hb
    obtain ⟨y, ⟨yX, yu⟩, rfl⟩ := hb
    show (0:ℝ) ≤ p ⬝ᵥ y
    rw [hdot]
    have y00 : (0:ℝ) ≤ y 0 := yX 0
    have y01 : (0:ℝ) ≤ y 1 := yX 1
    exact add_nonneg (mul_nonneg (le_of_lt hp0) y00) (mul_nonneg (le_of_lt hp1) y01)
  have hh : IsHicksianDemand (fun (y : Fin 2 → ℝ) => min (y 0) (y 1))
      ({y : Fin 2 → ℝ | 0 ≤ y} : Set (Fin 2 → ℝ)) (![1, 2] : Fin 2 → ℝ) 1
      (fun _ : Fin 2 => (1:ℝ)) := by
    refine ⟨?_, ?_, ?_⟩
    · show (0 : Fin 2 → ℝ) ≤ fun _ => 1
      intro k
      exact zero_le_one
    · show (1:ℝ) ≤ (fun (y : Fin 2 → ℝ) => min (y 0) (y 1)) (fun _ => 1)
      simp
    · intro y yX yu
      simp only [hdot, hp00, hp01]
      have hy0 : (1:ℝ) ≤ y 0 := (le_min_iff.mp yu).1
      have hy1 : (1:ℝ) ≤ y 1 := (le_min_iff.mp yu).2
      linarith
  have hdual : ∀ᶠ p : Fin 2 → ℝ in 𝓝 (![1, 2] : Fin 2 → ℝ),
      (fun (_ : Fin 2 → ℝ) (_ : Fin 2) => (1:ℝ)) p =
        (fun (p : Fin 2 → ℝ) (w : ℝ) (_ : Fin 2) => w / (p 0 + p 1)) p
          (expenditure (fun (y : Fin 2 → ℝ) => min (y 0) (y 1))
            {y : Fin 2 → ℝ | 0 ≤ y} p 1) := by
    filter_upwards [hexp, hpos0, hpos1] with p hpe hp0 hp1
    show (fun _ : Fin 2 => (1:ℝ)) = fun _ =>
      (expenditure (fun (y : Fin 2 → ℝ) => min (y 0) (y 1))
        {y : Fin 2 → ℝ | 0 ≤ y} p 1) / (p 0 + p 1)
    rw [hpe, div_self (ne_of_gt (by linarith : (0:ℝ) < p 0 + p 1))]
  have hediff : HasFDerivAt
      (fun (p : Fin 2 → ℝ) => expenditure (fun (y : Fin 2 → ℝ) => min (y 0) (y 1))
        {y : Fin 2 → ℝ | 0 ≤ y} p 1)
      ((ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ))
      (![1, 2] : Fin 2 → ℝ) := by
    have h0 : HasFDerivAt (fun (p : Fin 2 → ℝ) => p 0)
        (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ)
        (![1, 2] : Fin 2 → ℝ) :=
      ContinuousLinearMap.hasFDerivAt
        ((ContinuousLinearMap.proj (0 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ)
    have h1 : HasFDerivAt (fun (p : Fin 2 → ℝ) => p 1)
        (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ)
        (![1, 2] : Fin 2 → ℝ) :=
      ContinuousLinearMap.hasFDerivAt
        ((ContinuousLinearMap.proj (1 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ)
    have hadd := h0.add h1
    have heq : (fun (p : Fin 2 → ℝ) => expenditure (fun (y : Fin 2 → ℝ) => min (y 0) (y 1))
          {y : Fin 2 → ℝ | 0 ≤ y} p 1) =ᶠ[𝓝 (![1, 2] : Fin 2 → ℝ)]
        ((fun (p : Fin 2 → ℝ) => p 0) + (fun (p : Fin 2 → ℝ) => p 1)) := by
      filter_upwards [hexp] with p hp
      simpa [Pi.add_apply] using hp
    exact hadd.congr_of_eventuallyEq heq
  set q₀ : (Fin 2 → ℝ) × ℝ := ((![1, 2] : Fin 2 → ℝ),
    expenditure (fun (y : Fin 2 → ℝ) => min (y 0) (y 1))
      {y : Fin 2 → ℝ | 0 ≤ y} ![1, 2] 1) with hq₀_def
  set s' : ((Fin 2 → ℝ) × ℝ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ) +
      (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)) with hs'_def
  set Dinv : ((Fin 2 → ℝ) × ℝ) →L[ℝ] ℝ :=
    (-(((ContinuousLinearMap.mulLeftRight ℝ ℝ)
      ((fun (q : (Fin 2 → ℝ) × ℝ) => q.1 0 + q.1 1) q₀)⁻¹)
      ((fun (q : (Fin 2 → ℝ) × ℝ) => q.1 0 + q.1 1) q₀)⁻¹)).comp s' with hDinv_def
  set Dg : ((Fin 2 → ℝ) × ℝ) →L[ℝ] ℝ :=
    ((fun (q : (Fin 2 → ℝ) × ℝ) => q.2) q₀ • Dinv +
      (Inv.inv ∘ (fun (q : (Fin 2 → ℝ) × ℝ) => q.1 0 + q.1 1)) q₀ •
        (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ)) with hDg_def
  set Dx : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    Dg.smulRight (1 : Fin 2 → ℝ) with hDx_def
  have hw : HasFDerivAt (fun (q : (Fin 2 → ℝ) × ℝ) => q.2)
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ) q₀ :=
    ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ)
  have hs0 : HasFDerivAt (fun (q : (Fin 2 → ℝ) × ℝ) => q.1 0)
      ((ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)) q₀ :=
    ContinuousLinearMap.hasFDerivAt
      (((ContinuousLinearMap.proj (0 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ))
  have hs1 : HasFDerivAt (fun (q : (Fin 2 → ℝ) × ℝ) => q.1 1)
      ((ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)) q₀ :=
    ContinuousLinearMap.hasFDerivAt
      (((ContinuousLinearMap.proj (1 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ))
  have hs : HasFDerivAt (fun (q : (Fin 2 → ℝ) × ℝ) => q.1 0 + q.1 1) s' q₀ :=
    hs0.add hs1
  have hs_ne : (fun (q : (Fin 2 → ℝ) × ℝ) => q.1 0 + q.1 1) q₀ ≠ 0 := by
    simp only [hq₀_def]
    show (![1, 2] : Fin 2 → ℝ) 0 + (![1, 2] : Fin 2 → ℝ) 1 ≠ 0
    rw [hp00, hp01]
    norm_num
  have hinv : HasFDerivAt
      (Inv.inv ∘ (fun (q : (Fin 2 → ℝ) × ℝ) => q.1 0 + q.1 1)) Dinv q₀ :=
    (hasFDerivAt_inv' hs_ne).comp q₀ hs
  have hmul : HasFDerivAt ((fun (q : (Fin 2 → ℝ) × ℝ) => q.2) *
      (Inv.inv ∘ (fun (q : (Fin 2 → ℝ) × ℝ) => q.1 0 + q.1 1))) Dg q₀ :=
    hw.mul hinv
  have hdiv : HasFDerivAt (fun (q : (Fin 2 → ℝ) × ℝ) => q.2 / (q.1 0 + q.1 1)) Dg q₀ := by
    have heq : (fun (q : (Fin 2 → ℝ) × ℝ) => q.2 / (q.1 0 + q.1 1)) =
        (fun (q : (Fin 2 → ℝ) × ℝ) => q.2) *
          (Inv.inv ∘ (fun (q : (Fin 2 → ℝ) × ℝ) => q.1 0 + q.1 1)) := by
      funext q
      simp [Pi.mul_apply, Function.comp_apply, div_eq_mul_inv]
    rw [heq]
    exact hmul
  have hxdiff : HasFDerivAt
      (fun (q : (Fin 2 → ℝ) × ℝ) =>
        (fun (p : Fin 2 → ℝ) (w : ℝ) (_ : Fin 2) => w / (p 0 + p 1)) q.1 q.2)
      Dx q₀ := by
    have hsmul := hdiv.smul_const (1 : Fin 2 → ℝ)
    have heq : (fun (q : (Fin 2 → ℝ) × ℝ) =>
          (fun (p : Fin 2 → ℝ) (w : ℝ) (_ : Fin 2) => w / (p 0 + p 1)) q.1 q.2) =
        (fun (q : (Fin 2 → ℝ) × ℝ) =>
          (q.2 / (q.1 0 + q.1 1)) • (1 : Fin 2 → ℝ)) := by
      funext q i
      simp [Pi.smul_apply, smul_eq_mul, mul_one]
    rw [heq]
    exact hsmul
  have hhdiff : HasFDerivAt (fun (_ : Fin 2 → ℝ) (_ : Fin 2) => (1:ℝ))
      (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (![1, 2] : Fin 2 → ℝ) :=
    hasFDerivAt_const _ _
  have hslutsky := slutsky_equation
    (u := (fun (y : Fin 2 → ℝ) => min (y 0) (y 1)))
    (X := {y : Fin 2 → ℝ | 0 ≤ y})
    (ubar := (1:ℝ))
    (x := (fun (p : Fin 2 → ℝ) (w : ℝ) (_ : Fin 2) => w / (p 0 + p 1)))
    (h := (fun (_ : Fin 2 → ℝ) (_ : Fin 2) => (1:ℝ)))
    (p₀ := (![1, 2] : Fin 2 → ℝ))
    (e' := ((ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
      (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ)))
    (Dx := Dx) (Dh := (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)))
    hbdd hh hdual hediff hxdiff hhdiff
  have hDh0 : ∀ a b : Fin 2,
      (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (Pi.single b 1) a = (0:ℝ) := by
    intro a b
    simp
  have hDx1 : ∀ a b : Fin 2, Dx ((Pi.single b 1 : Fin 2 → ℝ), 0) a = -1/3 := by
    intro a b
    have hsum : ((Pi.single b 1 : Fin 2 → ℝ)) 0 + ((Pi.single b 1 : Fin 2 → ℝ)) 1 = 1 := by
      fin_cases b <;> simp
    simp only [hDx_def, ContinuousLinearMap.smulRight_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, mul_one, hDg_def, add_apply, smul_apply, ContinuousLinearMap.coe_snd',
      hDinv_def, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.mulLeftRight_apply, hs'_def, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.proj_apply, Function.comp_apply, hq₀_def, hexp0, hp00, hp01, hsum]
    norm_num
  have hDx2 : ∀ a : Fin 2, Dx ((0 : Fin 2 → ℝ), 1) a = 1/3 := by
    intro a
    simp only [hDx_def, ContinuousLinearMap.smulRight_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, mul_one, hDg_def, add_apply, smul_apply, ContinuousLinearMap.coe_snd',
      hDinv_def, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.mulLeftRight_apply, hs'_def, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.proj_apply, Function.comp_apply, hq₀_def, hexp0, hp00, hp01,
      Pi.zero_apply]
    norm_num
  have hxj : (3:ℝ) / (1 + 2) = 1 := by norm_num
  have h := hslutsky i j
  rw [hexp0, hDh0, hDx1, hDx2] at h
  rw [hp00, hp01, hxj] at h
  exact h

end MathlibExtTest.Economics.Consumer.Slutsky
