/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.CompensatedDemand
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Convex.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Examples and checks for `MathlibExt.Economics.Consumer.CompensatedDemand` (Atlas EC04.T05). -/

namespace MathlibExtTest.Economics.Consumer.CompensatedDemand

open Matrix

noncomputable def e : (Fin 2 → ℝ) → ℝ := fun p => p 0 + p 1 - (p 0 - p 1) ^ 2 / 2

def h : (Fin 2 → ℝ) → Fin 2 → ℝ := fun p => ![1 - (p 0 - p 1), 1 + (p 0 - p 1)]

def D0 : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2) - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2)

def D1 : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)

def Dh : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi ![D0, D1]

theorem shephard : ∀ q ∈ (Set.univ : Set (Fin 2 → ℝ)),
    HasFDerivAt e (Real.dotL (h q)) q := by
  intro q _
  have h0 : HasFDerivAt (fun p : Fin 2 → ℝ => p 0) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2)) q :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2)).hasFDerivAt
  have h1 : HasFDerivAt (fun p : Fin 2 → ℝ => p 1) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)) q :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)).hasFDerivAt
  have hadd : HasFDerivAt (fun p : Fin 2 → ℝ => p 0 + p 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)) q := h0.add h1
  have hsub : HasFDerivAt (fun p : Fin 2 → ℝ => p 0 - p 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)) q := h0.sub h1
  have hsq : HasFDerivAt (fun p : Fin 2 → ℝ => (p 0 - p 1) ^ 2)
      (((2 : ℕ) • (q 0 - q 1) ^ 1) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2))) q :=
    hsub.pow 2
  have hdiv : HasFDerivAt (fun p : Fin 2 → ℝ => (p 0 - p 1) ^ 2 / 2)
      ((2⁻¹ : ℝ) • (((2 : ℕ) • (q 0 - q 1) ^ 1) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)))) q := by
    have hfun : (fun p : Fin 2 → ℝ => (p 0 - p 1) ^ 2 / 2)
        = (fun p => (p 0 - p 1) ^ 2 * 2⁻¹) := by
      funext p
      exact div_eq_mul_inv _ _
    rw [hfun]
    exact hsq.mul_const _
  have htot : HasFDerivAt e
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)) -
        (2⁻¹ : ℝ) • (((2 : ℕ) • (q 0 - q 1) ^ 1) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)))) q := by
    have hfun2 : e = (fun p : Fin 2 → ℝ => p 0 + p 1)
        - (fun p : Fin 2 → ℝ => (p 0 - p 1) ^ 2 / 2) := by
      funext p
      simp [e, Pi.sub_apply]
    rw [hfun2]
    exact hadd.sub hdiv
  have hCLM : (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)) -
        (2⁻¹ : ℝ) • (((2 : ℕ) • (q 0 - q 1) ^ 1) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)))
      = Real.dotL (h q) := by
    ext v
    simp [Real.dotL_apply, dotProduct, Fin.sum_univ_two, h, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul, nsmul_eq_mul, pow_one]
    ring
  rw [hCLM] at htot
  exact htot

theorem concav : ConcaveOn ℝ Set.univ e := by
  have hlin : ConcaveOn ℝ Set.univ (fun p : Fin 2 → ℝ => p 0 + p 1) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have heq : (fun p : Fin 2 → ℝ => p 0 + p 1) (a • x + b • y)
        = a • (fun p : Fin 2 → ℝ => p 0 + p 1) x
          + b • (fun p : Fin 2 → ℝ => p 0 + p 1) y := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact le_of_eq heq.symm
  have hsq2 : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2 / 2) := by
    have h := (Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).smul
      (show (0 : ℝ) ≤ 2⁻¹ by norm_num)
    have hfun : (fun x : ℝ => x ^ 2 / 2) = (fun x => (2⁻¹ : ℝ) • x ^ 2) := by
      funext x
      simp [smul_eq_mul]
      ring
    rw [hfun]
    exact h
  have hquad : ConvexOn ℝ Set.univ (fun p : Fin 2 → ℝ => (p 0 - p 1) ^ 2 / 2) :=
    hsq2.comp_linearMap (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) - LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2))
  have hsub := hlin.sub hquad
  have hfun2 : e = (fun p : Fin 2 → ℝ => p 0 + p 1)
      - (fun p : Fin 2 → ℝ => (p 0 - p 1) ^ 2 / 2) := by
    funext p
    simp [e, Pi.sub_apply]
  rw [hfun2]
  exact hsub

theorem hasDeriv_h (q : Fin 2 → ℝ) : HasFDerivAt h Dh q := by
  have hmain : HasFDerivAt (fun p : Fin 2 → ℝ => Dh p + ![1, 1]) Dh q :=
    Dh.hasFDerivAt.add_const ![1, 1]
  have hfun : h = (fun p : Fin 2 → ℝ => Dh p + ![1, 1]) := by
    funext p
    show h p = Dh p + ![1, 1]
    ext i
    fin_cases i
    · simp [h, Dh, D0, Matrix.cons_val_zero]
      ring
    · simp [h, Dh, D1, Matrix.cons_val_one]
      ring
  rw [hfun]
  exact hmain

theorem mat_eq : MathlibExt.Economics.CompensatedDemand.compensatedJacobian Dh
    = !![-1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MathlibExt.Economics.CompensatedDemand.compensatedJacobian,
      Matrix.of_apply, Dh, D0, D1, ContinuousLinearMap.pi_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]

theorem symm_test (p : Fin 2 → ℝ) :
    (MathlibExt.Economics.CompensatedDemand.compensatedJacobian Dh).IsSymm :=
  MathlibExt.Economics.CompensatedDemand.compensatedJacobian_isSymm
    isOpen_univ (Set.mem_univ p) shephard (hasDeriv_h p)

theorem nsd_test (p : Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    x ⬝ᵥ (MathlibExt.Economics.CompensatedDemand.compensatedJacobian Dh *ᵥ x) ≤ 0 :=
  MathlibExt.Economics.CompensatedDemand.dotProduct_compensatedJacobian_mulVec_nonpos
    isOpen_univ (Set.mem_univ p) concav shephard (hasDeriv_h p) x

example (p : Fin 2 → ℝ) :
    (MathlibExt.Economics.CompensatedDemand.compensatedJacobian Dh).IsSymm
      ∧ ∀ x, x ⬝ᵥ (MathlibExt.Economics.CompensatedDemand.compensatedJacobian Dh *ᵥ x) ≤ 0 :=
  ⟨symm_test p, nsd_test p⟩

end MathlibExtTest.Economics.Consumer.CompensatedDemand
