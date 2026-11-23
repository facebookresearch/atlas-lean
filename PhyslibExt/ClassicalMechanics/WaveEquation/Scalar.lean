/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Scalar fields for the one-dimensional wave equation

## i. Overview

A real scalar field `φ : ℝ → ℝ → ℝ` (time first, then space) is read as
a field on Physlib's `Time` and one-dimensional `Space 1` by
`scalarWaveField φ t x = WithLp.toLp 2 (fun _ => φ t.val (x 0))`, where
`x 0` is the single coordinate of `Space 1` (the value of
`Space.oneEquiv x`). This module is the generic transport layer for
Physlib's `ClassicalMechanics.WaveEquation` predicate at `d = 1`: it
identifies the vector Laplacian of a transported field with its second
space derivative and the iterated Physlib time derivative with its
second time derivative. No field equation is assumed or proved here.

## ii. Key results

- `PhyslibExt.ClassicalMechanics.WaveEquation.Scalar.scalarWaveField`:
  the scalar-to-`Time → Space 1` transport.
- `PhyslibExt.ClassicalMechanics.WaveEquation.Scalar.laplacianVec_scalarWaveField`:
  the vector Laplacian is the second space derivative.
- `PhyslibExt.ClassicalMechanics.WaveEquation.Scalar.deriv_deriv_scalarWaveField`:
  the iterated time derivative is the second time derivative.

## iii. Table of contents

- A. Scalar transport
- B. Derivative adapters

## iv. References

- Physlib `ClassicalMechanics.WaveEquation.Basic` for `Space`, `Time`,
  their derivative operators, and the wave-equation predicate.
-/

@[expose] public section

namespace PhyslibExt.ClassicalMechanics.WaveEquation.Scalar

open Space Time

/-! ## A. Scalar transport -/

/-- A scalar field `φ t x` (time first) as a field `Time → Space 1 → EuclideanSpace ℝ (Fin 1)`,
read through `Time.val` and the coordinate `x 0` of `Space 1`. -/
def scalarWaveField (φ : ℝ → ℝ → ℝ) : Time → Space 1 → EuclideanSpace ℝ (Fin 1) :=
  fun t x => WithLp.toLp 2 (fun _ => φ t.val (x 0))

/-- Coordinate evaluation at `0 : Fin 1` on `Space 1`, as a linear map. -/
private def evalZeroLinear : Space 1 →ₗ[ℝ] ℝ where
  toFun x' := x' 0
  map_add' x y := Space.add_apply x y 0
  map_smul' c x := by
    show (c • x) 0 = c • x 0
    rw [smul_eq_mul]
    exact Space.smul_apply c x 0

/-- Coordinate evaluation at `0 : Fin 1` on `Space 1`, as a continuous linear
map with operator bound `1`. -/
private noncomputable def evalZeroCLM : Space 1 →L[ℝ] ℝ :=
  LinearMap.mkContinuous evalZeroLinear 1 (fun x' => by
    show ‖x' 0‖ ≤ 1 * ‖x'‖
    rw [Real.norm_eq_abs, one_mul]
    exact Space.abs_eval_le_norm x' 0)

private lemma evalZeroCLM_basis_zero :
    evalZeroCLM (Space.basis (d := 1) 0) = 1 := by
  show ((Space.basis (d := 1)) 0) (0 : Fin 1) = 1
  have h1 := OrthonormalBasis.repr_self (Space.basis (d := 1)) (0 : Fin 1)
  have h2 : ((Space.basis (d := 1)).repr ((Space.basis (d := 1)) 0)).ofLp (0 : Fin 1) =
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)).ofLp (0 : Fin 1) :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v.ofLp (0 : Fin 1)) h1
  have hLHS : ((Space.basis (d := 1)).repr ((Space.basis (d := 1)) 0)).ofLp 0 =
      ((Space.basis (d := 1)) 0) 0 := rfl
  rw [hLHS] at h2
  have hRHS : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)).ofLp 0 = 1 := by
    show (PiLp.single (β := fun _ : Fin 1 => ℝ) 2 (0 : Fin 1) (1 : ℝ)).ofLp 0 = 1
    rw [PiLp.single_apply]
    simp
  rw [hRHS] at h2
  exact h2

private lemma fderiv_space_slice (ψ : ℝ → ℝ) (ψ' : ℝ) (x' : Space 1)
    (hψ : HasDerivAt ψ ψ' (x' 0)) :
    fderiv ℝ (fun z : Space 1 => ψ (z 0)) x' (Space.basis (d := 1) 0) = ψ' := by
  have hπ : HasFDerivAt (fun z : Space 1 => z 0) evalZeroCLM x' :=
    evalZeroCLM.hasFDerivAt
  have hψF : HasFDerivAt ψ (ContinuousLinearMap.toSpanSingleton ℝ ψ') (x' 0) :=
    hψ.hasFDerivAt
  have hcomp := hψF.comp x' hπ
  have hfd := hcomp.fderiv
  show fderiv ℝ (ψ ∘ fun z : Space 1 => z 0) x' (Space.basis (d := 1) 0) = ψ'
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply, evalZeroCLM_basis_zero,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]

/-- The underlying real value of a `Time`, as a linear map. -/
private def timeValLinear : Time →ₗ[ℝ] ℝ where
  toFun t := t.val
  map_add' t1 t2 := Time.add_val t1 t2
  map_smul' c t := by
    show (c • t).val = c • t.val
    rw [smul_eq_mul]
    exact Time.smul_real_val c t

/-- The underlying real value of a `Time`, as a continuous linear map. -/
private def timeValCLM : Time →L[ℝ] ℝ :=
  LinearMap.mkContinuous timeValLinear 1
    (fun t => le_of_eq ((Time.norm_eq_val t).symm.trans (one_mul _).symm))

private lemma timeValCLM_one : timeValCLM 1 = 1 := by
  show (1 : Time).val = 1
  exact Time.one_val

/-- The constant vector with every `Fin 1` component equal to the input,
as a linear map. -/
private def constVecLinear : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) where
  toFun y := WithLp.toLp 2 (fun _ : Fin 1 => y)
  map_add' a b := by
    show WithLp.toLp 2 (fun _ : Fin 1 => a + b) =
      WithLp.toLp 2 (fun _ : Fin 1 => a) + WithLp.toLp 2 (fun _ : Fin 1 => b)
    rw [WithLp.ext_iff]
    funext i
    simp only [PiLp.add_apply]
  map_smul' c y := by
    show WithLp.toLp 2 (fun _ : Fin 1 => c • y) =
      c • WithLp.toLp 2 (fun _ : Fin 1 => y)
    rw [WithLp.ext_iff]
    funext i
    simp only [PiLp.smul_apply]

/-- The constant vector with every `Fin 1` component equal to the input,
as a continuous linear map. -/
private noncomputable def constVecCLM : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  LinearMap.mkContinuous constVecLinear 1 (fun y => by
    show ‖WithLp.toLp 2 (fun _ : Fin 1 => y)‖ ≤ 1 * ‖y‖
    have hnorm : ‖WithLp.toLp 2 (fun _ : Fin 1 => y)‖ = ‖y‖ := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, WithLp.ofLp_toLp,
        Real.sqrt_sq (norm_nonneg y)]
    rw [hnorm]
    exact le_of_eq (one_mul _).symm)

private lemma constVecCLM_apply (y : ℝ) :
    constVecCLM y = WithLp.toLp 2 (fun _ : Fin 1 => y) := rfl

private lemma fderiv_time_transport (ψ : ℝ → ℝ) (ψ' : ℝ) (t' : Time)
    (hψ : HasDerivAt ψ ψ' t'.val) :
    fderiv ℝ (fun s : Time => WithLp.toLp 2 (fun _ : Fin 1 => ψ s.val)) t' 1 =
      WithLp.toLp 2 (fun _ : Fin 1 => ψ') := by
  have hV : HasFDerivAt (fun s : Time => s.val) timeValCLM t' :=
    timeValCLM.hasFDerivAt
  have hψF : HasFDerivAt ψ (ContinuousLinearMap.toSpanSingleton ℝ ψ') t'.val :=
    hψ.hasFDerivAt
  have hE : HasFDerivAt (fun y : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => y)) constVecCLM (ψ t'.val) :=
    constVecCLM.hasFDerivAt
  have h1 := hψF.comp t' hV
  have h2 := hE.comp t' h1
  have hfd := h2.fderiv
  show fderiv ℝ ((fun y : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => y)) ∘
      (ψ ∘ fun s : Time => s.val)) t' 1 =
    WithLp.toLp 2 (fun _ : Fin 1 => ψ')
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply, timeValCLM_one,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, constVecCLM_apply]

/-! ## B. Derivative adapters -/

/-- On `Space 1`, the vector Laplacian of a transported field is the second `x`-derivative:
if the slice `φ t.val` has derivative `φx t.val y` at every `y`, and `φx t.val` has derivative
`φxx t.val (x 0)` at `x 0`, then `Δᵥ (scalarWaveField φ t) x` has component `φxx t.val (x 0)`. -/
lemma laplacianVec_scalarWaveField {φ φx φxx : ℝ → ℝ → ℝ} (t : Time) (x : Space 1)
    (hφx : ∀ y, HasDerivAt (fun y' => φ t.val y') (φx t.val y) y)
    (hφxx : HasDerivAt (fun y => φx t.val y) (φxx t.val (x 0)) (x 0)) :
    Δᵥ (scalarWaveField φ t) x = WithLp.toLp 2 (fun _ => φxx t.val (x 0)) := by
  have h1 : (fun x' : Space 1 => ∂[0] (fun z : Space 1 => φ t.val (z 0)) x') =
      (fun x' => φx t.val (x' 0)) := by
    funext x'
    exact fderiv_space_slice (fun y => φ t.val y) (φx t.val (x' 0)) x' (hφx (x' 0))
  have h2 : Δ (fun x' : Space 1 => φ t.val (x' 0)) x =
      ∂[0] (fun x' => φx t.val (x' 0)) x := by
    show (∑ i : Fin 1, ∂[i] (fun x' => ((Space.grad (fun z : Space 1 => φ t.val (z 0)) x') i)) x) =
      ∂[0] (fun x' => φx t.val (x' 0)) x
    rw [Fin.sum_univ_one]
    show ∂[0] (fun x' => ∂[0] (fun z : Space 1 => φ t.val (z 0)) x') x =
      ∂[0] (fun x' => φx t.val (x' 0)) x
    rw [h1]
  have hmain : Δ (fun x' : Space 1 => φ t.val (x' 0)) x = φxx t.val (x 0) := by
    rw [h2]
    exact fderiv_space_slice (fun y => φx t.val y) (φxx t.val (x 0)) x hφxx
  show WithLp.toLp 2 (fun i => Δ (fun x' => (scalarWaveField φ t x') i) x) =
    WithLp.toLp 2 (fun _ => φxx t.val (x 0))
  congr 1
  funext i
  exact hmain

/-- The iterated Physlib time derivative of a transported field is the second `t`-derivative:
if the slice `fun s => φ s (x 0)` has derivative `φt s (x 0)` at every `s`, and
`fun s => φt s (x 0)` has derivative `φtt t.val (x 0)` at `t.val`, then the second time
derivative in `ClassicalMechanics.WaveEquation` has component `φtt t.val (x 0)`. -/
lemma deriv_deriv_scalarWaveField {φ φt φtt : ℝ → ℝ → ℝ} (t : Time) (x : Space 1)
    (hφt : ∀ s, HasDerivAt (fun s' => φ s' (x 0)) (φt s (x 0)) s)
    (hφtt : HasDerivAt (fun s => φt s (x 0)) (φtt t.val (x 0)) t.val) :
    ∂ₜ (fun t => (∂ₜ (fun t => scalarWaveField φ t x) t)) t =
      WithLp.toLp 2 (fun _ => φtt t.val (x 0)) := by
  have h1 : (fun t : Time => ∂ₜ (fun t => scalarWaveField φ t x) t) =
      (fun t => WithLp.toLp 2 (fun _ : Fin 1 => φt t.val (x 0))) := by
    funext t
    exact fderiv_time_transport (fun s => φ s (x 0)) (φt t.val (x 0)) t (hφt t.val)
  have h2 : ∂ₜ (fun t : Time => ∂ₜ (fun t => scalarWaveField φ t x) t) t =
      ∂ₜ (fun t : Time => WithLp.toLp 2 (fun _ : Fin 1 => φt t.val (x 0))) t := by
    rw [h1]
  rw [h2]
  exact fderiv_time_transport (fun s => φt s (x 0)) (φtt t.val (x 0)) t hφtt

end PhyslibExt.ClassicalMechanics.WaveEquation.Scalar
