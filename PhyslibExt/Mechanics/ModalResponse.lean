/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
import MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalization
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Free response in a mass-orthonormal modal basis

A linear undamped structure with finitely many degrees of freedom has a symmetric
positive-definite mass matrix `M` and a symmetric positive-semidefinite stiffness matrix `K`:

  `M x'' + K x = 0`.

## i. Overview

The existing simultaneous-diagonalization theorem gives an invertible congruence `C` with
`Cᵀ M C = 1` and `Cᵀ K C` diagonal; its diagonal entries `μ i = ω_i ^ 2` are nonnegative because
`K` is positive semidefinite (no coercivity of `K` is assumed). In the modal coordinates
`q = C⁻¹ x = Cᵀ M x` the equation decouples into `q_i'' + μ i q_i = 0`. A positive entry gives
the oscillation `q_i (0) cos (ω_i t) + q_i' (0) / ω_i sin (ω_i t)`, a zero entry gives the rigid
drift `q_i (0) + q_i' (0) t`, and the physical response `x = C q` matches both the initial
position and the initial velocity. It is the only `C²` solution with that initial data, so it
does not depend on the choice of modal basis inside a repeated eigenvalue.

A negative stiffness entry would need a hyperbolic branch, which is outside this module. Mass,
stiffness and initial data are model inputs.

## ii. Key results

- `exists_modalBasis`: a mass-orthonormal modal basis with nonnegative stiffness entries.
- `inv_eq_transpose_mul`: a mass-orthonormal `C` is invertible with `C⁻¹ = Cᵀ M`.
- `modal_decoupling`: in modal coordinates the equation decouples into `q_i'' + μ i q_i = 0`.
- `modalCoordinate_of_pos`, `modalCoordinate_zero`: the oscillation and rigid-drift branches.
- `modalCoordinate_solves`, `modalCoordinate_unique`: for `μ ≥ 0` the modal response solves the
  modal equation with its initial data and is its only twice continuously differentiable
  solution.
- `modalResponse_solves`, `modalResponse_unique`: the physical response `x = C q` solves
  `M x'' + K x = 0` with initial position `x₀` and velocity `v₀`, and is the only twice
  continuously differentiable solution with that initial data.

## iii. Table of contents

- A. Model
- B. The mass-orthonormal modal basis
- C. Decoupling
- D. Modal responses
- E. The physical response

## iv. References

- S. S. Rao, *Mechanical Vibrations*, 6th edition, Chapter 6 (multidegree-of-freedom systems).
- D. J. Inman, *Engineering Vibration*, 4th edition, Chapter 4 (multiple-degree-of-freedom
  systems, mass-normalized modes).
- R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd edition, Cambridge University Press
  (2013), Theorem 4.5.15 (simultaneous diagonalization by congruence).
- `MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalization`: the simultaneous
  diagonalization theorem reused here.
-/

@[expose] public section

namespace PhyslibExt.Mechanics.ModalResponse

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## A. Model -/

/-- The response of the modal equation `q'' + μ q = 0` with `q (0) = q₀` and `q' (0) = v₀`:
the oscillation `q₀ cos (√μ t) + v₀ / √μ sin (√μ t)` at the modal angular frequency `√μ` when
`μ > 0`, and the rigid drift `q₀ + v₀ t` otherwise (meant for `μ = 0`). -/
noncomputable def modalCoordinate (μ q₀ v₀ t : ℝ) : ℝ :=
  if 0 < μ then
    q₀ * Real.cos (Real.sqrt μ * t) + v₀ / Real.sqrt μ * Real.sin (Real.sqrt μ * t)
  else q₀ + v₀ * t

/-- The modal response in physical coordinates, `x (t) = C q (t)`, where the modal coordinates
start from `q (0) = C⁻¹ x₀` and `q' (0) = C⁻¹ v₀`. -/
noncomputable def modalResponse (C : Matrix n n ℝ) (μ : n → ℝ) (x₀ v₀ : n → ℝ) (t : ℝ) :
    n → ℝ :=
  C *ᵥ fun i => modalCoordinate (μ i) ((C⁻¹ *ᵥ x₀) i) ((C⁻¹ *ᵥ v₀) i) t

/-! ## B. The mass-orthonormal modal basis -/

/-- For a positive-definite mass matrix `M` and a positive-semidefinite stiffness matrix `K`
there is an invertible `C` with `Cᵀ M C = 1` and `Cᵀ K C = diagonal μ`, `μ i ≥ 0`. -/
lemma exists_modalBasis {M K : Matrix n n ℝ} (hM : M.PosDef) (hK : K.PosSemidef) :
    ∃ C : Matrix n n ℝ, IsUnit C ∧ Cᵀ * M * C = 1 ∧
      ∃ μ : n → ℝ, Cᵀ * K * C = diagonal μ ∧ ∀ i, 0 ≤ μ i := by
  obtain ⟨C, hC, hdiag, hMC⟩ :=
    open MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted in
    simultaneous_diagonalization_posDef K M (Matrix.isHermitian_iff_isSymm.mp hK.1) hM
  have hpsd : (Cᵀ * K * C).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hK.conjTranspose_mul_mul_same C
  exact ⟨C, hC, hMC, fun i => (Cᵀ * K * C) i i, hdiag.diagonal_diag.symm,
    fun i => hpsd.diag_nonneg⟩

/-- A mass-orthonormal `C` is invertible with inverse `Cᵀ M`, so `q = C⁻¹ x = Cᵀ M x`. -/
lemma inv_eq_transpose_mul {M C : Matrix n n ℝ} (hMC : Cᵀ * M * C = 1) :
    IsUnit C ∧ C⁻¹ = Cᵀ * M := by
  have hdet : IsUnit C.det := Matrix.isUnit_det_of_left_inverse hMC
  exact ⟨(Matrix.isUnit_iff_isUnit_det C).mpr hdet, Matrix.inv_eq_left_inv hMC⟩

/-! ## C. Decoupling -/

/-- In the modal coordinates `q = C⁻¹ x` the equation `M x'' + K x = 0` decouples into
`q_i'' + μ i q_i = 0`, for every twice continuously differentiable `x`. -/
lemma modal_decoupling {M K C : Matrix n n ℝ} {μ : n → ℝ} (hMC : Cᵀ * M * C = 1)
    (hKC : Cᵀ * K * C = diagonal μ) {x : ℝ → n → ℝ} (hx : ContDiff ℝ 2 x) (t : ℝ) :
    M *ᵥ deriv (deriv x) t + K *ᵥ x t = 0 ↔
      ∀ i, deriv (deriv fun s => C⁻¹ *ᵥ x s) t i + μ i * (C⁻¹ *ᵥ x t) i = 0 := by
  obtain ⟨hCu, -⟩ := inv_eq_transpose_mul hMC
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hCu
  have hCCi : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hCdet
  let L : (n → ℝ) →L[ℝ] (n → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin C⁻¹)
  have hxd : Differentiable ℝ x := hx.differentiable (by norm_num)
  have hxdd : Differentiable ℝ (deriv x) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hx).2.2.differentiable (by norm_num)
  have hq1 : deriv (fun s => C⁻¹ *ᵥ x s) = fun s => C⁻¹ *ᵥ deriv x s := by
    funext s
    exact (L.hasFDerivAt.comp_hasDerivAt s (hxd s).hasDerivAt).deriv
  have hq2 : deriv (deriv fun s => C⁻¹ *ᵥ x s) t = C⁻¹ *ᵥ deriv (deriv x) t := by
    rw [hq1]
    exact (L.hasFDerivAt.comp_hasDerivAt t (hxdd t).hasDerivAt).deriv
  rw [hq2]
  set a := deriv (deriv x) t
  set b := x t
  have key : Cᵀ *ᵥ (M *ᵥ a + K *ᵥ b) = C⁻¹ *ᵥ a + diagonal μ *ᵥ (C⁻¹ *ᵥ b) := by
    have ha : a = C *ᵥ (C⁻¹ *ᵥ a) := by rw [Matrix.mulVec_mulVec, hCCi, Matrix.one_mulVec]
    have hb : b = C *ᵥ (C⁻¹ *ᵥ b) := by rw [Matrix.mulVec_mulVec, hCCi, Matrix.one_mulVec]
    conv_lhs => rw [ha, hb]
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hMC, hKC,
      Matrix.one_mul]
  have hT : (M * C) * Cᵀ = 1 := by
    have h1 : Cᵀ * (M * C) = 1 := by rw [← Matrix.mul_assoc]; exact hMC
    exact mul_eq_one_comm.mp h1
  constructor
  · intro h i
    have h2 : Cᵀ *ᵥ (M *ᵥ a + K *ᵥ b) = 0 := by rw [h]; simp
    rw [key] at h2
    have := congrFun h2 i
    rw [Pi.add_apply, Matrix.mulVec_diagonal, Pi.zero_apply] at this
    exact this
  · intro h
    have key2 : C⁻¹ *ᵥ a + diagonal μ *ᵥ (C⁻¹ *ᵥ b) = 0 := by
      funext i
      rw [Pi.add_apply, Matrix.mulVec_diagonal, Pi.zero_apply]
      exact h i
    have hback : M *ᵥ a + K *ᵥ b = (M * C) *ᵥ (Cᵀ *ᵥ (M *ᵥ a + K *ᵥ b)) := by
      rw [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
    rw [hback, key, key2, Matrix.mulVec_zero]

/-! ## D. Modal responses -/

/-- A positive entry gives the oscillation at the modal frequency `√μ`. -/
lemma modalCoordinate_of_pos {μ : ℝ} (hμ : 0 < μ) (q₀ v₀ t : ℝ) :
    modalCoordinate μ q₀ v₀ t =
      q₀ * Real.cos (Real.sqrt μ * t) + v₀ / Real.sqrt μ * Real.sin (Real.sqrt μ * t) := by
  simp [modalCoordinate, hμ]

/-- A zero entry gives the rigid drift `q₀ + v₀ t`. -/
lemma modalCoordinate_zero (q₀ v₀ t : ℝ) : modalCoordinate 0 q₀ v₀ t = q₀ + v₀ * t := by
  simp [modalCoordinate]

/-- For `μ ≥ 0` the modal response is twice continuously differentiable, solves
`q'' + μ q = 0`, and starts from `q₀` with velocity `v₀`. -/
lemma modalCoordinate_solves {μ : ℝ} (hμ : 0 ≤ μ) (q₀ v₀ : ℝ) :
    ContDiff ℝ 2 (modalCoordinate μ q₀ v₀) ∧
      (∀ t, deriv (deriv (modalCoordinate μ q₀ v₀)) t + μ * modalCoordinate μ q₀ v₀ t = 0) ∧
      modalCoordinate μ q₀ v₀ 0 = q₀ ∧ deriv (modalCoordinate μ q₀ v₀) 0 = v₀ := by
  rcases hμ.lt_or_eq with hpos | hzero
  · have hωpos : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hpos
    have hω2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ
    have hfun : modalCoordinate μ q₀ v₀ =
        fun t => q₀ * Real.cos (Real.sqrt μ * t) + v₀ / Real.sqrt μ * Real.sin (Real.sqrt μ * t) :=
      funext fun t => modalCoordinate_of_pos hpos q₀ v₀ t
    set ω := Real.sqrt μ with hω
    have h1 : ∀ t : ℝ, HasDerivAt (fun s => ω * s) ω t := fun t => by
      simpa using (hasDerivAt_id t).const_mul ω
    have hd : ∀ t, HasDerivAt (fun t => q₀ * Real.cos (ω * t) + v₀ / ω * Real.sin (ω * t))
        (-q₀ * ω * Real.sin (ω * t) + v₀ * Real.cos (ω * t)) t := by
      intro t
      have h := (((Real.hasDerivAt_cos (ω * t)).comp t (h1 t)).const_mul q₀).add
        (((Real.hasDerivAt_sin (ω * t)).comp t (h1 t)).const_mul (v₀ / ω))
      have h' : HasDerivAt (fun t => q₀ * Real.cos (ω * t) + v₀ / ω * Real.sin (ω * t)) _ t := h
      exact h'.congr_deriv (by field_simp)
    have hdd : ∀ t, HasDerivAt (fun t => -q₀ * ω * Real.sin (ω * t) + v₀ * Real.cos (ω * t))
        (-μ * (q₀ * Real.cos (ω * t) + v₀ / ω * Real.sin (ω * t))) t := by
      intro t
      have h := (((Real.hasDerivAt_sin (ω * t)).comp t (h1 t)).const_mul (-q₀ * ω)).add
        (((Real.hasDerivAt_cos (ω * t)).comp t (h1 t)).const_mul v₀)
      have h' : HasDerivAt (fun t => -q₀ * ω * Real.sin (ω * t) + v₀ * Real.cos (ω * t)) _ t := h
      exact h'.congr_deriv (by rw [← hω2]; field_simp; ring)
    have hD1 : deriv (modalCoordinate μ q₀ v₀) =
        fun t => -q₀ * ω * Real.sin (ω * t) + v₀ * Real.cos (ω * t) := by
      rw [hfun]
      exact funext fun t => (hd t).deriv
    refine ⟨?_, fun t => ?_, ?_, ?_⟩
    · rw [hfun]
      fun_prop
    · rw [hD1, (hdd t).deriv]
      simp only [hfun]
      ring
    · rw [hfun]
      simp
    · rw [hD1]
      simp
  · subst hzero
    have hfun : modalCoordinate 0 q₀ v₀ = fun t => q₀ + v₀ * t :=
      funext fun t => modalCoordinate_zero q₀ v₀ t
    have hD1 : deriv (modalCoordinate 0 q₀ v₀) = fun _ => v₀ := by
      rw [hfun]
      funext t
      have h : HasDerivAt (fun t => q₀ + v₀ * t) v₀ t := by
        simpa using ((hasDerivAt_id t).const_mul v₀).const_add q₀
      exact h.deriv
    refine ⟨?_, fun t => ?_, ?_, ?_⟩
    · rw [hfun]
      fun_prop
    · rw [hD1]
      simp
    · rw [hfun]
      simp
    · rw [hD1]

/-- For `μ ≥ 0` every twice continuously differentiable solution of `q'' + μ q = 0` is the modal
response with its own initial position and velocity. -/
lemma modalCoordinate_unique {μ : ℝ} (hμ : 0 ≤ μ) {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q)
    (hEq : ∀ t, deriv (deriv q) t + μ * q t = 0) :
    q = modalCoordinate μ (q 0) (deriv q 0) := by
  obtain ⟨hrC, hrEq, hr0, hrv⟩ := modalCoordinate_solves hμ (q 0) (deriv q 0)
  set r := modalCoordinate μ (q 0) (deriv q 0) with hr
  let A : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).prod ((-μ) • ContinuousLinearMap.fst ℝ ℝ ℝ)
  have phase : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ t, deriv (deriv f) t + μ * f t = 0) →
      ∀ t, HasDerivAt (fun s => (f s, deriv f s)) (A (f t, deriv f t)) t := by
    intro f hf hfe t
    have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
    have hfdd : Differentiable ℝ (deriv f) :=
      ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2.differentiable (by norm_num)
    have h : HasDerivAt (fun s => (f s, deriv f s)) (deriv f t, deriv (deriv f) t) t :=
      (hfd t).hasDerivAt.prodMk (hfdd t).hasDerivAt
    refine h.congr_deriv ?_
    have := hfe t
    simp [A]
    linarith
  have heq := ODE_solution_unique_univ (v := fun _ p => A p) (s := fun _ => Set.univ) (t₀ := 0)
    (f := fun s => (q s, deriv q s)) (g := fun s => (r s, deriv r s))
    (fun _ => A.lipschitzWith.lipschitzOnWith) (fun t => ⟨phase q hq hEq t, Set.mem_univ _⟩)
    (fun t => ⟨phase r hrC hrEq t, Set.mem_univ _⟩) (by simp [hr0, hrv])
  funext t
  exact (Prod.ext_iff.mp (congrFun heq t)).1

/-! ## E. The physical response -/

/-- The modal response `x = C q` is twice continuously differentiable, solves
`M x'' + K x = 0`, and matches both initial-data vectors: `x (0) = x₀`, `x' (0) = v₀`. -/
lemma modalResponse_solves {M K C : Matrix n n ℝ} {μ : n → ℝ} (hMC : Cᵀ * M * C = 1)
    (hKC : Cᵀ * K * C = diagonal μ) (hμ : ∀ i, 0 ≤ μ i) (x₀ v₀ : n → ℝ) :
    ContDiff ℝ 2 (modalResponse C μ x₀ v₀) ∧
      (∀ t, M *ᵥ deriv (deriv (modalResponse C μ x₀ v₀)) t + K *ᵥ modalResponse C μ x₀ v₀ t = 0) ∧
      modalResponse C μ x₀ v₀ 0 = x₀ ∧ deriv (modalResponse C μ x₀ v₀) 0 = v₀ := by
  obtain ⟨hCu, -⟩ := inv_eq_transpose_mul hMC
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hCu
  have hCiC : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hCdet
  have hCCi : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hCdet
  have hpi : ∀ φ : ℝ → n → ℝ, ContDiff ℝ 2 φ → ∀ i s,
      deriv φ s i = deriv (fun s => φ s i) s ∧
        deriv (deriv φ) s i = deriv (deriv fun s => φ s i) s := by
    intro φ hφ i s
    have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    have hdd : Differentiable ℝ (deriv φ) :=
      ((contDiff_succ_iff_deriv (n := 1)).mp hφ).2.2.differentiable (by norm_num)
    have e1 : ∀ s, deriv φ s i = deriv (fun s => φ s i) s := fun s => by
      rw [deriv_pi (fun j => (differentiableAt_pi.mp (hd s)) j)]
    refine ⟨e1 s, ?_⟩
    rw [deriv_pi (fun j => (differentiableAt_pi.mp (hdd s)) j)]
    change deriv (fun x => deriv φ x i) s = _
    congr 1
    funext s'
    exact e1 s'
  set a := C⁻¹ *ᵥ x₀ with ha
  set b := C⁻¹ *ᵥ v₀ with hb
  set Q : ℝ → n → ℝ := fun t i => modalCoordinate (μ i) (a i) (b i) t with hQ
  have hsol := fun i => modalCoordinate_solves (hμ i) (a i) (b i)
  have hQC : ContDiff ℝ 2 Q := contDiff_pi.mpr fun i => (hsol i).1
  let Lc : (n → ℝ) →L[ℝ] (n → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin C)
  have hxQ : modalResponse C μ x₀ v₀ = fun t => C *ᵥ Q t := rfl
  have hxC : ContDiff ℝ 2 (modalResponse C μ x₀ v₀) := by
    rw [hxQ]
    exact Lc.contDiff.comp hQC
  have hQd : Differentiable ℝ Q := hQC.differentiable (by norm_num)
  have hCQ : (fun s => C⁻¹ *ᵥ modalResponse C μ x₀ v₀ s) = Q := by
    funext s
    rw [hxQ]
    simp only [Matrix.mulVec_mulVec, hCiC, Matrix.one_mulVec]
  have hCQt : ∀ s, C⁻¹ *ᵥ modalResponse C μ x₀ v₀ s = Q s := fun s => congrFun hCQ s
  refine ⟨hxC, fun t => ?_, ?_, ?_⟩
  · rw [modal_decoupling hMC hKC hxC t, hCQ, hCQt]
    intro i
    rw [(hpi Q hQC i t).2]
    exact (hsol i).2.1 t
  · rw [hxQ]
    have hQ0 : Q 0 = a := by
      funext i
      exact (hsol i).2.2.1
    simp only [hQ0, ha, Matrix.mulVec_mulVec, hCCi, Matrix.one_mulVec]
  · have hdx : deriv (modalResponse C μ x₀ v₀) 0 = C *ᵥ deriv Q 0 := by
      rw [hxQ]
      exact (Lc.hasFDerivAt.comp_hasDerivAt 0 (hQd 0).hasDerivAt).deriv
    have hQ'0 : deriv Q 0 = b := by
      funext i
      rw [(hpi Q hQC i 0).1]
      exact (hsol i).2.2.2
    rw [hdx, hQ'0, hb, Matrix.mulVec_mulVec, hCCi, Matrix.one_mulVec]

/-- Every twice continuously differentiable solution of `M x'' + K x = 0` is the modal response
with its own initial position and velocity. -/
lemma modalResponse_unique {M K C : Matrix n n ℝ} {μ : n → ℝ} (hMC : Cᵀ * M * C = 1)
    (hKC : Cᵀ * K * C = diagonal μ) (hμ : ∀ i, 0 ≤ μ i) {x : ℝ → n → ℝ} (hx : ContDiff ℝ 2 x)
    (hEq : ∀ t, M *ᵥ deriv (deriv x) t + K *ᵥ x t = 0) :
    x = modalResponse C μ (x 0) (deriv x 0) := by
  obtain ⟨hCu, -⟩ := inv_eq_transpose_mul hMC
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hCu
  have hCCi : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hCdet
  have hpi : ∀ φ : ℝ → n → ℝ, ContDiff ℝ 2 φ → ∀ i s,
      deriv φ s i = deriv (fun s => φ s i) s ∧
        deriv (deriv φ) s i = deriv (deriv fun s => φ s i) s := by
    intro φ hφ i s
    have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    have hdd : Differentiable ℝ (deriv φ) :=
      ((contDiff_succ_iff_deriv (n := 1)).mp hφ).2.2.differentiable (by norm_num)
    have e1 : ∀ s, deriv φ s i = deriv (fun s => φ s i) s := fun s => by
      rw [deriv_pi (fun j => (differentiableAt_pi.mp (hd s)) j)]
    refine ⟨e1 s, ?_⟩
    rw [deriv_pi (fun j => (differentiableAt_pi.mp (hdd s)) j)]
    change deriv (fun x => deriv φ x i) s = _
    congr 1
    funext s'
    exact e1 s'
  let L : (n → ℝ) →L[ℝ] (n → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin C⁻¹)
  set q : ℝ → n → ℝ := fun s => C⁻¹ *ᵥ x s with hq
  have hqC : ContDiff ℝ 2 q := L.contDiff.comp hx
  have hxd : Differentiable ℝ x := hx.differentiable (by norm_num)
  have hdec := fun t => (modal_decoupling hMC hKC hx t).mp (hEq t)
  have hcomp : ∀ i, (fun s => q s i) =
      modalCoordinate (μ i) (q 0 i) (deriv (fun s => q s i) 0) := by
    intro i
    apply modalCoordinate_unique (hμ i) ((contDiff_pi.mp hqC) i)
    intro t
    rw [← (hpi q hqC i t).2]
    exact hdec t i
  have hq'0 : deriv q 0 = C⁻¹ *ᵥ deriv x 0 :=
    (L.hasFDerivAt.comp_hasDerivAt 0 (hxd 0).hasDerivAt).deriv
  funext t
  have hxt : x t = C *ᵥ q t := by
    simp only [hq, Matrix.mulVec_mulVec, hCCi, Matrix.one_mulVec]
  rw [hxt]
  unfold modalResponse
  congr 1
  funext i
  rw [show q t i = (fun s => q s i) t from rfl, hcomp i, ← (hpi q hqC i 0).1, hq'0]

end PhyslibExt.Mechanics.ModalResponse
