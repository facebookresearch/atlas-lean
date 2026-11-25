/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.ModalResponse
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Rayleigh damping and modal participation

In a complete mass-orthonormal modal basis, Rayleigh damping is diagonal
with modal coefficients `α + β * μ j`, the damped equation decouples mode
by mode, and the participation factors of a prescribed base-influence
vector have squares summing to the total mass seen by the base motion.

## i. Overview

A finite linear structure has mass matrix `M`, stiffness matrix `K`, and
Rayleigh (mass- and stiffness-proportional) damping
`Cd = α • M + β • K`, with equation `M x'' + Cd x' + K x = f t` for a
time-dependent load `f`. Coordinates are in one coherent unit system;
`α` has units of 1/time and `β` of time. For an oscillatory mode
(`μ j = ω_j ^ 2 > 0`), the modal damping coefficient `α + β * μ j` is
the usual `2 ζ_j ω_j` with `ζ_j = (α + β * μ j) / (2 * ω_j)`; a rigid
mode (`μ j = 0`) has no damping ratio and is described only by its modal
damping coefficient `α`. The damping transformation and the decoupling
equivalence themselves hold for every real `α` and `β`.

The modal basis `Φ` is complete and mass-orthonormal:
`Φᵀ * M * Φ = 1` and `Φᵀ * K * Φ = diagonal μ`, with `μ j = ω_j ^ 2`.
Repeated values of `μ` are allowed; completeness inside each eigenspace
is encoded by the full mass-orthonormality equation, not by distinct-mode
orthogonality. Modal coordinates are `q = (Φᵀ * M) *ᵥ x`, and the modal
load is `Φᵀ *ᵥ f t`. For the physical premises `M.PosDef` and
`K.PosSemidef`, such a basis is supplied by
`PhyslibExt.Mechanics.ModalResponse.exists_modalBasis`; this file proves
no second modal-basis existence theorem.

Derivatives are Mathlib's `deriv`. The decoupling equivalence is
pointwise in `t` with no regularity premise: `deriv` commutes with the
invertible modal transform, so for a non-differentiable trajectory both
sides use the totalized derivative value and the equivalence still
holds. The physical reading is the classical one for a twice
differentiable trajectory.

For base motion, the influence vector `r` is prescribed and arbitrary:
entry `i` is the displacement of degree of freedom `i` under a unit
static base displacement. It is never normalized. The participation
factors are `Γ = (Φᵀ * M) *ᵥ r`, and with unit modal masses the effective
modal mass of mode `j` is `Γ j ^ 2`; these sum to the total mass
`r ⬝ᵥ (M *ᵥ r)` seen by the base motion. No division or inverse appears
in the participation statements.

For peak accounting over a finite horizon `[0, T]`, the reference
response `u j` of mode `j` is the unit-mass oscillator response
`u'' + (α + β * μ j) u' + μ j u = -ag t` from rest, for a supplied base
acceleration history `ag`. The modal correspondence `q j = Γ j * u j` on
`[0, T]` is an explicit input to the peak bound, not derived: deriving it
needs a uniqueness theorem for the forced oscillator, which is out of
scope. The oscillator equation and the rest initial data identify which
`u j` is meant; the bound uses only continuity of `u j` and the
correspondence, so they are not premises.

Exclusions: no decoupling for nonproportional damping, no indefinite
stiffness, and only the finite-horizon ABSSUM bound below: no SRSS/CQC,
infinite-time spectrum, statistical combination or code coefficient.

## ii. Key results

- `rayleighDamping`: the proportional damping matrix `α • M + β • K`.
- `transpose_mul_rayleighDamping_mul`: its modal transform is diagonal.
- `rayleigh_modal_decoupling`: the physical equation at `t` is equivalent
  to the decoupled modal equations at `t`.
- `exists_rayleigh_modal_decoupling`: for positive-definite mass,
  positive-semidefinite stiffness and `α, β ≥ 0`, the canonical modal
  basis has nonnegative modal damping and decouples every trajectory.
- `participation`: the participation factors `(Φᵀ * M) *ᵥ r`.
- `participation_sq_sum`: effective-mass completeness,
  `∑ j, Γ j ^ 2 = r ⬝ᵥ (M *ᵥ r)`.
- `mulVec_participation`: the factors reconstruct `r`, `Φ *ᵥ Γ = r`.
- `sum_participation_sq_lt_of_not_mem`: dropping a participating mode
  strictly loses effective mass.
- `spectralDisplacement`: peak reference displacement on `[0, T]`.
- `abs_modal_combination_le`: finite-horizon ABSSUM peak bound.

## iii. Table of contents

- A. Rayleigh damping and modal decoupling
- B. Base participation and effective modal mass
- C. Finite-horizon peak bound

## iv. References

- S. S. Rao, *Mechanical Vibrations*, 6th edition, Chapter 6
  (multidegree-of-freedom systems).
- D. J. Inman, *Engineering Vibration*, 4th edition, Chapter 4
  (multiple-degree-of-freedom systems, mass-normalized modes).
- A. K. Chopra, *Dynamics of Structures*, earthquake analysis of linear
  multidegree-of-freedom systems (participation factors and effective
  modal mass under unit modal masses).
- `PhyslibExt.Mechanics.ModalResponse`: the canonical modal basis.
-/

@[expose] public section

namespace PhyslibExt.Mechanics.RayleighModal

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## A. Rayleigh damping and modal decoupling -/

/-- Rayleigh (classical proportional) damping matrix `Cd = α • M + β • K`. -/
def rayleighDamping (α β : ℝ) (M K : Matrix n n ℝ) : Matrix n n ℝ :=
  α • M + β • K

/-- Damping transformation: in a mass-orthonormal basis that diagonalizes the stiffness,
the Rayleigh damping matrix becomes diagonal with modal damping coefficients
`α + β * μ j` (for an oscillatory mode `μ j > 0`, twice the modal damping ratio times
the modal frequency; a rigid mode has coefficient `α` and no damping ratio). Holds for
every real `α`, `β`; repeated `μ` values are allowed. -/
lemma transpose_mul_rayleighDamping_mul {M K Φ : Matrix n n ℝ} {μ : n → ℝ}
    (hMΦ : Φᵀ * M * Φ = 1) (hKΦ : Φᵀ * K * Φ = diagonal μ) (α β : ℝ) :
    Φᵀ * rayleighDamping α β M K * Φ = diagonal fun j => α + β * μ j := by
  have h1 : Φᵀ * rayleighDamping α β M K * Φ
      = α • (1 : Matrix n n ℝ) + β • diagonal μ := by
    unfold rayleighDamping
    rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
      smul_mul_assoc, hMΦ, hKΦ]
  rw [h1]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

private lemma deriv_unit_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (U : (Matrix n n ℝ)ˣ) (g : ℝ → n → ℝ) (t : ℝ) :
    deriv (fun s => (U : Matrix n n ℝ) *ᵥ g s) t
      = (U : Matrix n n ℝ) *ᵥ deriv g t := by
  set L : (n → ℝ) →L[ℝ] (n → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin (U : Matrix n n ℝ)) with hLdef
  have hL : ∀ v, L v = (U : Matrix n n ℝ) *ᵥ v := fun v => by
    rw [hLdef, LinearMap.coe_toContinuousLinearMap', Matrix.coe_mulVecLin]
  by_cases hg : DifferentiableAt ℝ g t
  · have h1 : HasFDerivAt g (fderiv ℝ g t) t := hg.hasFDerivAt
    have h2 : HasFDerivAt (fun v => (U : Matrix n n ℝ) *ᵥ v) L (g t) :=
      HasFDerivAt.congr_of_eventuallyEq L.hasFDerivAt
        (Filter.Eventually.of_forall fun v => (hL v).symm)
    have h3 := HasFDerivAt.comp t h2 h1
    have h1d : (fderiv ℝ g t) 1 = deriv g t := h1.hasDerivAt.deriv.symm
    calc deriv (fun s => (U : Matrix n n ℝ) *ᵥ g s) t
        = (L.comp (fderiv ℝ g t)) 1 := h3.hasDerivAt.deriv
      _ = L ((fderiv ℝ g t) 1) := rfl
      _ = L (deriv g t) := by rw [h1d]
      _ = (U : Matrix n n ℝ) *ᵥ deriv g t := hL _
  · have hnc : ¬ DifferentiableAt ℝ (fun s => (U : Matrix n n ℝ) *ᵥ g s) t := by
      intro hd
      apply hg
      set L' : (n → ℝ) →L[ℝ] (n → ℝ) := LinearMap.toContinuousLinearMap
        (Matrix.mulVecLin ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ)) with hL'def
      have hL' : ∀ v, L' v = ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) *ᵥ v :=
        fun v => by
          rw [hL'def, LinearMap.coe_toContinuousLinearMap', Matrix.coe_mulVecLin]
      have hd' : DifferentiableAt ℝ
          (fun v => ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) *ᵥ v)
          ((U : Matrix n n ℝ) *ᵥ g t) :=
        HasFDerivAt.differentiableAt (HasFDerivAt.congr_of_eventuallyEq L'.hasFDerivAt
          (Filter.Eventually.of_forall fun v => (hL' v).symm))
      have hcomp := DifferentiableAt.comp t hd' hd
      have heq : (fun v => ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) *ᵥ v)
          ∘ (fun s => (U : Matrix n n ℝ) *ᵥ g s) = g := by
        funext s
        show ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) *ᵥ
          ((U : Matrix n n ℝ) *ᵥ g s) = g s
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rwa [heq] at hcomp
    rw [deriv_zero_of_not_differentiableAt hnc, deriv_zero_of_not_differentiableAt hg,
      Matrix.mulVec_zero]

/-- Rayleigh-damped modal decoupling: for a complete mass-orthonormal basis `Φ` of the
pencil `(K, M)` with `Φᵀ * K * Φ = diagonal μ`, a trajectory `x` satisfies
`M x'' + (α M + β K) x' + K x = f` at time `t` iff its modal coordinates
`q = Φᵀ * M *ᵥ x` satisfy the decoupled equations
`(q'')_j + (α + β * μ j) (q')_j + μ j q_j = (Φᵀ *ᵥ f t) j` at `t`, for every mode `j`, where
`(q')_j` and `(q'')_j` are the `j`-th components of the derivatives of the vector `q` (each
derivative `0` where the function is not differentiable). Proportional damping only; holds for
every real `α`, `β` and any load `f`. -/
theorem rayleigh_modal_decoupling {M K Φ : Matrix n n ℝ} {μ : n → ℝ}
    (hMΦ : Φᵀ * M * Φ = 1) (hKΦ : Φᵀ * K * Φ = diagonal μ) (α β : ℝ)
    (x f : ℝ → n → ℝ) (t : ℝ) :
    M *ᵥ deriv (deriv x) t + rayleighDamping α β M K *ᵥ deriv x t + K *ᵥ x t = f t ↔
      ∀ j, deriv (deriv fun s => (Φᵀ * M) *ᵥ x s) t j +
          (α + β * μ j) * deriv (fun s => (Φᵀ * M) *ᵥ x s) t j +
          μ j * ((Φᵀ * M) *ᵥ x t) j = (Φᵀ *ᵥ f t) j := by
  have hΦA : Φ * (Φᵀ * M) = 1 := mul_eq_one_comm.mp hMΦ
  have hcomm1 : deriv (fun s => (Φᵀ * M) *ᵥ x s) t = (Φᵀ * M) *ᵥ deriv x t :=
    deriv_unit_mulVec ⟨Φᵀ * M, Φ, hMΦ, hΦA⟩ x t
  have hcomm2 : deriv (deriv fun s => (Φᵀ * M) *ᵥ x s) t
      = (Φᵀ * M) *ᵥ deriv (deriv x) t := by
    have hfun : deriv (fun s => (Φᵀ * M) *ᵥ x s)
        = fun _ => (Φᵀ * M) *ᵥ deriv x _ :=
      funext fun u => deriv_unit_mulVec ⟨Φᵀ * M, Φ, hMΦ, hΦA⟩ x u
    rw [hfun]
    exact deriv_unit_mulVec ⟨Φᵀ * M, Φ, hMΦ, hΦA⟩ (deriv x) t
  have hinsert : ∀ w : n → ℝ, Φ *ᵥ ((Φᵀ * M) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hΦA, Matrix.one_mulVec]
  have hdiag : Φᵀ * rayleighDamping α β M K * Φ
      = diagonal fun j => α + β * μ j :=
    transpose_mul_rayleighDamping_mul hMΦ hKΦ α β
  have hCd : ∀ (w : n → ℝ) (j : n),
      ((Φᵀ * rayleighDamping α β M K) *ᵥ w) j
        = (α + β * μ j) * ((Φᵀ * M) *ᵥ w) j := by
    intro w j
    conv_lhs => rw [← hinsert w]
    rw [Matrix.mulVec_mulVec, hdiag, Matrix.mulVec_diagonal]
  have hK : ∀ (w : n → ℝ) (j : n),
      ((Φᵀ * K) *ᵥ w) j = μ j * ((Φᵀ * M) *ᵥ w) j := by
    intro w j
    conv_lhs => rw [← hinsert w]
    rw [Matrix.mulVec_mulVec, hKΦ, Matrix.mulVec_diagonal]
  have hleft : (M * Φ) * Φᵀ = 1 := by
    have h1 : (Φ * Φᵀ) * M = 1 := by
      rw [Matrix.mul_assoc]
      exact hΦA
    have h2 : M * (Φ * Φᵀ) = 1 := mul_eq_one_comm.mp h1
    calc (M * Φ) * Φᵀ = M * (Φ * Φᵀ) := by rw [Matrix.mul_assoc]
      _ = 1 := h2
  have hinj : Function.Injective (Φᵀ *ᵥ ·) := by
    have hleftinv : Function.LeftInverse ((M * Φ) *ᵥ ·) (Φᵀ *ᵥ ·) := fun v => by
      show (M * Φ) *ᵥ (Φᵀ *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
    exact hleftinv.injective
  have hsplit : ∀ j, (Φᵀ *ᵥ (M *ᵥ deriv (deriv x) t
      + rayleighDamping α β M K *ᵥ deriv x t + K *ᵥ x t)) j
      = ((Φᵀ * M) *ᵥ deriv (deriv x) t) j
        + ((Φᵀ * rayleighDamping α β M K) *ᵥ deriv x t) j
        + ((Φᵀ * K) *ᵥ x t) j := by
    intro j
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Pi.add_apply, Pi.add_apply]
  have e1 : ∀ j, ((Φᵀ * M) *ᵥ deriv (deriv x) t) j
      = deriv (deriv fun s => (Φᵀ * M) *ᵥ x s) t j := by
    intro j
    rw [hcomm2]
  have e2 : ∀ j, ((Φᵀ * rayleighDamping α β M K) *ᵥ deriv x t) j
      = (α + β * μ j) * deriv (fun s => (Φᵀ * M) *ᵥ x s) t j := by
    intro j
    rw [hCd (deriv x t) j, ← hcomm1]
  constructor
  · intro h j
    have h2 := congrArg (fun v => (Φᵀ *ᵥ v) j) h
    rwa [hsplit j, e1 j, e2 j, hK (x t) j] at h2
  · intro h
    apply hinj
    funext j
    show (Φᵀ *ᵥ (M *ᵥ deriv (deriv x) t
      + rayleighDamping α β M K *ᵥ deriv x t + K *ᵥ x t)) j = (Φᵀ *ᵥ f t) j
    rw [hsplit j, e1 j, e2 j, hK (x t) j]
    exact h j

/-- Physical-to-canonical bridge: for a positive-definite mass `M`, a positive-semidefinite
stiffness `K` and Rayleigh coefficients `α, β ≥ 0`, the canonical modal-basis
theorem (`PhyslibExt.Mechanics.ModalResponse.exists_modalBasis`) yields an invertible
mass-orthonormal basis `Φ` with `Φᵀ * K * Φ = diagonal μ`, nonnegative `μ j` and
nonnegative modal damping `α + β * μ j`, in which every trajectory and load decouple as in
`rayleigh_modal_decoupling` (components of the derivatives of the vector `q`, each derivative `0`
where the function is not differentiable). Repeated eigenvalues and rigid modes (`μ j = 0`)
included. -/
theorem exists_rayleigh_modal_decoupling
    {M K : Matrix n n ℝ} (hM : M.PosDef) (hK : K.PosSemidef) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∃ (Φ : Matrix n n ℝ) (μ : n → ℝ), IsUnit Φ ∧ Φᵀ * M * Φ = 1 ∧
      Φᵀ * K * Φ = diagonal μ ∧ (∀ j, 0 ≤ μ j ∧ 0 ≤ α + β * μ j) ∧
      ∀ (x f : ℝ → n → ℝ) (t : ℝ),
        (M *ᵥ deriv (deriv x) t + rayleighDamping α β M K *ᵥ deriv x t + K *ᵥ x t = f t ↔
          ∀ j, deriv (deriv fun s => (Φᵀ * M) *ᵥ x s) t j +
              (α + β * μ j) * deriv (fun s => (Φᵀ * M) *ᵥ x s) t j +
              μ j * ((Φᵀ * M) *ᵥ x t) j = (Φᵀ *ᵥ f t) j) := by
  obtain ⟨C, hC, hMC, μ, hKC, hμ⟩ := PhyslibExt.Mechanics.ModalResponse.exists_modalBasis hM hK
  exact ⟨C, μ, hC, hMC, hKC,
    fun j => ⟨hμ j, add_nonneg hα (mul_nonneg hβ (hμ j))⟩,
    fun x f t => rayleigh_modal_decoupling hMC hKC α β x f t⟩

/-! ## B. Base participation and effective modal mass -/

/-- Modal participation factors of the base-influence vector `r` for
the modal matrix `Φ` and mass matrix `M`: `Γ = (Φᵀ * M) *ᵥ r`, so
`Γ j` is the mass-weighted projection of `r` on mode `j`. -/
def participation (M Φ : Matrix n n ℝ) (r : n → ℝ) : n → ℝ :=
  (Φᵀ * M) *ᵥ r

private lemma mul_reverse {M Φ : Matrix n n ℝ} (hMΦ : Φᵀ * M * Φ = 1) :
    Φ * (Φᵀ * M) = 1 :=
  mul_eq_one_comm.mp hMΦ

private lemma expand {M Φ : Matrix n n ℝ} (hMΦ : Φᵀ * M * Φ = 1) (r : n → ℝ) :
    Φ *ᵥ participation M Φ r = r := by
  unfold participation
  rw [Matrix.mulVec_mulVec, mul_reverse hMΦ, Matrix.one_mulVec]

/-- Effective-mass completeness: for a complete modal basis with unit
modal masses (`Φᵀ * M * Φ = 1`, `Φ` square), the effective modal masses
`Γ j ^ 2` of the prescribed base-influence vector `r` sum to the total
mass `r ⬝ᵥ (M *ᵥ r)` that the base motion sees. Valid for every such
`Φ`, including any mass-orthonormal choice inside a repeated
eigenvalue; no damping or spectrum enters. For the modal matrix of the
pencil `(K, M)`, `hMΦ` is discharged by the `Cᵀ * M * C = 1` conjunct of
`PhyslibExt.Mechanics.ModalResponse.exists_modalBasis hM hK`. -/
theorem participation_sq_sum {M Φ : Matrix n n ℝ}
    (hMΦ : Φᵀ * M * Φ = 1) (r : n → ℝ) :
    ∑ j, participation M Φ r j ^ 2 = r ⬝ᵥ (M *ᵥ r) := by
  have hexpand : Φ *ᵥ participation M Φ r = r := expand hMΦ r
  have hdot : ∀ Z : n → ℝ, (Φ *ᵥ participation M Φ r) ⬝ᵥ Z
      = participation M Φ r ⬝ᵥ (Φᵀ *ᵥ Z) := fun Z =>
    (dotProduct_comm _ _).trans
      (Matrix.dotProduct_transpose_mulVec Φ (participation M Φ r) Z).symm
  have hsum : ∑ j, participation M Φ r j ^ 2
      = participation M Φ r ⬝ᵥ participation M Φ r := by
    simp only [dotProduct, pow_two]
  have hmid : (Φ *ᵥ participation M Φ r) ⬝ᵥ (M *ᵥ (Φ *ᵥ participation M Φ r))
      = participation M Φ r ⬝ᵥ participation M Φ r := by
    rw [hdot, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMΦ, Matrix.one_mulVec]
  rw [hexpand] at hmid
  exact hsum.trans hmid.symm

/-- Modal expansion of the base-influence vector: for a complete modal
basis with unit modal masses, the participation factors reconstruct
the prescribed `r` exactly, `r = ∑ j, Γ j • (column j of Φ)`. -/
lemma mulVec_participation {M Φ : Matrix n n ℝ}
    (hMΦ : Φᵀ * M * Φ = 1) (r : n → ℝ) :
    Φ *ᵥ participation M Φ r = r := by
  exact expand hMΦ r

/-- Truncation loses mass: keeping only the modes in `s` of a complete
modal basis with unit modal masses gives a strictly smaller effective
mass than the total `r ⬝ᵥ (M *ᵥ r)` whenever some dropped mode `j ∉ s`
has nonzero participation. -/
lemma sum_participation_sq_lt_of_not_mem {M Φ : Matrix n n ℝ}
    (hMΦ : Φᵀ * M * Φ = 1) (r : n → ℝ) (s : Finset n) {j : n}
    (hj : j ∉ s) (hΓ : participation M Φ r j ≠ 0) :
    ∑ i ∈ s, participation M Φ r i ^ 2 < r ⬝ᵥ (M *ᵥ r) := by
  rw [← participation_sq_sum hMΦ r]
  have hpos : 0 < participation M Φ r j ^ 2 := sq_pos_iff.mpr hΓ
  refine Finset.sum_lt_sum_of_subset (Finset.subset_univ s) (Finset.mem_univ j) hj hpos ?_
  intro k _ _
  exact sq_nonneg _

/-! ## C. Finite-horizon peak bound -/

/-- Spectral displacement of a response `u` on the horizon `[0, T]`: the supremum of
`|u t|` over `t ∈ [0, T]`, a maximum for continuous `u` and `0 ≤ T`. By the real `sSup`
convention it is `0` for `T < 0` and when `|u|` is unbounded on `[0, T]`. -/
noncomputable def spectralDisplacement (T : ℝ) (u : ℝ → ℝ) : ℝ :=
  sSup ((fun t => |u t|) '' Set.Icc 0 T)

omit [DecidableEq n] in
/-- Finite-horizon absolute-sum peak bound: if each modal response satisfies the
correspondence `q j = Γ j * u j` on `[0, T]` with a continuous reference response `u j`
and participation factors `Γ`, then for every `t ∈ [0, T]` the combined response obeys
`|∑ j, c j * q j t| ≤ ∑ j, |c j * Γ j| * spectralDisplacement T (u j)`. -/
theorem abs_modal_combination_le {M Φ : Matrix n n ℝ} {r : n → ℝ} {T : ℝ}
    {u q : n → ℝ → ℝ} (c : n → ℝ)
    (hu : ∀ j, ContinuousOn (u j) (Set.Icc 0 T))
    (hq : ∀ j, ∀ t ∈ Set.Icc 0 T, q j t = participation M Φ r j * u j t)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    |∑ j, c j * q j t| ≤
      ∑ j, |c j * participation M Φ r j| * spectralDisplacement T (u j) := by
  have hle : ∀ j, |u j t| ≤ spectralDisplacement T (u j) := by
    intro j
    apply le_csSup
    · exact (isCompact_Icc.image_of_continuousOn (hu j).abs).bddAbove
    · exact ⟨t, ht, rfl⟩
  calc |∑ j, c j * q j t| ≤ ∑ j, |c j * q j t| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |c j * participation M Φ r j| * spectralDisplacement T (u j) := by
        apply Finset.sum_le_sum
        intro j _
        rw [hq j t ht, ← mul_assoc, abs_mul]
        exact mul_le_mul_of_nonneg_left (hle j) (abs_nonneg _)

end PhyslibExt.Mechanics.RayleighModal
