/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv

/-!
# Index-one elimination for a linear descriptor system

## i. Overview

Let `A`, `B`, `C` and `D` be finite real matrices of compatible
shapes, with `D` invertible, let `f` and `g` be time-dependent real
forcing vectors, and let `x` be a differentiable time-dependent
state vector while `y` is a time-dependent algebraic vector with no
differentiability requirement. The descriptor system
`deriv x t = A *ᵥ x t + B *ᵥ y t + f t` together with
`C *ᵥ x t + D *ᵥ y t + g t = 0` at every time `t` is equivalent to
the reduced system
`deriv x t = (A - B * D⁻¹ * C) *ᵥ x t + f t - B *ᵥ (D⁻¹ *ᵥ g t)`
together with the reconstruction
`y t = -(D⁻¹ *ᵥ (C *ᵥ x t + g t))` at every time `t`. A pair
`(x₀, y₀)` is a consistent initial pair for a forcing value `g₀`
exactly when `C *ᵥ x₀ + D *ᵥ y₀ + g₀ = 0`, equivalently when `y₀` is
the reconstruction from `x₀` and `g₀`. No statement is made when
`D` is singular, and no existence or uniqueness theorem for
trajectories is claimed.

The pointwise elimination multiplies the algebraic equation by
`D⁻¹`, using the block-elimination results of
`MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv`; the
trajectory equivalence then applies that pointwise step at every
time, sharing the differentiability hypothesis on `x` and imposing
no regularity on `y`, while the reduced differential equation is
obtained by substituting the reconstruction into the descriptor
equation and collecting the Schur-complement coefficient.

## ii. Key results

- `satisfiesDescriptorSystem_iff_satisfiesReducedSystem`: the
  descriptor system holds if and only if the Schur-reduced system
  and the reconstruction hold.
- `consistentPair_iff_eq_algebraicReconstruction`: a pair is
  consistent if and only if its algebraic component is the
  reconstruction from its state component.

## iii. Table of contents

- A. Reconstruction and reduced data
- B. Pointwise algebraic elimination
- C. Trajectory equivalence
- D. Validation boundaries

## iv. References

- P. Kunkel and V. Mehrmann, *Differential-Algebraic Equations:
  Analysis and Numerical Solution*, EMS Textbooks in Mathematics,
  European Mathematical Society, 2006: index-one descriptor
  systems and elimination of the algebraic variables through an
  invertible algebraic block.

## A. Reconstruction and reduced data
-/

@[expose] public section

open Matrix MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv

namespace PhyslibExt.Circuits.IndexOneElimination

/-- The algebraic vector reconstructed from a state `x` and an
algebraic forcing value `g`: `-(D⁻¹ *ᵥ (C *ᵥ x + g))`. -/
noncomputable def algebraicReconstruction {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (D : Matrix m m ℝ) [Invertible D] (C : Matrix m n ℝ) (x : n → ℝ) (g : m → ℝ) :
    m → ℝ :=
  -(D⁻¹ *ᵥ (C *ᵥ x + g))

/-- The reduced forcing of the differential equation:
`f - B *ᵥ (D⁻¹ *ᵥ g)`. -/
noncomputable def reducedForcing {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) (D : Matrix m m ℝ) [Invertible D] (f : n → ℝ) (g : m → ℝ) :
    n → ℝ :=
  f - B *ᵥ (D⁻¹ *ᵥ g)

/-- A pair `(x₀, y₀)` is consistent for the algebraic forcing value
`g₀` when `C *ᵥ x₀ + D *ᵥ y₀ + g₀ = 0`. -/
def consistentPair {n m : Type*} [Fintype n] [Fintype m]
    (C : Matrix m n ℝ) (D : Matrix m m ℝ) (g₀ : m → ℝ) (x₀ : n → ℝ) (y₀ : m → ℝ) :
    Prop :=
  C *ᵥ x₀ + D *ᵥ y₀ + g₀ = 0

/-- A trajectory pair satisfies the descriptor system when `x` is
differentiable and, at every time, the differential equation and the
algebraic equation both hold. No regularity is required of `y`. -/
def satisfiesDescriptorSystem {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    (f : ℝ → n → ℝ) (g : ℝ → m → ℝ)
    (x : ℝ → n → ℝ) (y : ℝ → m → ℝ) : Prop :=
  Differentiable ℝ x ∧
    (∀ t : ℝ, deriv x t = A *ᵥ x t + B *ᵥ y t + f t) ∧
    (∀ t : ℝ, C *ᵥ x t + D *ᵥ y t + g t = 0)

/-- A trajectory pair satisfies the reduced system when `x` is
differentiable and, at every time, the Schur-reduced differential
equation and the algebraic reconstruction both hold. -/
def satisfiesReducedSystem {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    [Invertible D] (f : ℝ → n → ℝ) (g : ℝ → m → ℝ)
    (x : ℝ → n → ℝ) (y : ℝ → m → ℝ) : Prop :=
  Differentiable ℝ x ∧
    (∀ t : ℝ, deriv x t =
      schur A B C D *ᵥ x t + reducedForcing B D (f t) (g t)) ∧
    (∀ t : ℝ, y t = algebraicReconstruction D C (x t) (g t))

/-! ### B. Pointwise algebraic elimination -/

/-- Any algebraic vector satisfying the algebraic equation is the
reconstruction from the state and the forcing value. This is the
reconstruction component of block elimination, applied with the
algebraic equation written as `C *ᵥ x + D *ᵥ y = -g`. -/
lemma eq_algebraicReconstruction_of_algebraicEquation
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D]
    (x : n → ℝ) (y : m → ℝ) (g : m → ℝ)
    (h : C *ᵥ x + D *ᵥ y + g = 0) :
    y = algebraicReconstruction D C x g := by
  have h2 : C *ᵥ x + D *ᵥ y = -g := eq_neg_of_add_eq_zero_left h
  have h1 : (0 : Matrix n n ℝ) *ᵥ x + (0 : Matrix n m ℝ) *ᵥ y = (0 : n → ℝ) := by
    simp
  obtain ⟨_, hyrec⟩ :=
    MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv.elim_forward h1 h2
  rw [hyrec]
  unfold algebraicReconstruction
  rw [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_add]
  abel

/-- The reconstruction always satisfies the algebraic equation. This
is the algebraic component of block reconstruction, applied with
forcing value `-g`. -/
lemma algebraicEquation_of_eq_algebraicReconstruction
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D]
    (x : n → ℝ) (y : m → ℝ) (g : m → ℝ)
    (h : y = algebraicReconstruction D C x g) :
    C *ᵥ x + D *ᵥ y + g = 0 := by
  have hschur : schur (0 : Matrix n n ℝ) (0 : Matrix n m ℝ) C D *ᵥ x
      = (0 : n → ℝ) - (0 : Matrix n m ℝ) *ᵥ (D⁻¹ *ᵥ (-g)) := by
    simp [schur]
  obtain ⟨_, halg⟩ :=
    MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv.elim_backward hschur
  have hyrec : D⁻¹ *ᵥ (-g - C *ᵥ x) = algebraicReconstruction D C x g := by
    unfold algebraicReconstruction
    rw [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_add]
    abel
  have hfinal : C *ᵥ x + D *ᵥ y = -g := by
    rwa [hyrec, ← h] at halg
  rw [hfinal]
  exact neg_add_cancel g

/-- **Consistent initial value, exactly.** A pair is consistent for
the forcing value `g₀` if and only if its algebraic component is the
reconstruction from its state component and `g₀`. -/
theorem consistentPair_iff_eq_algebraicReconstruction
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D]
    (g₀ : m → ℝ) (x₀ : n → ℝ) (y₀ : m → ℝ) :
    consistentPair C D g₀ x₀ y₀ ↔
      y₀ = algebraicReconstruction D C x₀ g₀ := by
  constructor
  · intro hc
    exact eq_algebraicReconstruction_of_algebraicEquation C D x₀ y₀ g₀ hc
  · intro he
    exact algebraicEquation_of_eq_algebraicReconstruction C D x₀ y₀ g₀ he

private lemma derivRHS_eq_reducedRHS
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    [Invertible D] (x : n → ℝ) (y : m → ℝ) (f : n → ℝ) (g : m → ℝ)
    (hy : y = algebraicReconstruction D C x g) :
    A *ᵥ x + B *ᵥ y + f = schur A B C D *ᵥ x + reducedForcing B D f g := by
  rw [hy]
  simp only [algebraicReconstruction, schur, reducedForcing, Matrix.sub_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_neg, Matrix.mulVec_add, Matrix.mul_assoc]
  abel

/-! ### C. Trajectory equivalence -/

/-- **Index-one reduction.** With invertible `D`, a trajectory pair
satisfies the descriptor system if and only if it satisfies the
Schur-reduced differential equation together with the algebraic
reconstruction at every time. -/
theorem satisfiesDescriptorSystem_iff_satisfiesReducedSystem
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    [Invertible D] (f : ℝ → n → ℝ) (g : ℝ → m → ℝ)
    (x : ℝ → n → ℝ) (y : ℝ → m → ℝ) :
    satisfiesDescriptorSystem A B C D f g x y ↔
      satisfiesReducedSystem A B C D f g x y := by
  unfold satisfiesDescriptorSystem satisfiesReducedSystem
  constructor
  · rintro ⟨hdiff, hde, halg⟩
    refine ⟨hdiff, ?_, ?_⟩
    · intro t
      have hy :=
        eq_algebraicReconstruction_of_algebraicEquation C D (x t) (y t) (g t) (halg t)
      have hde' := hde t
      rw [derivRHS_eq_reducedRHS A B C D (x t) (y t) (f t) (g t) hy] at hde'
      exact hde'
    · intro t
      exact eq_algebraicReconstruction_of_algebraicEquation C D (x t) (y t) (g t) (halg t)
  · rintro ⟨hdiff, hred, hrec⟩
    refine ⟨hdiff, ?_, ?_⟩
    · intro t
      have hred' := hred t
      rw [← derivRHS_eq_reducedRHS A B C D (x t) (y t) (f t) (g t) (hrec t)] at hred'
      exact hred'
    · intro t
      exact algebraicEquation_of_eq_algebraicReconstruction C D (x t) (y t) (g t) (hrec t)

/-- Forward direction, differential equation only: a descriptor
trajectory satisfies the reduced differential equation at every
time. -/
lemma reducedDerivativeEquation_of_satisfiesDescriptorSystem
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    [Invertible D] (f : ℝ → n → ℝ) (g : ℝ → m → ℝ)
    (x : ℝ → n → ℝ) (y : ℝ → m → ℝ)
    (h : satisfiesDescriptorSystem A B C D f g x y) (t : ℝ) :
    deriv x t = schur A B C D *ᵥ x t + reducedForcing B D (f t) (g t) := by
  have hred :=
    (satisfiesDescriptorSystem_iff_satisfiesReducedSystem A B C D f g x y).mp h
  unfold satisfiesReducedSystem at hred
  exact hred.2.1 t

/-- In a reduced trajectory, the algebraic component is the
reconstruction at every time. -/
lemma algebraicVariable_eq_reconstruction_of_satisfiesReducedSystem
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    [Invertible D] (f : ℝ → n → ℝ) (g : ℝ → m → ℝ)
    (x : ℝ → n → ℝ) (y : ℝ → m → ℝ)
    (h : satisfiesReducedSystem A B C D f g x y) (t : ℝ) :
    y t = algebraicReconstruction D C (x t) (g t) := by
  unfold satisfiesReducedSystem at h
  exact h.2.2 t

/-- Every value of a descriptor trajectory is a consistent pair for
the forcing value at that time. -/
lemma consistentPair_of_satisfiesDescriptorSystem
    {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    (f : ℝ → n → ℝ) (g : ℝ → m → ℝ)
    (x : ℝ → n → ℝ) (y : ℝ → m → ℝ)
    (h : satisfiesDescriptorSystem A B C D f g x y) (t₀ : ℝ) :
    consistentPair C D (g t₀) (x t₀) (y t₀) := by
  unfold satisfiesDescriptorSystem at h
  exact h.2.2 t₀

/-! ### D. Validation boundaries -/

/-- An algebraic value different from the reconstruction is not a
consistent partner for the state: inconsistent initial algebraic
values are excluded, they are not silently adjusted. -/
lemma not_consistentPair_of_ne_algebraicReconstruction
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D]
    (g₀ : m → ℝ) (x₀ : n → ℝ) (y₀ : m → ℝ)
    (h : y₀ ≠ algebraicReconstruction D C x₀ g₀) :
    ¬ consistentPair C D g₀ x₀ y₀ := by
  intro hc
  exact h ((consistentPair_iff_eq_algebraicReconstruction C D g₀ x₀ y₀).mp hc)

end PhyslibExt.Circuits.IndexOneElimination
