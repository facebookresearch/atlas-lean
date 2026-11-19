/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.TrussCompatibility
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import MathlibExt.LinearAlgebra.Matrix.FullRankLinearSystem
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith

/-!
# Determinate planar truss equilibrium

## i. Overview

Method-of-joints equilibrium for the axial-member table of
`PhyslibExt.Mechanics.HarmonicMechanics`: joints `J` at
positions `r`, members `M` with endpoints `a e`, `b e`, and a
support table `(sj, sd)`, where reaction component `s : R`
acts at joint `sj s` along direction `sd s`. The unknowns
are ordered `M ⊕ R`: member axial forces `N` (tension
positive), then reaction components `ρ`. The assembled
matrix is `[Bᵤᵀ | -Rsup]`, with `Bᵤ` the unit-direction
compatibility matrix, so every entry is a direction cosine
or a support-direction component and every unknown is a
force. `JointBalance` says that at each joint coordinate the
member forces on the joint, the reactions, and the external
load sum to zero; it is exactly `A *ᵥ Sum.elim N ρ = f`.
Determinacy is a unit determinant of the square matrix
obtained by renumbering equations with a supplied
`e : M ⊕ R ≃ J × Fin 2`, never a member count. A
zero-length member gives a zero unit column, so that
premise excludes it.

## ii. Key results

- `Mechanics.TrussEquilibrium.reactionMatrix`,
  `equilibriumMatrix`, `squareEquilibriumMatrix`: the
  support table and assembled matrices.
- `jointBalance_iff_mulVec`: joint balance is the
  assembled matrix equation.
- `jointBalance_iff_eq_inv`, `jointBalance_existsUnique`:
  with a unit determinant the balancing pair is unique and
  explicit.

## iii. Table of contents

- A. Support table and equilibrium matrices
- B. Joint-balance bridge
- C. Determinate solve

## iv. References

- R. C. Hibbeler, *Structural Analysis*, 10th edition,
  Pearson, 2017, Chapter 3 (method of joints).
- `PhyslibExt.Mechanics.TrussCompatibility` for the
  compatibility matrices and transpose force collection.
- `MathlibExt.LinearAlgebra.Matrix.FullRankLinearSystem`
  for the canonical square-system solve.
-/

@[expose] public section

open Matrix
open PhyslibExt.Mechanics.HarmonicMechanics
open Mechanics.TrussCompatibility

namespace Mechanics.TrussEquilibrium

/-! ## A. Support table and equilibrium matrices -/

/-- Support table as a matrix: column `s` is the direction
`sd s` placed at joint `sj s`. -/
def reactionMatrix {J R : Type*} [DecidableEq J]
    (sj : R → J) (sd : R → (Fin 2 → ℝ)) : Matrix (J × Fin 2) R ℝ :=
  Matrix.of fun q s => if sj s = q.1 then sd s q.2 else 0

/-- Assembled equilibrium matrix `[Bᵤᵀ | -Rsup]`: rows are
joint coordinates, columns are member forces then reaction
components. -/
noncomputable def equilibriumMatrix {J M R : Type*} [DecidableEq J]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (sj : R → J) (sd : R → (Fin 2 → ℝ)) :
    Matrix (J × Fin 2) (M ⊕ R) ℝ :=
  Matrix.fromCols (axialCompatibilityUnit r a b)ᵀ (-reactionMatrix sj sd)

/-- Square equilibrium matrix: equation `e u` is placed in
row `u`. -/
noncomputable def squareEquilibriumMatrix {J M R : Type*}
    [DecidableEq J] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (sj : R → J) (sd : R → (Fin 2 → ℝ)) (e : M ⊕ R ≃ J × Fin 2) :
    Matrix (M ⊕ R) (M ⊕ R) ℝ :=
  (equilibriumMatrix r a b sj sd).submatrix e id

/-- Method-of-joints balance: at every joint coordinate the
axial forces the members exert on the joint, the support
reactions at the joint, and the external load sum to
zero. -/
def JointBalance {J M R : Type*} [DecidableEq J] [Fintype M] [Fintype R]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (sj : R → J) (sd : R → (Fin 2 → ℝ))
    (f : J × Fin 2 → ℝ) (N : M → ℝ) (ρ : R → ℝ) : Prop :=
  ∀ (j : J) (k : Fin 2),
    (∑ p : M × Bool,
        if endpointJoint a b p = j then axialEndpointForce r a b N p k else 0)
      + (∑ s : R, if sj s = j then ρ s * sd s k else 0)
      + f (j, k) = 0

/-! ## B. Joint-balance bridge -/

/-- The support block acts as the support table. -/
lemma reactionMatrix_mulVec_apply {J R : Type*} [DecidableEq J] [Fintype R]
    (sj : R → J) (sd : R → (Fin 2 → ℝ)) (ρ : R → ℝ) (j : J) (k : Fin 2) :
    (reactionMatrix sj sd *ᵥ ρ) (j, k)
      = ∑ s : R, if sj s = j then ρ s * sd s k else 0 := by
  simp only [reactionMatrix, Matrix.mulVec, Matrix.of_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : sj s = j <;> simp [h, mul_comm]

/-- Conditional bridge: joint balance is the assembled
matrix equation, given canonical force collection. -/
private theorem jointBalance_iff_mulVec_of {J M R : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [Fintype R]
    (hcollect : ∀ (r : J → (Fin 2 → ℝ)) (a b : M → J) (N : M → ℝ)
        (j : J) (k : Fin 2),
      ((axialCompatibilityUnit r a b)ᵀ *ᵥ N) (j, k)
        = -(∑ p : M × Bool,
            if endpointJoint a b p = j
            then axialEndpointForce r a b N p k else 0))
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (sj : R → J) (sd : R → (Fin 2 → ℝ))
    (f : J × Fin 2 → ℝ) (N : M → ℝ) (ρ : R → ℝ) :
    JointBalance r a b sj sd f N ρ
      ↔ equilibriumMatrix r a b sj sd *ᵥ Sum.elim N ρ = f := by
  simp only [equilibriumMatrix, Matrix.fromCols_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, Matrix.neg_mulVec]
  constructor
  · intro h
    funext q
    obtain ⟨j, k⟩ := q
    have hjk := h j k
    rw [Pi.add_apply, Pi.neg_apply, hcollect r a b N j k,
      reactionMatrix_mulVec_apply sj sd ρ j k]
    linarith
  · intro h j k
    have hqk := congrFun h (j, k)
    rw [Pi.add_apply, Pi.neg_apply, hcollect r a b N j k,
      reactionMatrix_mulVec_apply sj sd ρ j k] at hqk
    linarith

/-- Joint balance is exactly the assembled equilibrium
equation `A *ᵥ Sum.elim N ρ = f`. -/
theorem jointBalance_iff_mulVec {J M R : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [Fintype R]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (sj : R → J) (sd : R → (Fin 2 → ℝ))
    (f : J × Fin 2 → ℝ) (N : M → ℝ) (ρ : R → ℝ) :
    JointBalance r a b sj sd f N ρ
      ↔ equilibriumMatrix r a b sj sd *ᵥ Sum.elim N ρ = f :=
  jointBalance_iff_mulVec_of
    (fun r a b N j k =>
      axialCompatibilityUnit_transpose_mulVec_apply r a b N j k)
    r a b sj sd f N ρ

/-! ## C. Determinate solve -/

/-- Conditional explicit solve, given canonical force
collection and the canonical inverse-solve equivalence. -/
private theorem jointBalance_iff_eq_inv_of {J M R : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype R] [DecidableEq R]
    (hcollect : ∀ (r : J → (Fin 2 → ℝ)) (a b : M → J) (N : M → ℝ)
        (j : J) (k : Fin 2),
      ((axialCompatibilityUnit r a b)ᵀ *ᵥ N) (j, k)
        = -(∑ p : M × Bool,
            if endpointJoint a b p = j
            then axialEndpointForce r a b N p k else 0))
    (hsolve : ∀ {A : Matrix (M ⊕ R) (M ⊕ R) ℝ}, IsUnit A.det →
      ∀ {g x : M ⊕ R → ℝ}, A *ᵥ x = g ↔ x = A⁻¹ *ᵥ g)
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (sj : R → J) (sd : R → (Fin 2 → ℝ)) (e : M ⊕ R ≃ J × Fin 2)
    (hdet : IsUnit (squareEquilibriumMatrix r a b sj sd e).det)
    (f : J × Fin 2 → ℝ) (N : M → ℝ) (ρ : R → ℝ) :
    JointBalance r a b sj sd f N ρ
      ↔ Sum.elim N ρ
          = (squareEquilibriumMatrix r a b sj sd e)⁻¹ *ᵥ (f ∘ e) := by
  have hsub : ∀ u : M ⊕ R,
      (squareEquilibriumMatrix r a b sj sd e *ᵥ Sum.elim N ρ) u
        = (equilibriumMatrix r a b sj sd *ᵥ Sum.elim N ρ) (e u) :=
    fun u => rfl
  rw [jointBalance_iff_mulVec_of hcollect, (hsolve hdet).symm]
  constructor
  · intro h
    funext u
    rw [hsub u]
    exact congrFun h (e u)
  · intro h
    funext q
    have h1 := congrFun h (e.symm q)
    rw [hsub (e.symm q), Equiv.apply_symm_apply e q] at h1
    have h2 : (f ∘ e) (e.symm q) = f q := by
      rw [Function.comp_apply, Equiv.apply_symm_apply]
    rw [h2] at h1
    exact h1

/-- With a unit determinant, `(N, ρ)` balances the joints
exactly when `Sum.elim N ρ = A⁻¹ *ᵥ (f ∘ e)`. -/
theorem jointBalance_iff_eq_inv {J M R : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype R] [DecidableEq R]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (sj : R → J) (sd : R → (Fin 2 → ℝ)) (e : M ⊕ R ≃ J × Fin 2)
    (hdet : IsUnit (squareEquilibriumMatrix r a b sj sd e).det)
    (f : J × Fin 2 → ℝ) (N : M → ℝ) (ρ : R → ℝ) :
    JointBalance r a b sj sd f N ρ
      ↔ Sum.elim N ρ
          = (squareEquilibriumMatrix r a b sj sd e)⁻¹ *ᵥ (f ∘ e) :=
  jointBalance_iff_eq_inv_of
    (fun r a b N j k =>
      axialCompatibilityUnit_transpose_mulVec_apply r a b N j k)
    (fun hA => Matrix.mulVec_eq_iff_inv_mulVec hA)
    r a b sj sd e hdet f N ρ

/-- Conditional unique balance, given canonical force
collection and the canonical inverse-solve equivalence. -/
private theorem jointBalance_existsUnique_of {J M R : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype R] [DecidableEq R]
    (hcollect : ∀ (r : J → (Fin 2 → ℝ)) (a b : M → J) (N : M → ℝ)
        (j : J) (k : Fin 2),
      ((axialCompatibilityUnit r a b)ᵀ *ᵥ N) (j, k)
        = -(∑ p : M × Bool,
            if endpointJoint a b p = j
            then axialEndpointForce r a b N p k else 0))
    (hsolve : ∀ {A : Matrix (M ⊕ R) (M ⊕ R) ℝ}, IsUnit A.det →
      ∀ {g x : M ⊕ R → ℝ}, A *ᵥ x = g ↔ x = A⁻¹ *ᵥ g)
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (sj : R → J) (sd : R → (Fin 2 → ℝ)) (e : M ⊕ R ≃ J × Fin 2)
    (hdet : IsUnit (squareEquilibriumMatrix r a b sj sd e).det)
    (f : J × Fin 2 → ℝ) :
    ∃! p : (M → ℝ) × (R → ℝ), JointBalance r a b sj sd f p.1 p.2 := by
  set x₀ : M ⊕ R → ℝ :=
    (squareEquilibriumMatrix r a b sj sd e)⁻¹ *ᵥ (f ∘ e) with hx₀
  refine ⟨(x₀ ∘ Sum.inl, x₀ ∘ Sum.inr), ?_, ?_⟩
  · change JointBalance r a b sj sd f (x₀ ∘ Sum.inl) (x₀ ∘ Sum.inr)
    rw [jointBalance_iff_eq_inv_of hcollect hsolve r a b sj sd e hdet f]
    funext u
    cases u <;> rfl
  · rintro ⟨N, ρ⟩ h
    rw [jointBalance_iff_eq_inv_of hcollect hsolve r a b sj sd e hdet f] at h
    have hN : N = x₀ ∘ Sum.inl := by
      funext m
      simpa using congrFun h (Sum.inl m)
    have hρ : ρ = x₀ ∘ Sum.inr := by
      funext s
      simpa using congrFun h (Sum.inr s)
    exact Prod.ext hN hρ

/-- Main result: with a unit determinant, exactly one
member-force and reaction pair balances the joints. -/
theorem jointBalance_existsUnique {J M R : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype R] [DecidableEq R]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (sj : R → J) (sd : R → (Fin 2 → ℝ)) (e : M ⊕ R ≃ J × Fin 2)
    (hdet : IsUnit (squareEquilibriumMatrix r a b sj sd e).det)
    (f : J × Fin 2 → ℝ) :
    ∃! p : (M → ℝ) × (R → ℝ), JointBalance r a b sj sd f p.1 p.2 :=
  jointBalance_existsUnique_of
    (fun r a b N j k =>
      axialCompatibilityUnit_transpose_mulVec_apply r a b N j k)
    (fun hA => Matrix.mulVec_eq_iff_inv_mulVec hA)
    r a b sj sd e hdet f

end Mechanics.TrussEquilibrium
