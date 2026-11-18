/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv
public import MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity
public import MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Kron reduction of a port network

## i. Overview

A real conductance matrix in block form `G = [[A, B], [Bᵀ, D]]`
splits its nodes into retained ports, indexed by `m`, and interior
nodes, indexed by `p`, which are to be eliminated. Kron reduction
replaces the full network by the Schur complement
`K = A - B * D⁻¹ * Bᵀ` acting on the ports alone. This module records
what the elimination preserves: a full solution restricts to a
reduced port solution, the interior potentials are recovered from
the ports by reconstruction, the total dissipation splits into the
reduced port dissipation plus a retained interior source term, and
relabeling the nodes does not change the dissipation. No nonlinear,
time-varying, or zero-admittance claim is made.

The block elimination equivalence is proved directly in this
module, by expanding the Schur complement and cancelling `D⁻¹`
against `D`; it is not obtained from a canonical block elimination
theorem. The Schur complement and its strict positivity are the
canonical ones from
`MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity`, and the
dissipation identity is the canonical Schur source energy identity
from `MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy`, which
supplies the retained source term `jI ⬝ᵥ (D⁻¹ *ᵥ jI)`.

## ii. Key results

- `block_solution_iff_reduced`: the full block system holds if and
  only if the reduced port equation holds together with interior
  reconstruction, proved directly in this module.
- `dissipation_eq_reduced_add_source`: total dissipation equals
  reduced port dissipation plus the retained interior source term,
  from the canonical Schur source energy identity.
- `kron_reduction_correct`: for a positive-definite conductance
  matrix, the Schur complement is positive definite and every full
  solution is a reduced solution with reconstruction and the
  corrected dissipation split.

## iii. Table of contents

- A. Block elimination and reconstruction
- B. Dissipation with the retained source
- C. Reindexing invariance and headline correctness

## iv. References

- G. Kron, "Numerical solution of ordinary and partial differential
  equations by means of equivalent circuits", *Journal of Applied
  Physics* 15(4), 1944, pp. 273-291: elimination of interior nodes
  of a network by equivalent circuits, the origin of Kron reduction.
- F. Zhang (ed.), *The Schur Complement and Its Applications*,
  Springer, 2005: the Schur complement, its block elimination
  identities and its positivity for positive-definite block
  matrices.

## A. Block elimination and reconstruction

The equivalence between the full block equations and the reduced
port equation with reconstruction, proved directly by expanding
the Schur complement.
-/

@[expose] public section

open Matrix

namespace PhyslibExt.Circuits.KronPortReduction

open MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity
open MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy

private theorem inv_mulVec_mulVec_cancel {p : Type*} [Fintype p] [DecidableEq p]
    (D : Matrix p p ℝ) [Invertible D] (x : p → ℝ) :
    D⁻¹ *ᵥ (D *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

private theorem mulVec_inv_mulVec_cancel {p : Type*} [Fintype p] [DecidableEq p]
    (D : Matrix p p ℝ) [Invertible D] (x : p → ℝ) :
    D *ᵥ (D⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

private theorem schur_mulVec_expand {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) [Invertible D] (φP : m → ℝ) :
    schurComplement A B D *ᵥ φP = A *ᵥ φP - B *ᵥ (D⁻¹ *ᵥ (Bᵀ *ᵥ φP)) := by
  unfold schurComplement
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- The full block system is equivalent to the reduced port equation
together with interior reconstruction. -/
theorem block_solution_iff_reduced {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) [Invertible D] (φP : m → ℝ) (φI : p → ℝ)
    (jP : m → ℝ) (jI : p → ℝ) :
    (A *ᵥ φP + B *ᵥ φI = jP ∧ Bᵀ *ᵥ φP + D *ᵥ φI = jI) ↔
      (schurComplement A B D *ᵥ φP = jP - B *ᵥ (D⁻¹ *ᵥ jI) ∧
        φI = D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP)) := by
  constructor
  · intro h
    obtain ⟨hP, hI⟩ := h
    have hDφI : D *ᵥ φI = jI - Bᵀ *ᵥ φP := by
      rw [← hI]; abel
    have hφI : φI = D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP) := by
      have h1 : D⁻¹ *ᵥ (D *ᵥ φI) = D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP) := by
        rw [hDφI]
      rw [inv_mulVec_mulVec_cancel] at h1
      exact h1
    have hBφI : B *ᵥ φI = B *ᵥ (D⁻¹ *ᵥ jI) - B *ᵥ (D⁻¹ *ᵥ (Bᵀ *ᵥ φP)) := by
      rw [hφI]; simp only [Matrix.mulVec_sub]
    refine ⟨?_, hφI⟩
    rw [schur_mulVec_expand, ← hP, hBφI]
    abel
  · intro h
    obtain ⟨hRed, hRec⟩ := h
    have hRed' : A *ᵥ φP - B *ᵥ (D⁻¹ *ᵥ (Bᵀ *ᵥ φP))
        = jP - B *ᵥ (D⁻¹ *ᵥ jI) := by
      rw [← hRed, schur_mulVec_expand]
    have hA : A *ᵥ φP
        = jP - B *ᵥ (D⁻¹ *ᵥ jI) + B *ᵥ (D⁻¹ *ᵥ (Bᵀ *ᵥ φP)) := by
      rw [← hRed']; abel
    refine ⟨?_, ?_⟩
    · rw [hRec]; simp only [Matrix.mulVec_sub]; rw [hA]; abel
    · rw [hRec, mulVec_inv_mulVec_cancel]; abel

/-- A full solution induces the reduced port injection equation. -/
lemma reduced_injection_of_full_solution {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq m] [DecidableEq p] (A : Matrix m m ℝ)
    (B : Matrix m p ℝ) (D : Matrix p p ℝ) [Invertible D] (φP : m → ℝ)
    (φI : p → ℝ) (jP : m → ℝ) (jI : p → ℝ) (hP : A *ᵥ φP + B *ᵥ φI = jP)
    (hI : Bᵀ *ᵥ φP + D *ᵥ φI = jI) :
    schurComplement A B D *ᵥ φP = jP - B *ᵥ (D⁻¹ *ᵥ jI) := by
  exact ((block_solution_iff_reduced A B D φP φI jP jI).mp ⟨hP, hI⟩).1

/-- Reconstruction from a reduced solution solves the full system. -/
lemma full_solution_of_reduced {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) [Invertible D] (φP : m → ℝ) (jP : m → ℝ) (jI : p → ℝ)
    (h : schurComplement A B D *ᵥ φP = jP - B *ᵥ (D⁻¹ *ᵥ jI)) :
    A *ᵥ φP + B *ᵥ (D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP)) = jP ∧
      Bᵀ *ᵥ φP + D *ᵥ (D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP)) = jI := by
  exact (block_solution_iff_reduced A B D φP _ jP jI).mpr ⟨h, rfl⟩

/-! ## B. Dissipation with the retained source

The corrected dissipation split, from the canonical Schur source
energy identity. -/

/-- Corrected dissipation: total dissipation equals reduced port
dissipation plus the retained interior source term. -/
theorem dissipation_eq_reduced_add_source {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq m] [DecidableEq p] (A : Matrix m m ℝ)
    (B : Matrix m p ℝ) (D : Matrix p p ℝ) [Invertible D]
    (hG : (fromBlocks A B Bᵀ D).IsSymm) (φP : m → ℝ) (φI : p → ℝ)
    (jI : p → ℝ) (hI : Bᵀ *ᵥ φP + D *ᵥ φI = jI) :
    (φP ⊕ᵥ φI) ⬝ᵥ (fromBlocks A B Bᵀ D *ᵥ (φP ⊕ᵥ φI)) =
      φP ⬝ᵥ (schurComplement A B D *ᵥ φP) + jI ⬝ᵥ (D⁻¹ *ᵥ jI) :=
  dotProduct_fromBlocks_mulVec_eq_schur_add_source_of_interior A B D hG φP φI jI hI

/-- Source-free dissipation: zero interior injection drops the offset. -/
lemma dissipation_eq_reduced_of_zero_interior {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq m] [DecidableEq p] (A : Matrix m m ℝ)
    (B : Matrix m p ℝ) (D : Matrix p p ℝ) [Invertible D]
    (hG : (fromBlocks A B Bᵀ D).IsSymm) (φP : m → ℝ) (φI : p → ℝ)
    (hI : Bᵀ *ᵥ φP + D *ᵥ φI = 0) :
    (φP ⊕ᵥ φI) ⬝ᵥ (fromBlocks A B Bᵀ D *ᵥ (φP ⊕ᵥ φI)) =
      φP ⬝ᵥ (schurComplement A B D *ᵥ φP) :=
  dotProduct_fromBlocks_mulVec_eq_schur_of_interior_zero A B D hG φP φI hI

/-! ## C. Reindexing invariance and headline correctness

Relabeling invariance of the dissipation, and the headline
correctness statement for a positive-definite conductance matrix. -/

/-- Relabelling invariance of dissipation under an index equivalence. -/
lemma dissipation_reindex_invariant {m p α : Type*} [Fintype m] [Fintype p]
    [Fintype α] [DecidableEq m] [DecidableEq p] [DecidableEq α]
    (e : α ≃ (m ⊕ p)) (G : Matrix (m ⊕ p) (m ⊕ p) ℝ) (φ j : m ⊕ p → ℝ)
    (h : G *ᵥ φ = j) :
    (fun a => φ (e a)) ⬝ᵥ (reindex e.symm e.symm G *ᵥ (fun a => φ (e a))) = φ ⬝ᵥ j := by
  have hmv : reindex e.symm e.symm G *ᵥ (fun a => φ (e a))
      = fun a => (G *ᵥ φ) (e a) := by
    ext a
    change (∑ b, (reindex e.symm e.symm G) a b * φ (e b))
      = (G *ᵥ φ) (e a)
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    exact Equiv.sum_comp e (fun b => G (e a) b * φ b)
  rw [hmv, ← h]
  exact Equiv.sum_comp e (fun b => φ b * (G *ᵥ φ) b)

/-- Headline correctness: for a positive-definite conductance matrix,
the Schur complement is positive definite and every full solution is
exactly a reduced solution with reconstruction and corrected
dissipation. -/
theorem kron_reduction_correct {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) (hG : (fromBlocks A B Bᵀ D).PosDef)
    (φP : m → ℝ) (φI : p → ℝ) (jP : m → ℝ) (jI : p → ℝ)
    (hP : A *ᵥ φP + B *ᵥ φI = jP) (hI : Bᵀ *ᵥ φP + D *ᵥ φI = jI) :
    (schurComplement A B D).PosDef ∧
      schurComplement A B D *ᵥ φP = jP - B *ᵥ (D⁻¹ *ᵥ jI) ∧
      φI = D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP) ∧
      (φP ⊕ᵥ φI) ⬝ᵥ (fromBlocks A B Bᵀ D *ᵥ (φP ⊕ᵥ φI)) =
        φP ⬝ᵥ (schurComplement A B D *ᵥ φP) + jI ⬝ᵥ (D⁻¹ *ᵥ jI) := by
  have hD : D.PosDef := interior_posDef hG
  have hInv : Invertible D := hD.isUnit.invertible
  have hS : (schurComplement A B D).PosDef := schurComplement_posDef hG
  have hSymm : (fromBlocks A B Bᵀ D).IsSymm := hG.isHermitian.isSymm
  refine ⟨hS, ?_, ?_, ?_⟩
  · exact @reduced_injection_of_full_solution m p _ _ _ _ A B D hInv
      φP φI jP jI hP hI
  · exact ((@block_solution_iff_reduced m p _ _ _ _ A B D hInv φP φI jP jI).mp
      ⟨hP, hI⟩).2
  · exact
      @dotProduct_fromBlocks_mulVec_eq_schur_add_source_of_interior m p _ _ _ A B D hInv
        hSymm φP φI jI hI

end PhyslibExt.Circuits.KronPortReduction
