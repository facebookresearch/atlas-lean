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

The block elimination equivalence is the specialization of the
canonical block elimination equivalence
`MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv.elim_iff` to
`C = Bᵀ`, with the general Schur complement identified with the
symmetric one below. The Schur complement and its strict positivity are the
canonical ones from
`MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity`, and the
dissipation identity is the canonical Schur source energy identity
from `MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy`, which
supplies the retained source term `jI ⬝ᵥ (D⁻¹ *ᵥ jI)`.

## ii. Key results

- `block_solution_iff_reduced`: the full block system holds if and
  only if the reduced port equation holds together with interior
  reconstruction, derived from the canonical block elimination
  equivalence.
- The dissipation split, total dissipation equals reduced port
  dissipation plus the retained interior source term, is the
  canonical `dotProduct_fromBlocks_mulVec_eq_schur_add_source_of_interior`
  (and `dotProduct_fromBlocks_mulVec_eq_schur_of_interior_zero` for
  zero interior injection) from
  `MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy`, used directly.
- `kron_reduction_correct`: for a positive-definite conductance
  matrix, the Schur complement is positive definite and every full
  solution is a reduced solution with reconstruction and the
  corrected dissipation split.

## iii. Table of contents

- A. Block elimination and reconstruction
- B. Reindexing invariance and headline correctness

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
port equation with reconstruction, derived from the canonical
block elimination equivalence.
-/

@[expose] public section

open Matrix

namespace PhyslibExt.Circuits.KronPortReduction

open MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity
open MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy

/-- The full block system is equivalent to the reduced port equation
together with interior reconstruction. -/
theorem block_solution_iff_reduced {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) [Invertible D] (φP : m → ℝ) (φI : p → ℝ)
    (jP : m → ℝ) (jI : p → ℝ) :
    (A *ᵥ φP + B *ᵥ φI = jP ∧ Bᵀ *ᵥ φP + D *ᵥ φI = jI) ↔
      (schurComplement A B D *ᵥ φP = jP - B *ᵥ (D⁻¹ *ᵥ jI) ∧
        φI = D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP)) := by
  simpa only [MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv.schur,
    schurComplement] using
    MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv.elim_iff
      (A := A) (B := B) (C := Bᵀ) (D := D) (x := φP) (y := φI) (u := jP) (v := jI)

/-- A full solution induces the reduced port injection equation. -/
lemma reduced_injection_of_full_solution {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq p] (A : Matrix m m ℝ)
    (B : Matrix m p ℝ) (D : Matrix p p ℝ) [Invertible D] (φP : m → ℝ)
    (φI : p → ℝ) (jP : m → ℝ) (jI : p → ℝ) (hP : A *ᵥ φP + B *ᵥ φI = jP)
    (hI : Bᵀ *ᵥ φP + D *ᵥ φI = jI) :
    schurComplement A B D *ᵥ φP = jP - B *ᵥ (D⁻¹ *ᵥ jI) := by
  exact ((block_solution_iff_reduced A B D φP φI jP jI).mp ⟨hP, hI⟩).1

/-- Reconstruction from a reduced solution solves the full system. -/
lemma full_solution_of_reduced {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq p] (A : Matrix m m ℝ) (B : Matrix m p ℝ)
    (D : Matrix p p ℝ) [Invertible D] (φP : m → ℝ) (jP : m → ℝ) (jI : p → ℝ)
    (h : schurComplement A B D *ᵥ φP = jP - B *ᵥ (D⁻¹ *ᵥ jI)) :
    A *ᵥ φP + B *ᵥ (D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP)) = jP ∧
      Bᵀ *ᵥ φP + D *ᵥ (D⁻¹ *ᵥ (jI - Bᵀ *ᵥ φP)) = jI := by
  exact (block_solution_iff_reduced A B D φP _ jP jI).mpr ⟨h, rfl⟩

/-! ## B. Reindexing invariance and headline correctness

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
  · exact @reduced_injection_of_full_solution m p _ _ _ A B D hInv
      φP φI jP jI hP hI
  · exact ((@block_solution_iff_reduced m p _ _ _ A B D hInv φP φI jP jI).mp
      ⟨hP, hI⟩).2
  · exact
      @dotProduct_fromBlocks_mulVec_eq_schur_add_source_of_interior m p _ _ _ A B D hInv
        hSymm φP φI jI hI

end PhyslibExt.Circuits.KronPortReduction
