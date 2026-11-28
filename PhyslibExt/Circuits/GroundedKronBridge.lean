/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.GroundedNodalConductance
public import PhyslibExt.Circuits.KronPortReduction

/-!
# Kron reduction of a grounded positive-resistance network

## i. Overview

A linear resistor network on nodes `Fin nN` has branches `Fin nB`
with endpoints `tail e`, `head e`; the resistor branches `Rset`
carry resistances `Rval e > 0`, and the undirected graph they
generate is connected. Its nodal conductance matrix is the merged
MNA stamp `G = Br diag(1 / R) Brᵀ` on the tail-positive incidence
`Br`. One node, `ground`, is held at potential `0`; external
currents `j v` are injected at the other nodes, and Kirchhoff's
current law reads `(G φ) v = j v` for every `v ≠ ground` (the
ground row carries the return current).

The non-ground nodes are split into retained ports `m` and
interior nodes `p` by a relabelling `σ : m ⊕ p ≃ {v // v ≠ ground}`.
In that order the grounded matrix is the block matrix
`[[A, B], [Bᵀ, D]]`, and Kron reduction replaces the network seen
from the ports by the Schur complement `K = A - B D⁻¹ Bᵀ`. The
positivity of the grounded matrix is not assumed: it comes from
`nodalConductance_grounded_posDef` (positive resistances plus a
connected resistor graph), and the Kron consumer
`kron_reduction_correct` does the rest. Then:

- `K` is symmetric positive definite (in particular the interior
  block `D` is invertible);
- every grounded network solution satisfies the reduced port law
  `K φP = jP - B D⁻¹ jI` and the interior reconstruction
  `φI = D⁻¹ (jI - Bᵀ φP)`, and conversely these two equations give
  a grounded network solution;
- the total resistor dissipation
  `Σ_{e ∈ Rset} (φ(tail e) - φ(head e))² / R e` equals the reduced
  port dissipation `φP ⬝ K φP` plus the retained interior source
  term `jI ⬝ D⁻¹ jI`.

No division through a zero admittance, nonlinear device, or
time-varying element is claimed.

## ii. Key results

- `fromBlocks_portBlock_couplingBlock`: the relabelled grounded
  matrix is the symmetric block matrix `[[A, B], [Bᵀ, D]]`.
- `portInteriorConductance_posDef`: the grounded network provider,
  relabelled.
- `stampQuadratic_eq_blockQuadratic`, `groundedKCL_iff_blocks`: the
  stamped quadratic form `Σ (Δφ)² / R` and the stamped grounded nodal
  equations in block form, for any resistance values. These are
  totalized stamp identities: a resistance value `0` is stamped with
  conductance `0⁻¹ = 0`, an open branch rather than a short, so the
  quadratic form is the resistor dissipation, and the equations are
  Kirchhoff's current law, only when every resistance is positive.
- `groundedKron_correct`: positive definiteness of `K`, the reduced
  port law, reconstruction, and the corrected dissipation split.
- `groundedKCL_iff_reduced`: the converse, a grounded network
  solution is exactly a reduced solution with reconstruction.

## iii. Table of contents

- A. Port/interior blocks of the grounded nodal conductance matrix
- B. Dissipation and the grounded network equations in block form
- C. Kron reduction of the grounded network

## iv. References

- G. Kron, "Numerical solution of ordinary and partial differential
  equations by means of equivalent circuits", *Journal of Applied
  Physics* 16(3), 1945, pp. 172-186, DOI 10.1063/1.1707568.
- F. Zhang (ed.), *The Schur Complement and Its Applications*,
  Springer, 2005.
- F. Dörfler and F. Bullo, "Kron reduction of graphs with
  applications to electrical networks", *IEEE Transactions on
  Circuits and Systems I* 60(1), 2013, pp. 150-163.
-/

@[expose] public section

open Matrix

namespace PhyslibExt.Circuits.GroundedKronBridge

open MathlibExt.Combinatorics.Graph.ArcNetwork
  MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian
  MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity
  PhyslibExt.Circuits.LinearMNAStamping
  PhyslibExt.Circuits.GroundedNodalConductance
  PhyslibExt.Circuits.KronPortReduction

/-! ## A. Port/interior blocks of the grounded nodal conductance matrix -/

/-- The grounded nodal conductance matrix with the non-ground nodes relabelled by `σ` as retained
ports `m` followed by interior nodes `p`. -/
noncomputable def portInteriorConductance {nN nB : ℕ} {m p : Type*} {ground : Fin nN}
    (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ)
    (σ : m ⊕ p ≃ {v // v ≠ ground}) : Matrix (m ⊕ p) (m ⊕ p) ℝ :=
  (nodalConductance (physicalIncidence tail head) Rset Rval).submatrix
    (fun i => (σ i : Fin nN)) (fun i => (σ i : Fin nN))

/-- The port block `A` of the relabelled grounded conductance matrix. -/
noncomputable def portBlock {nN nB : ℕ} {m p : Type*} {ground : Fin nN}
    (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ)
    (σ : m ⊕ p ≃ {v // v ≠ ground}) : Matrix m m ℝ :=
  (portInteriorConductance tail head Rset Rval σ).toBlocks₁₁

/-- The port-interior coupling block `B` of the relabelled grounded conductance matrix. -/
noncomputable def couplingBlock {nN nB : ℕ} {m p : Type*} {ground : Fin nN}
    (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ)
    (σ : m ⊕ p ≃ {v // v ≠ ground}) : Matrix m p ℝ :=
  (portInteriorConductance tail head Rset Rval σ).toBlocks₁₂

/-- The interior block `D` of the relabelled grounded conductance matrix. -/
noncomputable def interiorBlock {nN nB : ℕ} {m p : Type*} {ground : Fin nN}
    (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ)
    (σ : m ⊕ p ≃ {v // v ≠ ground}) : Matrix p p ℝ :=
  (portInteriorConductance tail head Rset Rval σ).toBlocks₂₂

/-- The Kron-reduced port conductance matrix `K = A - B D⁻¹ Bᵀ`. It is defined for any
resistance values, with Mathlib's matrix inverse, which is `0` on a singular matrix; it is the
Kron elimination of the interior nodes only when the interior block `D` is invertible, as it is
for positive resistances on a connected resistor graph (`groundedKron_correct`). -/
noncomputable def kronConductance {nN nB : ℕ} {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq p] {ground : Fin nN} (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB))
    (Rval : Fin nB → ℝ) (σ : m ⊕ p ≃ {v // v ≠ ground}) : Matrix m m ℝ :=
  schurComplement (portBlock tail head Rset Rval σ) (couplingBlock tail head Rset Rval σ)
    (interiorBlock tail head Rset Rval σ)

/-- The port entries `x (σ (inl i))` of a node vector. -/
def portPart {nN : ℕ} {m p : Type*} {ground : Fin nN} (σ : m ⊕ p ≃ {v // v ≠ ground})
    (x : Fin nN → ℝ) : m → ℝ :=
  fun i => x (σ (Sum.inl i) : Fin nN)

/-- The interior entries `x (σ (inr k))` of a node vector. -/
def interiorPart {nN : ℕ} {m p : Type*} {ground : Fin nN} (σ : m ⊕ p ≃ {v // v ≠ ground})
    (x : Fin nN → ℝ) : p → ℝ :=
  fun k => x (σ (Sum.inr k) : Fin nN)

private theorem nodalConductance_transpose {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ) :
    (nodalConductance B Rset Rval)ᵀ = nodalConductance B Rset Rval := by
  simp [nodalConductance, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]

private theorem sumElim_parts {nN : ℕ} {m p : Type*} {ground : Fin nN}
    (σ : m ⊕ p ≃ {v // v ≠ ground}) (x : Fin nN → ℝ) :
    portPart σ x ⊕ᵥ interiorPart σ x = fun i => x (σ i : Fin nN) := by
  funext i
  rcases i with i | k <;> rfl

private theorem portInteriorConductance_mulVec {nN nB : ℕ} {m p : Type*} [Fintype m]
    [Fintype p] {ground : Fin nN} (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB))
    (Rval : Fin nB → ℝ) (σ : m ⊕ p ≃ {v // v ≠ ground}) (φ : Fin nN → ℝ)
    (hground : φ ground = 0) :
    portInteriorConductance tail head Rset Rval σ *ᵥ (fun i => φ (σ i : Fin nN)) =
      fun i => (nodalConductance (physicalIncidence tail head) Rset Rval *ᵥ φ) (σ i : Fin nN) := by
  funext i
  simp only [portInteriorConductance, mulVec, dotProduct, submatrix_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun v => nodalConductance (physicalIncidence tail head) Rset Rval (σ i : Fin nN) v * φ v)
    ground, hground, mul_zero, zero_add]
  exact Equiv.sum_comp σ
    (fun w => nodalConductance (physicalIncidence tail head) Rset Rval (σ i : Fin nN) w * φ w)

/-- The relabelled grounded conductance matrix is the symmetric block matrix
`[[A, B], [Bᵀ, D]]`, for any resistance values. -/
theorem fromBlocks_portBlock_couplingBlock {nN nB : ℕ} {m p : Type*} {ground : Fin nN}
    (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ)
    (σ : m ⊕ p ≃ {v // v ≠ ground}) :
    fromBlocks (portBlock tail head Rset Rval σ) (couplingBlock tail head Rset Rval σ)
        (couplingBlock tail head Rset Rval σ)ᵀ (interiorBlock tail head Rset Rval σ) =
      portInteriorConductance tail head Rset Rval σ := by
  have hsym := nodalConductance_transpose (physicalIncidence tail head) Rset Rval
  have h21 : (portInteriorConductance tail head Rset Rval σ).toBlocks₁₂ᵀ =
      (portInteriorConductance tail head Rset Rval σ).toBlocks₂₁ := by
    ext k i
    have h := congrFun (congrFun hsym (σ (Sum.inl i) : Fin nN)) (σ (Sum.inr k) : Fin nN)
    simp only [transpose_apply] at h
    simp only [transpose_apply, toBlocks₁₂, toBlocks₂₁, portInteriorConductance, of_apply,
      submatrix_apply]
    exact h.symm
  rw [couplingBlock, h21, portBlock, interiorBlock, fromBlocks_toBlocks]

/-- The grounded network provider, relabelled: positive resistances and a connected resistor
graph make the port/interior block matrix positive definite. -/
theorem portInteriorConductance_posDef {nN nB : ℕ} {m p : Type*} [Fintype m] [Fintype p]
    (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ)
    (hR : ∀ e ∈ Rset, 0 < Rval e) (ground : Fin nN)
    (hconn : (resistorGraph tail head Rset).Connected) (σ : m ⊕ p ≃ {v // v ≠ ground}) :
    (portInteriorConductance tail head Rset Rval σ).PosDef := by
  exact (nodalConductance_grounded_posDef tail head Rset Rval hR ground hconn).submatrix
    σ.injective

/-! ## B. Dissipation and the grounded network equations in block form -/

/-- **Totalized stamp identity for the dissipation.** For any resistance values, the stamped
quadratic form `Σ_{e ∈ Rset} (φ(tail e) - φ(head e))² / R e` of a grounded potential is the block
quadratic form of the relabelled grounded conductance matrix. Division is Lean's, so a branch
with resistance value `0` contributes `0`, as an open branch would, while a physical short would
force equal endpoint potentials; the sum is the resistor dissipation only when every resistance
in `Rset` is positive, as in `groundedKron_correct`. -/
theorem stampQuadratic_eq_blockQuadratic {nN nB : ℕ} {m p : Type*} [Fintype m]
    [Fintype p] (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ)
    (ground : Fin nN) (σ : m ⊕ p ≃ {v // v ≠ ground}) (φ : Fin nN → ℝ)
    (hground : φ ground = 0) :
    ∑ e ∈ Rset, (φ (tail e) - φ (head e)) ^ 2 / Rval e =
      (portPart σ φ ⊕ᵥ interiorPart σ φ) ⬝ᵥ
        (fromBlocks (portBlock tail head Rset Rval σ) (couplingBlock tail head Rset Rval σ)
            (couplingBlock tail head Rset Rval σ)ᵀ (interiorBlock tail head Rset Rval σ) *ᵥ
          (portPart σ φ ⊕ᵥ interiorPart σ φ)) := by
  rw [fromBlocks_portBlock_couplingBlock, sumElim_parts σ φ,
    portInteriorConductance_mulVec tail head Rset Rval σ φ hground]
  have hdot : (fun i => φ (σ i : Fin nN)) ⬝ᵥ
      (fun i => (nodalConductance (physicalIncidence tail head) Rset Rval *ᵥ φ) (σ i : Fin nN)) =
      φ ⬝ᵥ (nodalConductance (physicalIncidence tail head) Rset Rval *ᵥ φ) := by
    simp only [dotProduct]
    rw [Equiv.sum_comp σ (fun w : {v // v ≠ ground} =>
      φ w * (nodalConductance (physicalIncidence tail head) Rset Rval *ᵥ φ) w)]
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun v => φ v * (nodalConductance (physicalIncidence tail head) Rset Rval *ᵥ φ) v) ground,
      hground, zero_mul, zero_add]
  rw [hdot, nodalConductance_physicalIncidence_eq, dotProduct_weightedLaplacian_mulVec,
    ← Finset.sum_coe_sort Rset]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [div_eq_inv_mul]
  ring

/-- The stamped nodal equations `(G φ) v = j v` at every non-ground node of a grounded potential
are the block system `A φP + B φI = jP`, `Bᵀ φP + D φI = jI`, for any resistance values. They are
Kirchhoff's current law for the resistor network when every resistance is positive; a
resistance value `0` is stamped with conductance `0⁻¹ = 0`, as an open branch. -/
theorem groundedKCL_iff_blocks {nN nB : ℕ} {m p : Type*} [Fintype m] [Fintype p]
    (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ)
    (ground : Fin nN) (σ : m ⊕ p ≃ {v // v ≠ ground}) (φ j : Fin nN → ℝ)
    (hground : φ ground = 0) :
    (∀ v, v ≠ ground →
        (nodalConductance (physicalIncidence tail head) Rset Rval *ᵥ φ) v = j v) ↔
      (portBlock tail head Rset Rval σ *ᵥ portPart σ φ +
            couplingBlock tail head Rset Rval σ *ᵥ interiorPart σ φ = portPart σ j ∧
        (couplingBlock tail head Rset Rval σ)ᵀ *ᵥ portPart σ φ +
            interiorBlock tail head Rset Rval σ *ᵥ interiorPart σ φ = interiorPart σ j) := by
  have hmv := portInteriorConductance_mulVec tail head Rset Rval σ φ hground
  rw [← fromBlocks_portBlock_couplingBlock tail head Rset Rval σ, ← sumElim_parts σ φ,
    fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr] at hmv
  constructor
  · intro h
    have hj : (fun i => (nodalConductance (physicalIncidence tail head) Rset Rval *ᵥ φ)
        (σ i : Fin nN)) = portPart σ j ⊕ᵥ interiorPart σ j := by
      rw [sumElim_parts σ j]
      funext i
      exact h _ (σ i).2
    rw [hj] at hmv
    exact Sum.elim_eq_iff.mp hmv
  · rintro ⟨h1, h2⟩ v hv
    have hfull : (fun i => (nodalConductance (physicalIncidence tail head) Rset Rval *ᵥ φ)
        (σ i : Fin nN)) = portPart σ j ⊕ᵥ interiorPart σ j := by
      rw [← hmv, h1, h2]
    have h := congrFun hfull (σ.symm ⟨v, hv⟩)
    rw [sumElim_parts σ j] at h
    simpa using h

/-! ## C. Kron reduction of the grounded network -/

/-- **Kron reduction of a grounded positive-resistance network.** For positive resistances and a
connected resistor graph, the Kron-reduced port conductance matrix is positive definite, and
every grounded network solution satisfies the reduced port law, the interior reconstruction,
and the corrected dissipation split. -/
theorem groundedKron_correct {nN nB : ℕ} {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB))
    (Rval : Fin nB → ℝ) (hR : ∀ e ∈ Rset, 0 < Rval e) (ground : Fin nN)
    (hconn : (resistorGraph tail head Rset).Connected) (σ : m ⊕ p ≃ {v // v ≠ ground})
    (φ j : Fin nN → ℝ) (hground : φ ground = 0)
    (hKCL : ∀ v, v ≠ ground →
      (nodalConductance (physicalIncidence tail head) Rset Rval *ᵥ φ) v = j v) :
    (kronConductance tail head Rset Rval σ).PosDef ∧
      kronConductance tail head Rset Rval σ *ᵥ portPart σ φ =
        portPart σ j - couplingBlock tail head Rset Rval σ *ᵥ
          ((interiorBlock tail head Rset Rval σ)⁻¹ *ᵥ interiorPart σ j) ∧
      interiorPart σ φ = (interiorBlock tail head Rset Rval σ)⁻¹ *ᵥ
        (interiorPart σ j - (couplingBlock tail head Rset Rval σ)ᵀ *ᵥ portPart σ φ) ∧
      ∑ e ∈ Rset, (φ (tail e) - φ (head e)) ^ 2 / Rval e =
        portPart σ φ ⬝ᵥ (kronConductance tail head Rset Rval σ *ᵥ portPart σ φ) +
          interiorPart σ j ⬝ᵥ ((interiorBlock tail head Rset Rval σ)⁻¹ *ᵥ interiorPart σ j) := by
  have hG := portInteriorConductance_posDef tail head Rset Rval hR ground hconn σ
  rw [← fromBlocks_portBlock_couplingBlock] at hG
  obtain ⟨hP, hI⟩ := (groundedKCL_iff_blocks tail head Rset Rval ground σ φ j hground).mp hKCL
  obtain ⟨hK, hred, hrec, hdiss⟩ := kron_reduction_correct _ _ _ hG _ _ _ _ hP hI
  refine ⟨hK, hred, hrec, ?_⟩
  rw [stampQuadratic_eq_blockQuadratic tail head Rset Rval ground σ φ hground]
  exact hdiss

/-- Converse direction: for positive resistances and a connected resistor graph, a grounded
potential solves the network exactly when its port part solves the reduced port law and its
interior part is the reconstruction. -/
theorem groundedKCL_iff_reduced {nN nB : ℕ} {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] (tail head : Fin nB → Fin nN) (Rset : Finset (Fin nB))
    (Rval : Fin nB → ℝ) (hR : ∀ e ∈ Rset, 0 < Rval e) (ground : Fin nN)
    (hconn : (resistorGraph tail head Rset).Connected) (σ : m ⊕ p ≃ {v // v ≠ ground})
    (φ j : Fin nN → ℝ) (hground : φ ground = 0) :
    (∀ v, v ≠ ground →
        (nodalConductance (physicalIncidence tail head) Rset Rval *ᵥ φ) v = j v) ↔
      (kronConductance tail head Rset Rval σ *ᵥ portPart σ φ =
          portPart σ j - couplingBlock tail head Rset Rval σ *ᵥ
            ((interiorBlock tail head Rset Rval σ)⁻¹ *ᵥ interiorPart σ j) ∧
        interiorPart σ φ = (interiorBlock tail head Rset Rval σ)⁻¹ *ᵥ
          (interiorPart σ j - (couplingBlock tail head Rset Rval σ)ᵀ *ᵥ portPart σ φ)) := by
  have hG := portInteriorConductance_posDef tail head Rset Rval hR ground hconn σ
  rw [← fromBlocks_portBlock_couplingBlock] at hG
  let _ : Invertible (interiorBlock tail head Rset Rval σ) :=
    (interior_posDef hG).isUnit.invertible
  rw [groundedKCL_iff_blocks tail head Rset Rval ground σ φ j hground]
  exact block_solution_iff_reduced _ _ _ _ _ _ _

end PhyslibExt.Circuits.GroundedKronBridge
