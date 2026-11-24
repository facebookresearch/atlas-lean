/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Ring.StableElementary.Basic
public import MathlibExt.KTheory.Ring.StableGeneralLinear.BlockStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Whitehead
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Elementary realizations of finite stable conjugation

Any finite conjugator can be doubled as `diag(q,q⁻¹)`. The existing
Whitehead identity puts that actual doubled matrix in the elementary
subgroup. Its conjugation of the active stabilized block is exactly the
original finite conjugation, with no determinant or commutativity
hypothesis on the ring. These computed elementary loops are the ones to
use in stabilized block-permutation homotopies after the plus map.
-/

noncomputable section

open CategoryTheory Matrix

universe u

namespace AlgebraicKTheory.StableGL

variable {R : Type u} [Ring R]

/-- The actual doubled index permutation underlying the Whitehead
elementary matrix for a permutation conjugator. -/
public def doubledFinitePermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + n)) :=
  (finSumFinEquiv (m := n) (n := n)).permCongr (Equiv.sumCongr σ σ⁻¹)

/-- Applying the actual doubled permutation through its original sum-index
    enumeration acts by the original permutation and its inverse. -/
public theorem doubledFinitePermutation_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n ⊕ Fin n) :
    doubledFinitePermutation σ ((finSumFinEquiv (m := n) (n := n)) x) =
      (finSumFinEquiv (m := n) (n := n)) ((Equiv.sumCongr σ σ⁻¹) x) := by
  change (finSumFinEquiv (m := n) (n := n)).permCongr
    (Equiv.sumCongr σ σ⁻¹) ((finSumFinEquiv (m := n) (n := n)) x) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- Doubling a permutation with its inverse produces an even permutation,
without using a determinant or a commutative coefficient ring. -/
public theorem doubledFinitePermutation_sign {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (doubledFinitePermutation σ) = 1 := by
  change Equiv.Perm.sign
    ((finSumFinEquiv (m := n) (n := n)).permCongr (Equiv.sumCongr σ σ⁻¹)) = 1
  rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, map_inv, mul_inv_cancel]

/-- The actual trailing-identity stabilization of a finite permutation. -/
public def finitePermutationStabilization {n : ℕ} (m : ℕ) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + m)) :=
  (finSumFinEquiv (m := n) (n := m)).permCongr
    (Equiv.sumCongr σ (1 : Equiv.Perm (Fin m)))

/-- Identity stabilization preserves the original sign. -/
public theorem finitePermutationStabilization_sign {n : ℕ}
    (m : ℕ) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (finitePermutationStabilization m σ) = Equiv.Perm.sign σ := by
  change Equiv.Perm.sign ((finSumFinEquiv (m := n) (n := m)).permCongr
    (Equiv.sumCongr σ (1 : Equiv.Perm (Fin m)))) = _
  rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, map_one, mul_one]

/-- On the original finite coordinates, the stabilized permutation is
the literal original permutation with the same trailing identity offset. -/
public theorem finitePermutationStabilization_castAdd {n : ℕ}
    (m : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    finitePermutationStabilization m σ (Fin.castAdd m i) = Fin.castAdd m (σ i) := by
  simp [finitePermutationStabilization, Equiv.permCongr_apply,
    finSumFinEquiv_symm_apply_castAdd]

/-- The added coordinates are literally fixed. -/
public theorem finitePermutationStabilization_natAdd {n : ℕ}
    (m : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin m) :
    finitePermutationStabilization m σ (Fin.natAdd n i) = Fin.natAdd n i := by
  simp [finitePermutationStabilization, Equiv.permCongr_apply,
    finSumFinEquiv_symm_apply_natAdd]

/-- The permutation matrix of the actual stabilized permutation is the
original finite general-linear identity-block stabilization. -/
public theorem finitePermutationStabilization_matrix {n : ℕ}
    (m : ℕ) (σ : Equiv.Perm (Fin n)) :
    Matrix.GeneralLinearGroup.permutationUnitsHom R (Fin (n + m))
        (finitePermutationStabilization m σ) =
      Matrix.GeneralLinearGroup.blockStabilization n m R
        (Matrix.GeneralLinearGroup.permutationUnitsHom R (Fin n) σ) := by
  change Matrix.GeneralLinearGroup.permutationUnitsHom R (Fin (n + m))
    ((finSumFinEquiv (m := n) (n := m)).permCongr
      (Equiv.sumCongr σ (1 : Equiv.Perm (Fin m)))) = _
  rw [← Matrix.GeneralLinearGroup.permutationUnitsHom_reindex,
    Matrix.GeneralLinearGroup.permutationUnitsHom_sumCongr, map_one,
    Matrix.GeneralLinearGroup.blockDiagonalHom_one_right]
  rfl

private theorem diagUnit_permutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Matrix.GeneralLinearGroup.diagUnit
        (Matrix.GeneralLinearGroup.permutationUnitsHom R (Fin n) σ) =
      Matrix.GeneralLinearGroup.permutationUnitsHom R (Fin n ⊕ Fin n)
        (Equiv.sumCongr σ σ⁻¹) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_diagUnit,
    Matrix.GeneralLinearGroup.coe_permutationUnitsHom,
    Matrix.GeneralLinearGroup.coe_permutationUnitsHom_GL_inv,
    Matrix.GeneralLinearGroup.coe_permutationUnitsHom]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Equiv.Perm.inv_def, Equiv.sumCongr_symm]

private theorem diagUnit_conjugate_active {n : ℕ}
    (q g : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup.diagUnit q *
        Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin n) R g *
          (Matrix.GeneralLinearGroup.diagUnit q)⁻¹ =
      Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin n) R (q * g * q⁻¹) := by
  apply Units.ext
  have hq : (↑(q⁻¹) : Matrix (Fin n) (Fin n) R) *
      (↑q : Matrix (Fin n) (Fin n) R) = 1 := by
    exact_mod_cast q.inv_val
  have hi : (↑((Matrix.GeneralLinearGroup.diagUnit q)⁻¹) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) =
      Matrix.fromBlocks (↑(q⁻¹) : Matrix (Fin n) (Fin n) R) 0 0
        (↑q : Matrix (Fin n) (Fin n) R) := rfl
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_diagUnit,
    Matrix.GeneralLinearGroup.coe_blockDiagonalOne, hi, Matrix.fromBlocks_multiply,
    mul_zero, zero_mul, add_zero, zero_add, mul_one, hq]

private def elementaryConjugatorFinite {n : ℕ}
    (q : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup (Fin (n + n)) R :=
  Matrix.GeneralLinearGroup.reindexMulEquiv
    (finSumFinEquiv (m := n) (n := n))
    (Matrix.GeneralLinearGroup.diagUnit q)

private theorem elementaryConjugatorFinite_mem {n : ℕ}
    (q : Matrix.GeneralLinearGroup (Fin n) R) :
    elementaryConjugatorFinite q ∈
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + n)) R :=
  Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup _
    (Matrix.GeneralLinearGroup.diagUnit_mem q)

private theorem elementaryConjugatorFinite_conjugates {n : ℕ}
    (q g : Matrix.GeneralLinearGroup (Fin n) R) :
    elementaryConjugatorFinite q *
        Matrix.GeneralLinearGroup.blockStabilization n n R g *
          (elementaryConjugatorFinite q)⁻¹ =
      Matrix.GeneralLinearGroup.blockStabilization n n R (q * g * q⁻¹) := by
  let e := Matrix.GeneralLinearGroup.reindexMulEquiv
    (finSumFinEquiv (m := n) (n := n)) (A := R)
  have h := congrArg e (diagUnit_conjugate_active q g)
  change e (Matrix.GeneralLinearGroup.diagUnit q) *
      e (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin n) R g) *
        (e (Matrix.GeneralLinearGroup.diagUnit q))⁻¹ =
    e (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin n) R (q * g * q⁻¹))
  simpa only [map_mul, map_inv] using h

/-- The actual stable elementary conjugator, obtained by doubling the given
finite matrix and using the existing ordered-sum reindexing. -/
public def elementaryConjugator {n : ℕ}
    (q : Matrix.GeneralLinearGroup (Fin n) R) : StableGL R :=
  StableGL.of (elementaryConjugatorFinite q)

/-- The computed conjugator belongs to the SAME stable elementary subgroup
which is killed by the original plus map. -/
public theorem elementaryConjugator_mem {n : ℕ}
    (q : Matrix.GeneralLinearGroup (Fin n) R) :
    elementaryConjugator q ∈ stableElementarySubgroup R := by
  exact StableE.fromFinite_mem (n + n) (elementaryConjugatorFinite_mem q)

/-- For a permutation input the SAME elementary conjugator is the stable
matrix of the actual even doubled permutation. -/
public theorem elementaryConjugator_permutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    elementaryConjugator (Matrix.GeneralLinearGroup.permutationUnitsHom R (Fin n) σ) =
      StableGL.of (Matrix.GeneralLinearGroup.permutationUnitsHom R (Fin (n + n))
        (doubledFinitePermutation σ)) := by
  change StableGL.of (elementaryConjugatorFinite
    (Matrix.GeneralLinearGroup.permutationUnitsHom R (Fin n) σ)) = _
  apply congrArg (fun g : Matrix.GeneralLinearGroup (Fin (n + n)) R => StableGL.of g)
  change Matrix.GeneralLinearGroup.reindexMulEquiv (finSumFinEquiv (m := n) (n := n))
    (Matrix.GeneralLinearGroup.diagUnit
      (Matrix.GeneralLinearGroup.permutationUnitsHom R (Fin n) σ)) = _
  rw [diagUnit_permutation, Matrix.GeneralLinearGroup.permutationUnitsHom_reindex]
  rfl

/-- On the active block its conjugation is precisely the original finite
conjugation, in the original stable general-linear group. -/
public theorem elementaryConjugator_conjugates {n : ℕ}
    (q g : Matrix.GeneralLinearGroup (Fin n) R) :
    elementaryConjugator q * StableGL.of g * (elementaryConjugator q)⁻¹ =
      StableGL.of (q * g * q⁻¹) := by
  have h := congrArg (fun t : Matrix.GeneralLinearGroup (Fin (n + n)) R => StableGL.of t)
    (elementaryConjugatorFinite_conjugates q g)
  change StableGL.of (elementaryConjugatorFinite q) * StableGL.of g *
      (StableGL.of (elementaryConjugatorFinite q))⁻¹ = StableGL.of (q * g * q⁻¹)
  simpa only [StableGL.of_mul, StableGL.of_inv, StableGL.of_blockStabilization] using h

/-- Finite-stage conjugation equations therefore have an actual elementary
witness in the stable group. No expected homotopy or elementary witness is
supplied by the caller. -/
public theorem exists_elementary_conjugator_of_finite_conjugacy {n : ℕ}
    (q g h : Matrix.GeneralLinearGroup (Fin n) R) (he : q * g * q⁻¹ = h) :
    ∃ w : stableElementarySubgroup R,
      (w : StableGL R) * StableGL.of g * (w : StableGL R)⁻¹ = StableGL.of h := by
  refine ⟨⟨elementaryConjugator q, elementaryConjugator_mem q⟩, ?_⟩
  exact (elementaryConjugator_conjugates q g).trans (congrArg StableGL.of he)

end AlgebraicKTheory.StableGL

end
