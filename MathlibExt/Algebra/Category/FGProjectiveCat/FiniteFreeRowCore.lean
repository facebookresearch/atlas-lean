/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.CategoryTheory.Conj
public import MathlibExt.Algebra.Category.FGProjectiveCat.FiniteFreeComplement
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BlockElementary
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BlockStabilization

/-!
# Row matrices and finite-free projective automorphisms

For an associative unital ring, row multiplication identifies the opposite
finite general linear group with the automorphisms of the standard finite-free
left module.  The equivalence sends `op g` to `v ↦ v ᵥ* g`.

The full reindexed block-diagonal square identifies matrix blocks with
categorical direct sums.  Identity blocks give arbitrary block and successor
stabilization.  The existing inverse-column convention over commutative rings
is a separate comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Matrix

universe u

namespace FGProjectiveCat

section Semiring

variable (R : Type u) [Semiring R]

private theorem rowMatrixEquiv_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) :
    MulOpposite.unop (matrixRingEquivEndVecMulOpposite (ι := ι) (A := R) M) =
      M.toLinearMapRight' := by
  ext v i
  rfl

/-- The opposite matrix general linear group acts by right multiplication of
row vectors in the standard finite-free left module. -/
noncomputable def rowGLLinearEquiv (n : ℕ) :
    (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ≃*
      ((Fin n → R) ≃ₗ[R] (Fin n → R)) := by
  let M := Matrix (Fin n) (Fin n) R
  let E := Module.End R (Fin n → R)
  let e : M ≃+* Eᵐᵒᵖ :=
    matrixRingEquivEndVecMulOpposite (ι := Fin n) (A := R)
  let eop : Mᵐᵒᵖ ≃+* E := e.op.trans (RingEquiv.opOp E).symm
  exact (Units.opEquiv (M := M)).symm.trans
    ((Units.mapEquiv eop.toMulEquiv).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin n → R)))

@[simp]
theorem rowGLLinearEquiv_apply (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) (v : Fin n → R) :
    rowGLLinearEquiv R n g v =
      v ᵥ* (↑(MulOpposite.unop g) : Matrix (Fin n) (Fin n) R) := by
  change MulOpposite.unop
      (matrixRingEquivEndVecMulOpposite (ι := Fin n) (A := R)
        (↑(MulOpposite.unop g) : Matrix (Fin n) (Fin n) R)) v = _
  rw [rowMatrixEquiv_eq]
  rfl

end Semiring

section Ring

variable (R : Type u) [Ring R]

/-- Row multiplication identifies the opposite finite matrix group with the
automorphism group of the standard finite-free projective. -/
noncomputable def finiteOppositeGLAutRowMulEquiv (n : ℕ) :
    (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ≃*
      Aut (standardFree R n) :=
  (rowGLLinearEquiv R n).trans
    (autCarrierLinearEquiv (standardFree R n)).symm

@[simp]
theorem finiteOppositeGLAutRowMulEquiv_apply (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) (v : Fin n → R) :
    (finiteOppositeGLAutRowMulEquiv R n g).asIso.hom v =
      v ᵥ* (↑(MulOpposite.unop g) : Matrix (Fin n) (Fin n) R) := by
  change rowGLLinearEquiv R n g v = _
  exact rowGLLinearEquiv_apply R n g v

/-- A full reindexed block-diagonal matrix corresponds to the direct sum of
the two row automorphisms under the standard free-module isomorphism. -/
theorem finiteOppositeGLAutRowMulEquiv_blockDiagonal (n m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R)
    (h : Matrix.GeneralLinearGroup (Fin m) R) :
    finiteOppositeGLAutRowMulEquiv R (n + m)
        (MulOpposite.op
          (Matrix.GeneralLinearGroup.reindexMulEquiv
            (finSumFinEquiv (m := n) (n := m))
            (Matrix.GeneralLinearGroup.BlockElementary.blockDiagonal g h))) =
      (standardFreeAddIso R n m).symm.conjAut
        (Aut.of (biprod.mapIso
          (finiteOppositeGLAutRowMulEquiv R n (MulOpposite.op g)).asIso
          (finiteOppositeGLAutRowMulEquiv R m (MulOpposite.op h)).asIso)) := by
  let P := standardFree R n
  let Q := standardFree R m
  let e := standardFreeAddIso R n m
  let f := finSumFinEquiv (m := n) (n := m)
  let D := Matrix.GeneralLinearGroup.reindexMulEquiv f
    (Matrix.GeneralLinearGroup.BlockElementary.blockDiagonal g h)
  let gIso : P ≅ P := (finiteOppositeGLAutRowMulEquiv R n (MulOpposite.op g)).asIso
  let hIso : Q ≅ Q := (finiteOppositeGLAutRowMulEquiv R m (MulOpposite.op h)).asIso
  let b : Aut (P ⊞ Q) := .of (biprod.mapIso gIso hIso)
  have hsplit (v : Fin (n + m) → R) :
      biprodCarrierLinearEquiv P Q (e.hom v) =
        ((v ∘ f) ∘ Sum.inl, (v ∘ f) ∘ Sum.inr) := by
    let x : (P ⊞ Q : FGProjectiveCat R) := e.hom v
    have h := standardFreeAddIso_inv_apply_fun R n m x
    have hx : e.symm.hom.hom x = v := by
      exact congrArg
        (fun k : standardFree R (n + m) ⟶ standardFree R (n + m) => k.hom.hom v)
        (Iso.hom_inv_id e)
    rw [hx] at h
    dsimp only [x] at h ⊢
    apply Prod.ext
    · funext i
      simpa only [f, Function.comp_apply, finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_apply_left, Sum.elim_inl]
        using (congrFun h (Fin.castAdd m i)).symm
    · funext j
      simpa only [f, Function.comp_apply, finSumFinEquiv_symm_apply_natAdd,
        finSumFinEquiv_apply_right, Sum.elim_inr]
        using (congrFun h (Fin.natAdd n j)).symm
  have hrow (v : Fin (n + m) → R) :
      (v ᵥ* (D : Matrix (Fin (n + m)) (Fin (n + m)) R)) ∘ f =
        Sum.elim (((v ∘ f) ∘ Sum.inl) ᵥ* (g : Matrix (Fin n) (Fin n) R))
          (((v ∘ f) ∘ Sum.inr) ᵥ* (h : Matrix (Fin m) (Fin m) R)) := by
    funext i
    dsimp only [D]
    rw [Matrix.GeneralLinearGroup.coe_reindexMulEquiv,
      Matrix.GeneralLinearGroup.BlockElementary.blockDiagonal_eq_blockDiagonalHom,
      Matrix.GeneralLinearGroup.coe_blockDiagonalHom]
    change
      (v ᵥ* (Matrix.fromBlocks
        (g : Matrix (Fin n) (Fin n) R) 0 0
        (h : Matrix (Fin m) (Fin m) R)).submatrix f.symm f.symm) (f i) = _
    rw [Matrix.submatrix_vecMul_equiv]
    simp only [Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    simpa using congrFun (Matrix.vecMul_fromBlocks
      (g : Matrix (Fin n) (Fin n) R) 0 0
      (h : Matrix (Fin m) (Fin m) R) (v ∘ f)) i
  have hconj : (e.symm.conjAut b).asIso.hom = e.hom ≫ b.asIso.hom ≫ e.inv := by
    rw [Iso.conjAut_hom, Iso.conj_apply_asHom]
    rfl
  apply Aut.ext
  apply Iso.ext
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro v
  funext i
  change
    (finiteOppositeGLAutRowMulEquiv R (n + m) (MulOpposite.op D)).asIso.hom v i =
      (e.symm.conjAut b).asIso.hom v i
  rw [hconj]
  change _ = e.inv (b.asIso.hom (e.hom v)) i
  rw [finiteOppositeGLAutRowMulEquiv_apply]
  change _ = (standardFreeAddIso R n m).symm.hom.hom (b.asIso.hom (e.hom v)) i
  rw [standardFreeAddIso_inv_apply]
  change _ = Sum.elim
    (biprodCarrierLinearEquiv P Q
      ((biprod.mapIso gIso hIso).hom (e.hom v))).1
    (biprodCarrierLinearEquiv P Q
      ((biprod.mapIso gIso hIso).hom (e.hom v))).2
    (f.symm i)
  rw [biprodCarrierLinearEquiv_mapIso_apply, hsplit]
  change _ = Sum.elim
    ((finiteOppositeGLAutRowMulEquiv R n (MulOpposite.op g)).asIso.hom
      ((v ∘ f) ∘ Sum.inl))
    ((finiteOppositeGLAutRowMulEquiv R m (MulOpposite.op h)).asIso.hom
      ((v ∘ f) ∘ Sum.inr)) (f.symm i)
  rw [finiteOppositeGLAutRowMulEquiv_apply, finiteOppositeGLAutRowMulEquiv_apply]
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, MulOpposite.unop_op] using
    congrFun (hrow v) (f.symm i)

/-- Adding an identity matrix block is categorical direct-sum stabilization
of the corresponding row automorphism. -/
theorem finiteOppositeGLAutRowMulEquiv_blockStabilization (n m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteOppositeGLAutRowMulEquiv R (n + m)
        (MulOpposite.op (Matrix.GeneralLinearGroup.blockStabilization n m R g)) =
      (standardFreeAddIso R n m).symm.conjAut
        (Aut.of (biprod.mapIso
          (finiteOppositeGLAutRowMulEquiv R n (MulOpposite.op g)).asIso
          (Iso.refl (standardFree R m)))) := by
  have hblock : Matrix.GeneralLinearGroup.BlockElementary.blockDiagonal
      g (1 : Matrix.GeneralLinearGroup (Fin m) R) =
        Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin m) R g := by
    rw [Matrix.GeneralLinearGroup.BlockElementary.blockDiagonal_eq_blockDiagonalHom]
    exact Matrix.GeneralLinearGroup.blockDiagonalHom_one_right (m := Fin m) g
  have hone : (1 : Aut (standardFree R m)).asIso = Iso.refl (standardFree R m) := rfl
  simpa only [hblock, MulOpposite.op_one, map_one, hone,
    Matrix.GeneralLinearGroup.blockStabilization, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom] using
    finiteOppositeGLAutRowMulEquiv_blockDiagonal R n m g 1

/-- Successor matrix stabilization agrees with direct sum by the rank-one
identity automorphism. -/
theorem finiteOppositeGLAutRowMulEquiv_stabilization (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteOppositeGLAutRowMulEquiv R (n + 1)
        (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization R g)) =
      (standardFreeAddIso R n 1).symm.conjAut
        (Aut.of (biprod.mapIso
          (finiteOppositeGLAutRowMulEquiv R n (MulOpposite.op g)).asIso
          (Iso.refl (standardFree R 1)))) := by
  exact finiteOppositeGLAutRowMulEquiv_blockStabilization R n 1 g

end Ring

end FGProjectiveCat

end
