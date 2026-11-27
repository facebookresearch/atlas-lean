/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Map
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Block-diagonal inclusions and general linear stabilization

Let R be a semiring and n,m finite index types in independent universes. Write
ιL(g)=diag(g,I_m) and ιR(h)=diag(I_n,h) in GL(n⊕m,R), and D(g,h)=diag(g,h). The left and right
inclusions have commuting images, so D is a group homomorphism GL(n,R)×GL(m,R)→GL(n⊕m,R). For
n=Fin k and m=Fin 1, reindexing gives the injective successor map GL(k,R)→GL(k+1,R),
g↦diag(g,1).
-/

@[expose] public section

namespace Matrix

universe u v w

/-- **Matrix monoid homomorphism adjoining an identity block.**

Let R be a semiring and n,m finite index types. The multiplicative map fromBlocksOneMonoidHom
R n m sends a square matrix A to diag(A,I_m) on n⊕m.
-/
def fromBlocksOneMonoidHom (R : Type w) [Semiring R] (n : Type u) (m : Type v)
    [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m] :
    Matrix n n R →* Matrix (n ⊕ m) (n ⊕ m) R where
  toFun A := fromBlocks A 0 0 1
  map_one' := fromBlocks_one
  map_mul' A B := by
    calc
      fromBlocks (A * B) (0 : Matrix n m R) (0 : Matrix m n R) (1 : Matrix m m R)
          = fromBlocks (A * B + (0 : Matrix n m R) * (0 : Matrix m n R))
              (A * (0 : Matrix n m R) + (0 : Matrix n m R) * (1 : Matrix m m R))
              ((0 : Matrix m n R) * B + (1 : Matrix m m R) * (0 : Matrix m n R))
              ((0 : Matrix m n R) * (0 : Matrix n m R) + (1 : Matrix m m R) * 1) := by
            simp
      _ = fromBlocks A (0 : Matrix n m R) (0 : Matrix m n R) (1 : Matrix m m R) *
            fromBlocks B (0 : Matrix n m R) (0 : Matrix m n R) (1 : Matrix m m R) :=
        (fromBlocks_multiply A (0 : Matrix n m R) (0 : Matrix m n R) (1 : Matrix m m R)
          B (0 : Matrix n m R) (0 : Matrix m n R) (1 : Matrix m m R)).symm

end Matrix

namespace Matrix.GeneralLinearGroup

open Matrix

universe u v uR vR

section BlockInclusion

variable {n : Type u} {m : Type v} [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m]
variable {R : Type uR} [Semiring R] {S : Type vR} [Semiring S]

/-- **Left block inclusion of a general linear group.**

Let R be a semiring and n,m finite index types in independent universes. Write
ιL(g)=diag(g,I_m) and ιR(h)=diag(I_n,h) in GL(n⊕m,R), and D(g,h)=diag(g,h). The group
homomorphism blockDiagonalOne n m R:GL(n,R)→GL(n⊕m,R) is g↦ιL(g)=diag(g,I_m).
-/
def blockDiagonalOne (n : Type u) (m : Type v) (R : Type uR) [Semiring R]
    [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m] :
    GL n R →* GL (n ⊕ m) R :=
  Units.map (Matrix.fromBlocksOneMonoidHom R n m)

@[simp]
lemma coe_blockDiagonalOne (g : GL n R) :
    (↑(blockDiagonalOne n m R g) : Matrix (n ⊕ m) (n ⊕ m) R) =
      fromBlocks (↑g : Matrix n n R) 0 0 1 :=
  rfl

/-- **Right block inclusion of a general linear group.**

Let R be a semiring and n,m finite index types in independent universes. Write
ιL(g)=diag(g,I_m) and ιR(h)=diag(I_n,h) in GL(n⊕m,R), and D(g,h)=diag(g,h). The group
homomorphism blockDiagonalRight n m R:GL(m,R)→GL(n⊕m,R) is h↦ιR(h)=diag(I_n,h).
-/
def blockDiagonalRight (n : Type u) (m : Type v) (R : Type uR) [Semiring R]
    [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m] :
    GL m R →* GL (n ⊕ m) R :=
  (reindexMulEquiv (Equiv.sumComm m n)).toMonoidHom.comp (blockDiagonalOne m n R)

/-- **Underlying matrix of the right block inclusion.**

Let R be a semiring and n,m finite index types in independent universes. Write
ιL(g)=diag(g,I_m) and ιR(h)=diag(I_n,h) in GL(n⊕m,R), and D(g,h)=diag(g,h). For h∈GL(m,R), the
matrix underlying blockDiagonalRight n m R h is [[I_n,0],[0,h]].
-/
@[simp]
lemma coe_blockDiagonalRight (g : GL m R) :
    (↑(blockDiagonalRight n m R g) : Matrix (n ⊕ m) (n ⊕ m) R) =
      fromBlocks 1 0 0 (↑g : Matrix m m R) := by
  change Matrix.reindex (Equiv.sumComm m n) (Equiv.sumComm m n)
    (fromBlocks (↑g : Matrix m m R) 0 0 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- **Disjoint block general linear groups commute.**

Let R be a semiring and n,m finite index types in independent universes. Write
ιL(g)=diag(g,I_m) and ιR(h)=diag(I_n,h) in GL(n⊕m,R), and D(g,h)=diag(g,h). For g∈GL(n,R) and
h∈GL(m,R), ιL(g)*ιR(h)=ιR(h)*ιL(g).
-/
theorem commute_blockDiagonalOne_blockDiagonalRight (g : GL n R) (h : GL m R) :
    Commute (blockDiagonalOne n m R g) (blockDiagonalRight n m R h) := by
  change blockDiagonalOne n m R g * blockDiagonalRight n m R h =
    blockDiagonalRight n m R h * blockDiagonalOne n m R g
  apply Units.ext
  simp only [Units.val_mul, coe_blockDiagonalOne, coe_blockDiagonalRight,
    fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, one_mul, mul_one]

/-- **Two-block diagonal group homomorphism.**

Let R be a semiring and n,m finite index types in independent universes. Write
ιL(g)=diag(g,I_m) and ιR(h)=diag(I_n,h) in GL(n⊕m,R), and D(g,h)=diag(g,h). The map
blockDiagonalHom n m R:GL(n,R)×GL(m,R)→GL(n⊕m,R) sends (g,h) to D(g,h)=diag(g,h).
-/
def blockDiagonalHom (n : Type u) (m : Type v) (R : Type uR) [Semiring R]
    [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m] :
    (GL n R × GL m R) →* GL (n ⊕ m) R :=
  (blockDiagonalOne n m R).noncommCoprod (blockDiagonalRight n m R)
    (fun g h => commute_blockDiagonalOne_blockDiagonalRight g h)

/-- **Underlying matrix of the two-block diagonal homomorphism.**

Let R be a semiring and n,m finite index types in independent universes. Write
ιL(g)=diag(g,I_m) and ιR(h)=diag(I_n,h) in GL(n⊕m,R), and D(g,h)=diag(g,h). For g∈GL(n,R) and
h∈GL(m,R), blockDiagonalHom n m R (g,h) has matrix [[g,0],[0,h]].
-/
@[simp]
theorem coe_blockDiagonalHom (g : GL n R) (h : GL m R) :
    (↑(blockDiagonalHom n m R (g, h)) : Matrix (n ⊕ m) (n ⊕ m) R) =
      fromBlocks (↑g : Matrix n n R) 0 0 (↑h : Matrix m m R) := by
  change (↑(blockDiagonalOne n m R g * blockDiagonalRight n m R h) :
    Matrix (n ⊕ m) (n ⊕ m) R) = _
  simp only [Units.val_mul, coe_blockDiagonalOne, coe_blockDiagonalRight,
    fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, one_mul, mul_one]

/-- **Second identity block recovers the left inclusion.**

Let R be a semiring and n,m finite index types in independent universes. Write
ιL(g)=diag(g,I_m) and ιR(h)=diag(I_n,h) in GL(n⊕m,R), and D(g,h)=diag(g,h). For g∈GL(n,R),
D(g,1)=ιL(g), or blockDiagonalHom n m R (g,1)=blockDiagonalOne n m R g.
-/
@[simp]
theorem blockDiagonalHom_one_right (g : GL n R) :
    blockDiagonalHom n m R (g, 1) = blockDiagonalOne n m R g := by
  change blockDiagonalOne n m R g * blockDiagonalRight n m R 1 = _
  rw [map_one, mul_one]

/-- **First identity block recovers the right inclusion.**

Let R be a semiring and n,m finite index types in independent universes. Write
ιL(g)=diag(g,I_m) and ιR(h)=diag(I_n,h) in GL(n⊕m,R), and D(g,h)=diag(g,h). For h∈GL(m,R),
D(1,h)=ιR(h), or blockDiagonalHom n m R (1,h)=blockDiagonalRight n m R h.
-/
@[simp]
theorem blockDiagonalHom_one_left (h : GL m R) :
    blockDiagonalHom n m R (1, h) = blockDiagonalRight n m R h := by
  change blockDiagonalOne n m R 1 * blockDiagonalRight n m R h = _
  rw [map_one, one_mul]

theorem blockDiagonalOne_mapRingHom (f : R →+* S) :
    (blockDiagonalOne n m S).comp (mapRingHom (n := n) f) =
      (mapRingHom (n := n ⊕ m) f).comp (blockDiagonalOne n m R) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, coe_blockDiagonalOne, coe_mapRingHom,
    fromBlocks_map]
  have h0_nm : (0 : Matrix n m R).map f = 0 := by
    ext i j
    simp [Matrix.map_apply, f.map_zero]
  have h0_mn : (0 : Matrix m n R).map f = 0 := by
    ext i j
    simp [Matrix.map_apply, f.map_zero]
  have h1 : (1 : Matrix m m R).map f = 1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.one_apply]
    split
    · simp
    · simp [f.map_zero]
  rw [h0_nm, h0_mn, h1]

@[simp]
theorem blockDiagonalOne_mapRingHom_apply (f : R →+* S) (g : GL n R) :
    blockDiagonalOne n m S (mapRingHom f g) =
      mapRingHom (n := n ⊕ m) f (blockDiagonalOne n m R g) :=
  DFunLike.congr_fun (blockDiagonalOne_mapRingHom (n := n) (m := m) (f := f)) g

end BlockInclusion

section SuccStabilization

variable {R : Type uR} [Semiring R] {S : Type vR} [Semiring S]

/-- **Successor stabilization of finite general linear groups.**

Let R be a semiring and k∈ℕ. The group homomorphism stabilization R:GL(Fin k,R)→GL(Fin(k+1),R)
sends g to diag(g,1), with the identity in the new last coordinate.
-/
def stabilization (R : Type uR) [Semiring R] {n : ℕ} :
    GL (Fin n) R →* GL (Fin (n + 1)) R :=
  (reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))).toMonoidHom.comp
    (blockDiagonalOne (Fin n) (Fin 1) R)

@[simp]
lemma coe_stabilization {n : ℕ} (g : GL (Fin n) R) :
    (↑(stabilization R (n := n) g) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      Matrix.reindex (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1))
        (fromBlocks (↑g : Matrix (Fin n) (Fin n) R) 0 0 1) :=
  rfl

theorem stabilization_mapRingHom {n : ℕ} (f : R →+* S) :
    (stabilization S (n := n)).comp (mapRingHom (n := Fin n) f) =
      (mapRingHom (n := Fin (n + 1)) f).comp (stabilization R (n := n)) := by
  calc
    (stabilization S (n := n)).comp (mapRingHom (n := Fin n) f)
        = ((reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))).toMonoidHom.comp
            (blockDiagonalOne (Fin n) (Fin 1) S)).comp (mapRingHom (n := Fin n) f) := rfl
    _ = (reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))).toMonoidHom.comp
          ((blockDiagonalOne (Fin n) (Fin 1) S).comp (mapRingHom (n := Fin n) f)) := by
          rw [MonoidHom.comp_assoc]
    _ = (reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))).toMonoidHom.comp
          ((mapRingHom (n := Fin n ⊕ Fin 1) f).comp (blockDiagonalOne (Fin n) (Fin 1) R)) := by
          rw [blockDiagonalOne_mapRingHom]
    _ = ((reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))).toMonoidHom.comp
          (mapRingHom (n := Fin n ⊕ Fin 1) f)).comp (blockDiagonalOne (Fin n) (Fin 1) R) := by
          rw [← MonoidHom.comp_assoc]
    _ = ((mapRingHom (n := Fin (n + 1)) f).comp
          (reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))).toMonoidHom).comp
          (blockDiagonalOne (Fin n) (Fin 1) R) := by
          rw [reindexMulEquiv_mapRingHom]
    _ = (mapRingHom (n := Fin (n + 1)) f).comp
          ((reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))).toMonoidHom.comp
            (blockDiagonalOne (Fin n) (Fin 1) R)) := by
          rw [MonoidHom.comp_assoc]
    _ = (mapRingHom (n := Fin (n + 1)) f).comp (stabilization R (n := n)) := rfl

@[simp]
theorem stabilization_mapRingHom_apply {n : ℕ} (f : R →+* S) (g : GL (Fin n) R) :
    stabilization S (mapRingHom f g) =
      mapRingHom (n := Fin (n + 1)) f (stabilization R g) :=
  DFunLike.congr_fun (stabilization_mapRingHom (n := n) (f := f)) g

end SuccStabilization

/-- **Injectivity of the block identity inclusion.**

Let R be a semiring and n,m finite index types in independent universes. Write
ιL(g)=diag(g,I_m) and ιR(h)=diag(I_n,h) in GL(n⊕m,R), and D(g,h)=diag(g,h). The group
homomorphism blockDiagonalOne n m R:g↦diag(g,I_m) is injective.
-/
private theorem blockDiagonalOne_injective {R : Type u} [Semiring R]
    {n : Type*} {m : Type*} [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m] :
    Function.Injective (blockDiagonalOne n m R) := by
  intro g₁ g₂ h
  apply Units.ext
  have h_eq : (↑(blockDiagonalOne n m R g₁) : Matrix (n ⊕ m) (n ⊕ m) R) =
      (↑(blockDiagonalOne n m R g₂) : Matrix (n ⊕ m) (n ⊕ m) R) :=
    congrArg Units.val h
  simp only [coe_blockDiagonalOne] at h_eq
  ext i j
  have h_ij := congrFun (congrFun h_eq (Sum.inl i)) (Sum.inl j)
  simp only [Matrix.fromBlocks_apply₁₁] at h_ij
  exact h_ij

/-- **Injectivity of successor general-linear stabilization.**

Let R be a semiring and k∈ℕ. The map stabilization R:GL(Fin k,R)→GL(Fin(k+1),R), g↦diag(g,1),
is injective, including k=0.
-/
theorem stabilization_injective {R : Type u} [Semiring R] {n : ℕ} :
    Function.Injective (stabilization (R := R) (n := n)) := by
  intro g₁ g₂ h
  have h_block : blockDiagonalOne (Fin n) (Fin 1) R g₁ =
      blockDiagonalOne (Fin n) (Fin 1) R g₂ := by
    apply (MulEquiv.injective (reindexMulEquiv (finSumFinEquiv (m := n) (n := 1)))) h
  exact blockDiagonalOne_injective h_block

end Matrix.GeneralLinearGroup

universe uBlock₁ uBlock₂ uBlock₃ uScalar

namespace Matrix.GeneralLinearGroup

variable {α : Type uBlock₁} {β : Type uBlock₂} {γ : Type uBlock₃}
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable [Fintype α] [Fintype β] [Fintype γ]
variable {R : Type uScalar} [Semiring R]

/-- **Exchanging two complete diagonal blocks.**

Let R be a semiring, α,β finite index types and g∈GL(α,R), h∈GL(β,R). Reindexing diag(g,h)
along α⊕β≃β⊕α gives diag(h,g).
-/
public theorem blockDiagonalHom_sumComm (g : GL α R) (h : GL β R) :
    reindexMulEquiv (Equiv.sumComm α β) (blockDiagonalHom α β R (g, h)) =
      blockDiagonalHom β α R (h, g) := by
  apply Units.ext
  simp only [coe_reindexMulEquiv, coe_blockDiagonalHom]
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- **Associating three complete diagonal blocks.**

Let R be a semiring, α,β,γ finite index types and g,h,k invertible matrices on them.
Reindexing diag(diag(g,h),k) from (α⊕β)⊕γ to α⊕(β⊕γ) gives diag(g,diag(h,k)).
-/
public theorem blockDiagonalHom_sumAssoc
    (g : GL α R) (h : GL β R) (k : GL γ R) :
    reindexMulEquiv (Equiv.sumAssoc α β γ)
      (blockDiagonalHom (α ⊕ β) γ R (blockDiagonalHom α β R (g, h), k)) =
      blockDiagonalHom α (β ⊕ γ) R (g, blockDiagonalHom β γ R (h, k)) := by
  apply Units.ext
  simp only [coe_reindexMulEquiv, coe_blockDiagonalHom]
  apply Matrix.ext
  intro i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> rfl

end Matrix.GeneralLinearGroup

universe uActive₁ uActive₂ uInactive₁ uInactive₂ uCoeff

namespace Matrix.GeneralLinearGroup

/-- **Block stabilization is natural under both index equivalences.**

Let R be a semiring, A₁,A₂,I₁,I₂ finite index types, eA:A₁≃A₂, eI:I₁≃I₂ and g∈GL(A₁,R).
Reindexing diag(g,I_(I₁)) along eA⊕eI gives diag(reindex_eA(g),I_(I₂)). All four index types
and R may have independent universes.
-/
public theorem blockDiagonalOne_reindex
    {Active₁ : Type uActive₁} {Active₂ : Type uActive₂}
    {Inactive₁ : Type uInactive₁} {Inactive₂ : Type uInactive₂}
    [DecidableEq Active₁] [DecidableEq Active₂]
    [DecidableEq Inactive₁] [DecidableEq Inactive₂]
    [Fintype Active₁] [Fintype Active₂] [Fintype Inactive₁] [Fintype Inactive₂]
    (R : Type uCoeff) [Semiring R]
    (eA : Active₁ ≃ Active₂) (eI : Inactive₁ ≃ Inactive₂)
    (g : GL Active₁ R) :
    reindexMulEquiv (Equiv.sumCongr eA eI) (blockDiagonalOne Active₁ Inactive₁ R g) =
      blockDiagonalOne Active₂ Inactive₂ R (reindexMulEquiv eA g) := by
  apply Units.ext
  simp only [coe_reindexMulEquiv, coe_blockDiagonalOne]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change (g : Matrix Active₁ Active₁ R) (eA.symm i) (eA.symm j) =
      (g : Matrix Active₁ Active₁ R) (eA.symm i) (eA.symm j)
    rfl
  · change (0 : R) = 0
    rfl
  · change (0 : R) = 0
    rfl
  · change (1 : Matrix Inactive₁ Inactive₁ R) (eI.symm i) (eI.symm j) =
      (1 : Matrix Inactive₂ Inactive₂ R) i j
    simp only [Matrix.one_apply]
    exact if_congr eI.symm.injective.eq_iff rfl rfl

end Matrix.GeneralLinearGroup
