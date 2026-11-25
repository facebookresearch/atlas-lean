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
# Block diagonal maps and stabilization for finite general linear groups

Over a semiring `R`, finite index types `n` and `m` with decidable equality give block
inclusions `g ↦ diag(g, 1)` and `h ↦ diag(1, h)` in `GL (n ⊕ m) R`. Their images commute
and give the block map `(g, h) ↦ diag(g, h)`. Their cross blocks are zero.

With `n` replaced by `Fin n` and `m` by `Fin 1`, adjoining the identity block and using
`finSumFinEquiv` gives the injective successor stabilization from rank `n` to `n + 1`.
-/

@[expose] public section

namespace Matrix

universe u v w

/-- For a semiring `R` and finite index types `n`, `m` with decidable
equality, `A ↦ fromBlocks A 0 0 1` is a multiplicative monoid homomorphism from
square matrices on `n` to square matrices on `n ⊕ m`. The new block on `m` is the identity. -/
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

/-- For a semiring `R` and finite index types `n`, `m` with decidable equality,
the left block inclusion `GL n R →* GL (n ⊕ m) R` sends `g` to `diag(g, 1)` with the
identity on `m` and zero cross blocks. -/
def blockDiagonalOne (n : Type u) (m : Type v) (R : Type uR) [Semiring R]
    [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m] :
    GL n R →* GL (n ⊕ m) R :=
  Units.map (Matrix.fromBlocksOneMonoidHom R n m)

/-- For a semiring `R`, finite index types `n`, `m` with decidable equality,
and `g : GL n R`, the underlying matrix of `blockDiagonalOne n m R g` is
`fromBlocks ↑g 0 0 1`. -/
@[simp]
lemma coe_blockDiagonalOne (g : GL n R) :
    (↑(blockDiagonalOne n m R g) : Matrix (n ⊕ m) (n ⊕ m) R) =
      fromBlocks (↑g : Matrix n n R) 0 0 1 :=
  rfl

/-- For a semiring `R` and finite index types `n`, `m` with decidable equality,
the right block inclusion `GL m R →* GL (n ⊕ m) R` sends `h` to `diag(1, h)` with the
identity on `n` and zero cross blocks. -/
def blockDiagonalRight (n : Type u) (m : Type v) (R : Type uR) [Semiring R]
    [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m] :
    GL m R →* GL (n ⊕ m) R :=
  (reindexMulEquiv (Equiv.sumComm m n)).toMonoidHom.comp (blockDiagonalOne m n R)

/-- For a semiring `R`, finite index types `n`, `m` with decidable equality,
and `h : GL m R`, the underlying matrix of `blockDiagonalRight n m R h` is
`fromBlocks 1 0 0 ↑h`. -/
@[simp]
lemma coe_blockDiagonalRight (g : GL m R) :
    (↑(blockDiagonalRight n m R g) : Matrix (n ⊕ m) (n ⊕ m) R) =
      fromBlocks 1 0 0 (↑g : Matrix m m R) := by
  change Matrix.reindex (Equiv.sumComm m n) (Equiv.sumComm m n)
    (fromBlocks (↑g : Matrix m m R) 0 0 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- For a semiring `R` and finite index types `n`, `m`
with decidable equality, `diag(g, 1) * diag(1, h) = diag(1, h) * diag(g, 1)` in
`GL (n ⊕ m) R` for every `g : GL n R` and `h : GL m R`. -/
theorem commute_blockDiagonalOne_blockDiagonalRight (g : GL n R) (h : GL m R) :
    Commute (blockDiagonalOne n m R g) (blockDiagonalRight n m R h) := by
  change blockDiagonalOne n m R g * blockDiagonalRight n m R h =
    blockDiagonalRight n m R h * blockDiagonalOne n m R g
  apply Units.ext
  simp only [Units.val_mul, coe_blockDiagonalOne, coe_blockDiagonalRight,
    fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, one_mul, mul_one]

/-- For a semiring `R` and finite index types `n`, `m` with decidable equality,
the group homomorphism `GL n R × GL m R →* GL (n ⊕ m) R` sends `(g, h)` to `diag(g, h)`,
with zero cross blocks. -/
def blockDiagonalHom (n : Type u) (m : Type v) (R : Type uR) [Semiring R]
    [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m] :
    (GL n R × GL m R) →* GL (n ⊕ m) R :=
  (blockDiagonalOne n m R).noncommCoprod (blockDiagonalRight n m R)
    (fun g h => commute_blockDiagonalOne_blockDiagonalRight g h)

/-- For a semiring `R`, finite index types `n`, `m` with decidable equality,
and `g : GL n R`, `h : GL m R`, the underlying matrix of `blockDiagonalHom n m R (g, h)`
is `fromBlocks ↑g 0 0 ↑h`. -/
@[simp]
theorem coe_blockDiagonalHom (g : GL n R) (h : GL m R) :
    (↑(blockDiagonalHom n m R (g, h)) : Matrix (n ⊕ m) (n ⊕ m) R) =
      fromBlocks (↑g : Matrix n n R) 0 0 (↑h : Matrix m m R) := by
  change (↑(blockDiagonalOne n m R g * blockDiagonalRight n m R h) :
    Matrix (n ⊕ m) (n ⊕ m) R) = _
  simp only [Units.val_mul, coe_blockDiagonalOne, coe_blockDiagonalRight,
    fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, one_mul, mul_one]

/-- For a semiring `R`, finite index types `n`, `m` with decidable
equality, and `g : GL n R`, `blockDiagonalHom n m R (g, 1) = blockDiagonalOne n m R g`:
taking the second argument to be the identity gives the left block inclusion. -/
@[simp]
theorem blockDiagonalHom_one_right (g : GL n R) :
    blockDiagonalHom n m R (g, 1) = blockDiagonalOne n m R g := by
  change blockDiagonalOne n m R g * blockDiagonalRight n m R 1 = _
  rw [map_one, mul_one]

/-- For a semiring `R`, finite index types `n`, `m` with decidable
equality, and `h : GL m R`, `blockDiagonalHom n m R (1, h) = blockDiagonalRight n m R h`:
taking the first argument to be the identity gives the right block inclusion. -/
@[simp]
theorem blockDiagonalHom_one_left (h : GL m R) :
    blockDiagonalHom n m R (1, h) = blockDiagonalRight n m R h := by
  change blockDiagonalOne n m R 1 * blockDiagonalRight n m R h = _
  rw [map_one, one_mul]

/-- For semirings `R`, `S`, finite index types `n`, `m` with decidable
equality, and `f : R →+* S`, applying `f` before the left block inclusion equals applying
`f` after it, as group homomorphisms `GL n R →* GL (n ⊕ m) S`. -/
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

/-- For semirings `R`, `S`, finite index types `n`, `m` with
decidable equality, `f : R →+* S`, and `g : GL n R`, the matrix `diag(mapRingHom f g, 1)`
over `S` equals `mapRingHom f (diag(g, 1))`. -/
@[simp]
theorem blockDiagonalOne_mapRingHom_apply (f : R →+* S) (g : GL n R) :
    blockDiagonalOne n m S (mapRingHom f g) =
      mapRingHom (n := n ⊕ m) f (blockDiagonalOne n m R g) :=
  DFunLike.congr_fun (blockDiagonalOne_mapRingHom (n := n) (m := m) (f := f)) g

end BlockInclusion

section SuccStabilization

variable {R : Type uR} [Semiring R] {S : Type vR} [Semiring S]

/-- For a semiring `R` and `n : ℕ`, successor stabilization is the group map
`GL (Fin n) R →* GL (Fin (n + 1)) R` given by adjoining an identity block of size one
and reindexing `Fin n ⊕ Fin 1` by `finSumFinEquiv`. -/
def stabilization (R : Type uR) [Semiring R] {n : ℕ} :
    GL (Fin n) R →* GL (Fin (n + 1)) R :=
  (reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))).toMonoidHom.comp
    (blockDiagonalOne (Fin n) (Fin 1) R)

/-- For a semiring `R`, `n : ℕ`, and `g : GL (Fin n) R`, the underlying
matrix of `stabilization R g` is `fromBlocks ↑g 0 0 1` reindexed on both axes by
`finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)`. -/
@[simp]
lemma coe_stabilization {n : ℕ} (g : GL (Fin n) R) :
    (↑(stabilization R (n := n) g) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      Matrix.reindex (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1))
        (fromBlocks (↑g : Matrix (Fin n) (Fin n) R) 0 0 1) :=
  rfl

/-- For semirings `R`, `S`, `n : ℕ`, and `f : R →+* S`, applying
`f` entrywise at rank `n` and then stabilizing equals stabilizing and then applying `f` at
rank `n + 1`, as homomorphisms `GL (Fin n) R →* GL (Fin (n + 1)) S`. -/
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

/-- For semirings `R`, `S`, `f : R →+* S`, and `g : GL (Fin n) R`,
`stabilization S (mapRingHom f g) = mapRingHom f (stabilization R g)` at rank `n + 1`. -/
@[simp]
theorem stabilization_mapRingHom_apply {n : ℕ} (f : R →+* S) (g : GL (Fin n) R) :
    stabilization S (mapRingHom f g) =
      mapRingHom (n := Fin (n + 1)) f (stabilization R g) :=
  DFunLike.congr_fun (stabilization_mapRingHom (n := n) (f := f)) g

end SuccStabilization

/-- `blockDiagonalOne` is injective: equality on the top-left block determines equality. -/
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

/-- For every semiring `R` and `n : ℕ`, successor stabilization
`GL (Fin n) R →* GL (Fin (n + 1)) R`, given by `g ↦ diag(g, 1)`, is injective. -/
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

/-- For a semiring `R`, finite index types `α`, `β` with decidable
equality, and `g : GL α R`, `h : GL β R`, reindexing `blockDiagonalHom α β R (g, h)` by
`Equiv.sumComm α β : α ⊕ β ≃ β ⊕ α` gives `blockDiagonalHom β α R (h, g)`. -/
public theorem blockDiagonalHom_sumComm (g : GL α R) (h : GL β R) :
    reindexMulEquiv (Equiv.sumComm α β) (blockDiagonalHom α β R (g, h)) =
      blockDiagonalHom β α R (h, g) := by
  apply Units.ext
  simp only [coe_reindexMulEquiv, coe_blockDiagonalHom]
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- For a semiring `R`, finite index types `α`, `β`, `γ` with decidable
equality, and `g : GL α R`, `h : GL β R`, `k : GL γ R`, the two iterated block maps satisfy
`reindexMulEquiv (Equiv.sumAssoc α β γ)
  (blockDiagonalHom (α ⊕ β) γ R (blockDiagonalHom α β R (g, h), k))
= blockDiagonalHom α (β ⊕ γ) R (g, blockDiagonalHom β γ R (h, k))`.
The reindexing sends `(α ⊕ β) ⊕ γ` to `α ⊕ (β ⊕ γ)`, preserving the order of the blocks. -/
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

/-- For a semiring `R`, finite types `A`, `A'`, `I`, `I'` with decidable
equality, equivalences `eA : A ≃ A'`, `eI : I ≃ I'`, and `g : GL A R`, reindexing
`blockDiagonalOne A I R g` by `Equiv.sumCongr eA eI` gives
`blockDiagonalOne A' I' R (reindexMulEquiv eA g)`. The reindexing permutes the inactive
identity block without changing it. -/
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
