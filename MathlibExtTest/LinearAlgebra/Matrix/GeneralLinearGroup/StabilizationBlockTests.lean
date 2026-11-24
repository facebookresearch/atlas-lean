/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BlockElementary

/-!
# Clients of the heterogeneous GL block maps

The coefficient assertions cover all four blocks of both inclusions and
of the pair map. The bundled identity maps, multiplication and inverse
laws, and combined coefficient/index naturality use the production APIs
across independent index and coefficient universes.
-/

open Matrix Matrix.GeneralLinearGroup

namespace MathlibExtTest.StabilizationBlockTests

universe uA uB uC uA' uB' uR uS

section BlockMaps

variable {A : Type uA} {B : Type uB}
    [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B]
variable {R : Type uR} [Semiring R]

/-- Both inclusions retain their active entries, zero cross terms and
actual inactive identity coefficients with heterogeneous block sizes. -/
public theorem block_inclusions_coefficients (g : GL A R) (h : GL B R)
    (i j : A) (k l : B) :
    (↑(blockDiagonalOne A B R g) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inl i) (Sum.inl j) = (↑g : Matrix A A R) i j ∧
    (↑(blockDiagonalOne A B R g) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inl i) (Sum.inr k) = 0 ∧
    (↑(blockDiagonalOne A B R g) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inr k) (Sum.inl i) = 0 ∧
    (↑(blockDiagonalOne A B R g) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inr k) (Sum.inr l) = (if k = l then 1 else 0) ∧
    (↑(blockDiagonalRight A B R h) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inl i) (Sum.inl j) = (if i = j then 1 else 0) ∧
    (↑(blockDiagonalRight A B R h) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inl i) (Sum.inr k) = 0 ∧
    (↑(blockDiagonalRight A B R h) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inr k) (Sum.inl i) = 0 ∧
    (↑(blockDiagonalRight A B R h) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inr k) (Sum.inr l) = (↑h : Matrix B B R) k l := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.fromBlocks_apply₁₁] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inl i) (Sum.inl j))
      (coe_blockDiagonalOne (m := B) g)
  · simpa only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inl i) (Sum.inr k))
      (coe_blockDiagonalOne (m := B) g)
  · simpa only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inr k) (Sum.inl i))
      (coe_blockDiagonalOne (m := B) g)
  · simpa only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inr k) (Sum.inr l))
      (coe_blockDiagonalOne (m := B) g)
  · simpa only [Matrix.fromBlocks_apply₁₁, Matrix.one_apply] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inl i) (Sum.inl j))
      (coe_blockDiagonalRight (n := A) h)
  · simpa only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inl i) (Sum.inr k))
      (coe_blockDiagonalRight (n := A) h)
  · simpa only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inr k) (Sum.inl i))
      (coe_blockDiagonalRight (n := A) h)
  · simpa only [Matrix.fromBlocks_apply₂₂] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inr k) (Sum.inr l))
      (coe_blockDiagonalRight (n := A) h)

/-- The pair map preserves both original coefficient blocks and has
zero coefficients in both rectangular off-diagonal blocks. -/
public theorem block_pair_coefficients (g : GL A R) (h : GL B R)
    (i j : A) (k l : B) :
    (↑(blockDiagonalHom A B R (g, h)) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inl i) (Sum.inl j) = (↑g : Matrix A A R) i j ∧
    (↑(blockDiagonalHom A B R (g, h)) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inl i) (Sum.inr k) = 0 ∧
    (↑(blockDiagonalHom A B R (g, h)) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inr k) (Sum.inl i) = 0 ∧
    (↑(blockDiagonalHom A B R (g, h)) : Matrix (A ⊕ B) (A ⊕ B) R)
        (Sum.inr k) (Sum.inr l) = (↑h : Matrix B B R) k l := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.fromBlocks_apply₁₁] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inl i) (Sum.inl j))
      (coe_blockDiagonalHom g h)
  · simpa only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inl i) (Sum.inr k))
      (coe_blockDiagonalHom g h)
  · simpa only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inr k) (Sum.inl i))
      (coe_blockDiagonalHom g h)
  · simpa only [Matrix.fromBlocks_apply₂₂] using congrArg
      (fun M : Matrix (A ⊕ B) (A ⊕ B) R => M (Sum.inr k) (Sum.inr l))
      (coe_blockDiagonalHom g h)

/-- The pair map restricts to both block inclusions as bundled maps,
using the actual product-group injections with an identity component. -/
public theorem identity_block_maps :
    (blockDiagonalHom A B R).comp (MonoidHom.inl (GL A R) (GL B R)) =
        blockDiagonalOne A B R ∧
    (blockDiagonalHom A B R).comp (MonoidHom.inr (GL A R) (GL B R)) =
        blockDiagonalRight A B R := by
  constructor
  · apply MonoidHom.ext
    intro g
    simpa only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply] using
      (blockDiagonalHom_one_right (m := B) g)
  · apply MonoidHom.ext
    intro h
    simpa only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply] using
      (blockDiagonalHom_one_left (n := A) h)

/-- Products and actual inverses of pairs are respected over arbitrary
semirings, and the two whole block images commute in the target group. -/
public theorem pair_group_laws (g₁ g₂ : GL A R) (h₁ h₂ : GL B R) :
    blockDiagonalHom A B R (g₁, h₁) * blockDiagonalHom A B R (g₂, h₂) =
        blockDiagonalHom A B R (g₁ * g₂, h₁ * h₂) ∧
    (blockDiagonalHom A B R (g₁, h₁))⁻¹ =
        blockDiagonalHom A B R (g₁⁻¹, h₁⁻¹) ∧
    Commute (blockDiagonalOne A B R g₁) (blockDiagonalRight A B R h₁) := by
  exact ⟨(map_mul (blockDiagonalHom A B R) (g₁, h₁) (g₂, h₂)).symm,
    (map_inv (blockDiagonalHom A B R) (g₁, h₁)).symm,
    commute_blockDiagonalOne_blockDiagonalRight g₁ h₁⟩

variable {A' : Type uA'} {B' : Type uB'}
    [DecidableEq A'] [DecidableEq B'] [Fintype A'] [Fintype B']
variable {S : Type uS} [Semiring S]

/-- Reindexing both block carriers after a coefficient map agrees with
mapping the original reindexed matrix and then inserting its identity block. -/
public theorem left_reindex_coefficient_naturality
    (eA : A ≃ A') (eB : B ≃ B') (f : R →+* S) (g : GL A R) :
    reindexMulEquiv (A := S) (Equiv.sumCongr eA eB)
        (mapRingHom f (blockDiagonalOne A B R g)) =
      blockDiagonalOne A' B' S (mapRingHom f (reindexMulEquiv (A := R) eA g)) := by
  rw [← blockDiagonalOne_mapRingHom_apply]
  rw [blockDiagonalOne_reindex, reindexMulEquiv_mapRingHom_apply]

/-- The right inclusion is natural under genuine equivalences of both
index summands, including the independent inactive identity coordinates. -/
public theorem right_reindex_naturality (eA : A ≃ A') (eB : B ≃ B') (h : GL B R) :
    reindexMulEquiv (Equiv.sumCongr eA eB) (blockDiagonalRight A B R h) =
      blockDiagonalRight A' B' R (reindexMulEquiv eB h) := by
  apply Units.ext
  simp only [coe_reindexMulEquiv, coe_blockDiagonalRight]
  ext i j
  dsimp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp only [Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
      Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
    exact if_congr eA.symm.injective.eq_iff rfl rfl
  · simp only [Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · simp only [Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · simp only [Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr,
      Matrix.fromBlocks_apply₂₂, Matrix.submatrix_apply]

end BlockMaps

section Successor

variable {R : Type uR} [Semiring R] {S : Type uS} [Semiring S]

/-- The successor enumeration retains every old coefficient, both zero
cross blocks, and the literal new identity coordinate. -/
public theorem successor_coefficients {q : ℕ} (g : GL (Fin q) R) (i j : Fin q) :
    (↑(stabilization R g) : Matrix (Fin (q + 1)) (Fin (q + 1)) R)
        ((finSumFinEquiv (m := q) (n := 1)) (Sum.inl i))
        ((finSumFinEquiv (m := q) (n := 1)) (Sum.inl j)) =
      (↑g : Matrix (Fin q) (Fin q) R) i j ∧
    (↑(stabilization R g) : Matrix (Fin (q + 1)) (Fin (q + 1)) R)
        ((finSumFinEquiv (m := q) (n := 1)) (Sum.inl i))
        ((finSumFinEquiv (m := q) (n := 1)) (Sum.inr (0 : Fin 1))) = 0 ∧
    (↑(stabilization R g) : Matrix (Fin (q + 1)) (Fin (q + 1)) R)
        ((finSumFinEquiv (m := q) (n := 1)) (Sum.inr (0 : Fin 1)))
        ((finSumFinEquiv (m := q) (n := 1)) (Sum.inl i)) = 0 ∧
    (↑(stabilization R g) : Matrix (Fin (q + 1)) (Fin (q + 1)) R)
        ((finSumFinEquiv (m := q) (n := 1)) (Sum.inr (0 : Fin 1)))
        ((finSumFinEquiv (m := q) (n := 1)) (Sum.inr (0 : Fin 1))) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁] using congrArg
      (fun M : Matrix (Fin (q + 1)) (Fin (q + 1)) R =>
        M ((finSumFinEquiv (m := q) (n := 1)) (Sum.inl i))
          ((finSumFinEquiv (m := q) (n := 1)) (Sum.inl j)))
      (coe_stabilization g)
  · simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using congrArg
      (fun M : Matrix (Fin (q + 1)) (Fin (q + 1)) R =>
        M ((finSumFinEquiv (m := q) (n := 1)) (Sum.inl i))
          ((finSumFinEquiv (m := q) (n := 1)) (Sum.inr (0 : Fin 1))))
      (coe_stabilization g)
  · simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using congrArg
      (fun M : Matrix (Fin (q + 1)) (Fin (q + 1)) R =>
        M ((finSumFinEquiv (m := q) (n := 1)) (Sum.inr (0 : Fin 1)))
          ((finSumFinEquiv (m := q) (n := 1)) (Sum.inl i)))
      (coe_stabilization g)
  · simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, ite_true] using congrArg
      (fun M : Matrix (Fin (q + 1)) (Fin (q + 1)) R =>
        M ((finSumFinEquiv (m := q) (n := 1)) (Sum.inr (0 : Fin 1)))
          ((finSumFinEquiv (m := q) (n := 1)) (Sum.inr (0 : Fin 1))))
      (coe_stabilization g)

/-- Coefficient change and a real old-index permutation commute with
successor stabilization, which still reflects equality of original matrices. -/
public theorem successor_naturality_and_reflection {q : ℕ}
    (f : R →+* S) (e : Equiv.Perm (Fin q)) (g h : GL (Fin q) R) :
    stabilization S (reindexMulEquiv (A := S) e (mapRingHom f g)) =
        mapRingHom f (stabilization R (reindexMulEquiv (A := R) e g)) ∧
    (stabilization R (reindexMulEquiv (A := R) e g) =
        stabilization R (reindexMulEquiv (A := R) e h) ↔ g = h) := by
  constructor
  · rw [reindexMulEquiv_mapRingHom_apply, stabilization_mapRingHom_apply]
  · constructor
    · intro he
      exact (reindexMulEquiv (A := R) e).injective
        (stabilization_injective he)
    · intro he
      rw [he]

end Successor

section BlockReindexCoherence

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [Fintype A] [Fintype B] [Fintype C]
variable {R : Type uR} [Semiring R]

/-- The full pair interchange accepts independent block and coefficient worlds. -/
public theorem pair_sum_interchange (g : GL A R) (h : GL B R) :
    reindexMulEquiv (Equiv.sumComm A B) (blockDiagonalHom A B R (g, h)) =
      blockDiagonalHom B A R (h, g) :=
  blockDiagonalHom_sumComm g h

/-- Association retains all three independent finite block carriers over a semiring. -/
public theorem triple_sum_association (g : GL A R) (h : GL B R) (k : GL C R) :
    reindexMulEquiv (Equiv.sumAssoc A B C)
      (blockDiagonalHom (A ⊕ B) C R (blockDiagonalHom A B R (g, h), k)) =
      blockDiagonalHom A (B ⊕ C) R (g, blockDiagonalHom B C R (h, k)) :=
  blockDiagonalHom_sumAssoc g h k

/-- Unequal finite blocks in independent universes use both laws with natural coefficients. -/
public theorem natural_coefficient_coherence
    (g : GL (ULift.{uA} (Fin 2)) ℕ) (h : GL (ULift.{uB} (Fin 3)) ℕ)
    (k : GL (ULift.{uC} (Fin 4)) ℕ) :
    reindexMulEquiv (Equiv.sumComm _ _)
      (blockDiagonalHom (ULift.{uA} (Fin 2)) (ULift.{uB} (Fin 3)) ℕ (g, h)) =
        blockDiagonalHom (ULift.{uB} (Fin 3)) (ULift.{uA} (Fin 2)) ℕ (h, g) ∧
    reindexMulEquiv (Equiv.sumAssoc _ _ _)
      (blockDiagonalHom _ _ ℕ (blockDiagonalHom _ _ ℕ (g, h), k)) =
        blockDiagonalHom _ _ ℕ (g, blockDiagonalHom _ _ ℕ (h, k)) :=
  ⟨blockDiagonalHom_sumComm g h, blockDiagonalHom_sumAssoc g h k⟩

end BlockReindexCoherence

-- Distinct lifted index universes and noncommutative matrix coefficients.
example (g : GL (ULift.{uA} (Fin 2)) (Matrix (Fin 2) (Fin 2) ℕ))
    (h : GL (ULift.{uB} (Fin 3)) (Matrix (Fin 2) (Fin 2) ℕ)) :
    Commute
      (blockDiagonalOne (ULift.{uA} (Fin 2)) (ULift.{uB} (Fin 3))
        (Matrix (Fin 2) (Fin 2) ℕ) g)
      (blockDiagonalRight (ULift.{uA} (Fin 2)) (ULift.{uB} (Fin 3))
        (Matrix (Fin 2) (Fin 2) ℕ) h) :=
  (pair_group_laws g g h h).2.2

section LegacyRingMigration

/-- The old Ring wrapper uses the same homomorphism and keeps both matrix fields,
with independent block carriers and the original inverse blocks. -/
public theorem legacy_block_diagonal_bridge
    {A : Type uA} {B : Type uB}
    [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B]
    {R : Type uR} [Ring R] (g : GL A R) (h : GL B R) :
    BlockElementary.blockDiagonal g h = blockDiagonalHom A B R (g, h) ∧
    (↑(BlockElementary.blockDiagonal g h) : Matrix (A ⊕ B) (A ⊕ B) R) =
      fromBlocks (↑g : Matrix A A R) (0 : Matrix A B R) (0 : Matrix B A R)
        (↑h : Matrix B B R) ∧
    (↑((BlockElementary.blockDiagonal g h)⁻¹) : Matrix (A ⊕ B) (A ⊕ B) R) =
      fromBlocks (↑(g⁻¹) : Matrix A A R) (0 : Matrix A B R) (0 : Matrix B A R)
        (↑(h⁻¹) : Matrix B B R) := by
  exact ⟨BlockElementary.blockDiagonal_eq_blockDiagonalHom g h,
    BlockElementary.coe_blockDiagonal g h, BlockElementary.coe_blockDiagonal_inv g h⟩

end LegacyRingMigration

end MathlibExtTest.StabilizationBlockTests

#check @MathlibExtTest.StabilizationBlockTests.block_inclusions_coefficients
#print axioms MathlibExtTest.StabilizationBlockTests.block_inclusions_coefficients
#check @MathlibExtTest.StabilizationBlockTests.block_pair_coefficients
#print axioms MathlibExtTest.StabilizationBlockTests.block_pair_coefficients
#check @MathlibExtTest.StabilizationBlockTests.identity_block_maps
#print axioms MathlibExtTest.StabilizationBlockTests.identity_block_maps
#check @MathlibExtTest.StabilizationBlockTests.pair_group_laws
#print axioms MathlibExtTest.StabilizationBlockTests.pair_group_laws
#check @MathlibExtTest.StabilizationBlockTests.left_reindex_coefficient_naturality
#print axioms MathlibExtTest.StabilizationBlockTests.left_reindex_coefficient_naturality
#check @MathlibExtTest.StabilizationBlockTests.right_reindex_naturality
#print axioms MathlibExtTest.StabilizationBlockTests.right_reindex_naturality
#check @MathlibExtTest.StabilizationBlockTests.successor_coefficients
#print axioms MathlibExtTest.StabilizationBlockTests.successor_coefficients
#check @MathlibExtTest.StabilizationBlockTests.successor_naturality_and_reflection
#print axioms MathlibExtTest.StabilizationBlockTests.successor_naturality_and_reflection
#check @MathlibExtTest.StabilizationBlockTests.legacy_block_diagonal_bridge
#print axioms MathlibExtTest.StabilizationBlockTests.legacy_block_diagonal_bridge
