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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.RankOneEmbedding
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Whitehead

/-!
# Rank-one correction membership in the elementary subgroup

The rank-one correction `rankOneCorrection n R p` is a reindexing of
`blockDiagonalOne (Fin 1 ⊕ Fin 1) (Fin n) R (diagUnit p⁻¹)` via an explicit
rotation equivalence, hence lies in `elementarySubgroup`.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix

variable {R : Type*} [Ring R]

private def rotationEquiv (n : ℕ) : (Fin 1 ⊕ Fin 1) ⊕ Fin n ≃ (Fin 1 ⊕ Fin n) ⊕ Fin 1 where
  toFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr b) => Sum.inr b
    | Sum.inr c => Sum.inl (Sum.inr c)
  invFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr c) => Sum.inr c
    | Sum.inr b => Sum.inl (Sum.inr b)
  left_inv := by
    intro x
    match x with
    | Sum.inl (Sum.inl _) => rfl
    | Sum.inl (Sum.inr _) => rfl
    | Sum.inr _ => rfl
  right_inv := by
    intro x
    match x with
    | Sum.inl (Sum.inl _) => rfl
    | Sum.inl (Sum.inr _) => rfl
    | Sum.inr _ => rfl

private def finOneSumFinEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  ((Equiv.cast (congrArg Fin (Nat.add_comm n 1))).trans
    (finSumFinEquiv (m := 1) (n := n)).symm).symm

private def targetEquiv (n : ℕ) : (Fin 1 ⊕ Fin 1) ⊕ Fin n ≃ Fin (n + 1) ⊕ Fin 1 :=
  (rotationEquiv n).trans (Equiv.sumCongr (finOneSumFinEquiv n) (Equiv.refl _))

private lemma finOneSumFinEquiv_symm_zero (n : ℕ) :
    (finOneSumFinEquiv n).symm (0 : Fin (n + 1)) = Sum.inl (0 : Fin 1) := by
  have h_eq : (finOneSumFinEquiv n).symm (0 : Fin (n + 1)) =
      finSumFinEquiv.symm (Equiv.cast (congrArg Fin (Nat.add_comm n 1)) (0 : Fin (n + 1))) := by
    simp [finOneSumFinEquiv, Equiv.trans_apply]
  have h_cast : Equiv.cast (congrArg Fin (Nat.add_comm n 1)) (0 : Fin (n + 1)) =
      Fin.castAdd n (0 : Fin 1) := by
    apply Fin.ext
    rw [Equiv.cast_apply]
    rw [← Fin.cast_eq_cast (h := Nat.add_comm n 1)]
    simp
  rw [h_eq, h_cast]
  exact finSumFinEquiv_symm_apply_castAdd _

private lemma finOneSumFinEquiv_symm_succ (n : ℕ) (i : Fin n) :
    (finOneSumFinEquiv n).symm (Fin.succ i) = Sum.inr i := by
  have h_eq : (finOneSumFinEquiv n).symm (Fin.succ i) =
      finSumFinEquiv.symm (Equiv.cast (congrArg Fin (Nat.add_comm n 1)) (Fin.succ i)) := by
    simp [finOneSumFinEquiv, Equiv.trans_apply]
  have h_cast : Equiv.cast (congrArg Fin (Nat.add_comm n 1)) (Fin.succ i) =
      Fin.natAdd 1 i := by
    apply Fin.ext
    rw [Equiv.cast_apply]
    rw [← Fin.cast_eq_cast (h := Nat.add_comm n 1)]
    simp [Fin.val_natAdd, Fin.val_succ, Nat.add_comm]
  rw [h_eq, h_cast]
  exact finSumFinEquiv_symm_apply_natAdd _

private lemma targetEquiv_symm_inl_zero (n : ℕ) :
    (targetEquiv n).symm (Sum.inl (0 : Fin (n + 1))) = Sum.inl (Sum.inl (0 : Fin 1)) := by
  simp [targetEquiv, rotationEquiv, finOneSumFinEquiv_symm_zero]

private lemma targetEquiv_symm_inl_succ (n : ℕ) (i : Fin n) :
    (targetEquiv n).symm (Sum.inl (Fin.succ i)) = Sum.inr i := by
  simp [targetEquiv, rotationEquiv, finOneSumFinEquiv_symm_succ]

private lemma targetEquiv_symm_inr (n : ℕ) (b : Fin 1) :
    (targetEquiv n).symm (Sum.inr b) = Sum.inl (Sum.inr b) := by
  simp [targetEquiv, rotationEquiv]

attribute [-simp] map_inv in
private lemma rankOneCorrection_eq_reindex (n : ℕ) (R : Type*) [Ring R]
    (p : GL (Fin 1) R) :
    rankOneCorrection n R p =
      reindexMulEquiv (targetEquiv n)
        (blockDiagonalOne (Fin 1 ⊕ Fin 1) (Fin n) R (diagUnit p⁻¹)) := by
  have h_inv : (rankOneEmbedding n R p)⁻¹ = rankOneEmbedding n R (p⁻¹) := by
    rw [← map_inv]
  have h_rank : rankOneEmbedding n R (p⁻¹) =
      reindexMulEquiv (finOneSumFinEquiv n)
        (blockDiagonalOne (Fin 1) (Fin n) R (p⁻¹)) := by
    simp [rankOneEmbedding, finOneSumFinEquiv]
  apply Units.ext
  ext x y
  simp only [rankOneCorrection, h_inv, h_rank,
    BlockElementary.blockDiagonal_eq_blockDiagonalHom, coe_blockDiagonalHom,
    coe_blockDiagonalOne, coe_diagUnit, coe_reindexMulEquiv]
  -- expose target reindex
  change
    (fromBlocks (Matrix.reindex (finOneSumFinEquiv n) (finOneSumFinEquiv n)
          (fromBlocks (↑(p⁻¹) : Matrix (Fin 1) (Fin 1) R) 0 0 1) : Matrix (Fin (n+1)) (Fin (n+1)) R)
        0 0 (↑p : Matrix (Fin 1) (Fin 1) R)) x y =
    (Matrix.reindex (targetEquiv n) (targetEquiv n)
        (fromBlocks (fromBlocks (↑(p⁻¹) : Matrix (Fin 1) (Fin 1) R) 0 0
            (↑p : Matrix (Fin 1) (Fin 1) R)) 0 0 1) :
          Matrix (Fin (n + 1) ⊕ Fin 1) (Fin (n + 1) ⊕ Fin 1) R) x y
  simp only [fromBlocks]
  rcases x with x | b
  · rcases y with y | b'
    · -- both in Fin (n+1): split via 0 / succ
      cases x using Fin.cases with
      | zero =>
        cases y using Fin.cases with
        | zero =>
          have hx : (finOneSumFinEquiv n).symm (0 : Fin (n+1)) = Sum.inl (0 : Fin 1) :=
            finOneSumFinEquiv_symm_zero n
          have htx : (targetEquiv n).symm (Sum.inl (0 : Fin (n+1))) =
              Sum.inl (Sum.inl (0 : Fin 1)) := targetEquiv_symm_inl_zero n
          simp [hx, htx]
        | succ y' =>
          have hx : (finOneSumFinEquiv n).symm (0 : Fin (n+1)) = Sum.inl (0 : Fin 1) :=
            finOneSumFinEquiv_symm_zero n
          have hy : (finOneSumFinEquiv n).symm (Fin.succ y') = Sum.inr y' :=
            finOneSumFinEquiv_symm_succ n y'
          have htx : (targetEquiv n).symm (Sum.inl (0 : Fin (n+1))) =
              Sum.inl (Sum.inl (0 : Fin 1)) := targetEquiv_symm_inl_zero n
          have hty : (targetEquiv n).symm (Sum.inl (Fin.succ y')) = Sum.inr y' :=
              targetEquiv_symm_inl_succ n y'
          simp [hx, hy, htx, hty]
      | succ x' =>
        cases y using Fin.cases with
        | zero =>
          have hx : (finOneSumFinEquiv n).symm (Fin.succ x') = Sum.inr x' :=
            finOneSumFinEquiv_symm_succ n x'
          have hy : (finOneSumFinEquiv n).symm (0 : Fin (n+1)) = Sum.inl (0 : Fin 1) :=
            finOneSumFinEquiv_symm_zero n
          have htx : (targetEquiv n).symm (Sum.inl (Fin.succ x')) = Sum.inr x' :=
            targetEquiv_symm_inl_succ n x'
          have hty : (targetEquiv n).symm (Sum.inl (0 : Fin (n+1))) =
              Sum.inl (Sum.inl (0 : Fin 1)) := targetEquiv_symm_inl_zero n
          simp [hx, hy, htx, hty]
        | succ y' =>
          have hx : (finOneSumFinEquiv n).symm (Fin.succ x') = Sum.inr x' :=
            finOneSumFinEquiv_symm_succ n x'
          have hy : (finOneSumFinEquiv n).symm (Fin.succ y') = Sum.inr y' :=
            finOneSumFinEquiv_symm_succ n y'
          have htx : (targetEquiv n).symm (Sum.inl (Fin.succ x')) = Sum.inr x' :=
            targetEquiv_symm_inl_succ n x'
          have hty : (targetEquiv n).symm (Sum.inl (Fin.succ y')) = Sum.inr y' :=
            targetEquiv_symm_inl_succ n y'
          simp [hx, hy, htx, hty]
    · -- x in Fin (n+1), y in Fin 1 (right block) : off-diagonal 0
      cases x using Fin.cases with
      | zero =>
        have htx : (targetEquiv n).symm (Sum.inl (0 : Fin (n+1))) =
            Sum.inl (Sum.inl (0 : Fin 1)) := targetEquiv_symm_inl_zero n
        have hty : (targetEquiv n).symm (Sum.inr b') = Sum.inl (Sum.inr b') :=
          targetEquiv_symm_inr n b'
        simp [htx, hty]
      | succ x' =>
        have htx : (targetEquiv n).symm (Sum.inl (Fin.succ x')) = Sum.inr x' :=
          targetEquiv_symm_inl_succ n x'
        have hty : (targetEquiv n).symm (Sum.inr b') = Sum.inl (Sum.inr b') :=
          targetEquiv_symm_inr n b'
        simp [htx, hty]
  · rcases y with y | b'
    · -- x in Fin 1, y in Fin (n+1) : off-diagonal 0
      have htx : (targetEquiv n).symm (Sum.inr b) = Sum.inl (Sum.inr b) :=
        targetEquiv_symm_inr n b
      cases y using Fin.cases with
      | zero =>
        have hty : (targetEquiv n).symm (Sum.inl (0 : Fin (n+1))) =
            Sum.inl (Sum.inl (0 : Fin 1)) := targetEquiv_symm_inl_zero n
        simp [htx, hty]
      | succ y' =>
        have hty : (targetEquiv n).symm (Sum.inl (Fin.succ y')) = Sum.inr y' :=
          targetEquiv_symm_inl_succ n y'
        simp [htx, hty]
    · -- both in right Fin 1 : p block
      have htx : (targetEquiv n).symm (Sum.inr b) = Sum.inl (Sum.inr b) :=
        targetEquiv_symm_inr n b
      have hb : b = (0 : Fin 1) := Subsingleton.elim _ _
      have hb' : b' = (0 : Fin 1) := Subsingleton.elim _ _
      subst hb; subst hb'
      simp [htx]

/-- Rank-one correction lies in the elementary subgroup. -/
theorem rankOneCorrection_mem_elementarySubgroup (n : ℕ) (R : Type*) [Ring R]
    (p : GL (Fin 1) R) :
    rankOneCorrection n R p ∈ elementarySubgroup (Fin (n + 1) ⊕ Fin 1) R := by
  rw [rankOneCorrection_eq_reindex n R p]
  have h1 : diagUnit (p⁻¹) ∈ elementarySubgroup (Fin 1 ⊕ Fin 1) R :=
    diagUnit_mem (p⁻¹)
  have h2 : blockDiagonalOne (Fin 1 ⊕ Fin 1) (Fin n) R (diagUnit p⁻¹) ∈
      elementarySubgroup ((Fin 1 ⊕ Fin 1) ⊕ Fin n) R :=
    BlockElementary.blockDiagonalOne_mem_elementarySubgroup h1
  exact reindexMulEquiv_mem_elementarySubgroup (targetEquiv n) h2

end Matrix.GeneralLinearGroup
