/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.InterleavedUnitConjugators
public import MathlibExt.KTheory.Ring.StableGeneralLinear.InactivePermutationFactor
public import MathlibExt.KTheory.Ring.StableGeneralLinear.StabilizeTo

/-!
# Actual inactive differences of finite unit comparisons

Consecutive computed left-unit conjugators are placed at one common finite
matrix rank. Their index permutations agree on every original active
coordinate, using the SAME fixed slot enumeration. Their quotient is an
even permutation fixing the whole active set. The previously constructed
perfect inactive factor therefore recovers the actual difference of the
original stable elementary matrices. No inactive-factor or compatibility
witness is supplied by the caller.
-/

set_option autoImplicit false

noncomputable section

open Matrix CategoryTheory

universe u

namespace AlgebraicKTheory.StableGL

/-- The actual doubled finite rank of the stage-n unit conjugator. -/
public def leftUnitMatrixRank (n : ℕ) : ℕ :=
  n * Fintype.card BlockPairIndex.{u} + n * Fintype.card BlockPairIndex.{u}

private theorem leftUnitMatrixRank_eq_computed (n : ℕ) :
    leftUnitMatrixRank.{u} n =
      n * Fintype.card BlockPairIndex.{u} + n * Fintype.card BlockPairIndex.{u} := by
  simp only [leftUnitMatrixRank]

/-- The original doubled rank evaluates by its original two-slot formula. -/
public theorem leftUnitMatrixRank_eq (n : ℕ) :
    leftUnitMatrixRank.{u} n =
      n * Fintype.card BlockPairIndex.{u} + n * Fintype.card BlockPairIndex.{u} :=
  leftUnitMatrixRank_eq_computed.{u} n

/-- A common original finite rank for the two consecutive matrices. -/
public def leftUnitCommonRank (n : ℕ) : ℕ :=
  leftUnitMatrixRank.{u} n + leftUnitMatrixRank.{u} (n + 1)

/-- The original finite active rank fits in the actual common rank,
using only the proved two-slot index cardinality. -/
public theorem leftUnitCommonRank_bound (n : ℕ) : n ≤ leftUnitCommonRank.{u} n := by
  have hcard : Fintype.card BlockPairIndex.{u} = 2 := by
    simp [BlockPairIndex]
  simp only [leftUnitCommonRank, leftUnitMatrixRank, hcard]
  omega

/-- The previous actual permutation, with only trailing identities added. -/
public def leftUnitOldCommonPermutation (n : ℕ) :
    Equiv.Perm (Fin (leftUnitCommonRank.{u} n)) :=
  finitePermutationStabilization (leftUnitMatrixRank.{u} (n + 1))
    (leftBlockDoubledPermutation.{u} n)

/-- The next actual permutation at the same finite rank. Reindexing only
uses the proved equality between the two orders of the rank sum. -/
public def leftUnitNewCommonPermutation (n : ℕ) :
    Equiv.Perm (Fin (leftUnitCommonRank.{u} n)) :=
  (finCongr (Nat.add_comm (leftUnitMatrixRank.{u} (n + 1))
    (leftUnitMatrixRank.{u} n))).permCongr
      (finitePermutationStabilization (leftUnitMatrixRank.{u} n)
        (leftBlockDoubledPermutation.{u} (n + 1)))

private theorem oldCommon_active_val (n : ℕ)
    (x : Fin (leftUnitCommonRank.{u} n)) (hx : x.val < n) :
    (leftUnitOldCommonPermutation.{u} n x).val =
      (MatrixDiagram.equivFinMatrix (ι := BlockPairIndex.{u}) (ULift.up (0 : Fin 2))).val +
        Fintype.card BlockPairIndex.{u} * x.val := by
  let i : Fin n := ⟨x.val, hx⟩
  let a := leftBlockActiveIndex.{u} n i
  have ha : Fin.castAdd (leftUnitMatrixRank.{u} (n + 1)) a = x :=
    Fin.ext (leftBlockActiveIndex_val n i)
  have hp := congrArg (fun z : Fin (leftUnitCommonRank.{u} n) =>
    (leftUnitOldCommonPermutation.{u} n z).val) ha
  have hact : leftUnitOldCommonPermutation.{u} n
      (Fin.castAdd (leftUnitMatrixRank.{u} (n + 1)) a) =
    Fin.castAdd (leftUnitMatrixRank.{u} (n + 1)) (leftBlockDoubledPermutation.{u} n a) :=
    finitePermutationStabilization_castAdd _ _ a
  exact hp.symm.trans ((congrArg Fin.val hact).trans
    (leftBlockDoubledPermutation_active_val n i))

private theorem newCommon_active_val (n : ℕ)
    (x : Fin (leftUnitCommonRank.{u} n)) (hx : x.val < n) :
    (leftUnitNewCommonPermutation.{u} n x).val =
      (MatrixDiagram.equivFinMatrix (ι := BlockPairIndex.{u}) (ULift.up (0 : Fin 2))).val +
        Fintype.card BlockPairIndex.{u} * x.val := by
  let i : Fin (n + 1) := ⟨x.val, hx.trans (Nat.lt_succ_self n)⟩
  let a := leftBlockActiveIndex.{u} (n + 1) i
  let e := finCongr (Nat.add_comm (leftUnitMatrixRank.{u} (n + 1))
    (leftUnitMatrixRank.{u} n))
  have ha : e (Fin.castAdd (leftUnitMatrixRank.{u} n) a) = x :=
    Fin.ext (leftBlockActiveIndex_val (n + 1) i)
  have hp := congrArg (fun z : Fin (leftUnitCommonRank.{u} n) =>
    (leftUnitNewCommonPermutation.{u} n z).val) ha
  have hact : leftUnitNewCommonPermutation.{u} n
      (e (Fin.castAdd (leftUnitMatrixRank.{u} n) a)) =
      e (Fin.castAdd (leftUnitMatrixRank.{u} n)
        (leftBlockDoubledPermutation.{u} (n + 1) a)) := by
    change e.permCongr (finitePermutationStabilization (leftUnitMatrixRank.{u} n)
      (leftBlockDoubledPermutation.{u} (n + 1)))
        (e (Fin.castAdd (leftUnitMatrixRank.{u} n) a)) = _
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact congrArg e (finitePermutationStabilization_castAdd _ _ a)
  exact hp.symm.trans ((congrArg Fin.val hact).trans
    (leftBlockDoubledPermutation_active_val (n + 1) i))

/-- The computed consecutive difference of the two original index permutations. -/
public def leftUnitDifferencePermutation (n : ℕ) :
    Equiv.Perm (Fin (leftUnitCommonRank.{u} n)) :=
  (leftUnitNewCommonPermutation.{u} n)⁻¹ * leftUnitOldCommonPermutation.{u} n

/-- The whole original active coordinate set is fixed by that actual difference. -/
public theorem leftUnitDifferencePermutation_fixed (n : ℕ)
    (x : Fin (leftUnitCommonRank.{u} n)) (hx : x.val < n) :
    leftUnitDifferencePermutation.{u} n x = x := by
  have hxy : leftUnitOldCommonPermutation.{u} n x = leftUnitNewCommonPermutation.{u} n x :=
    Fin.ext ((oldCommon_active_val n x hx).trans (newCommon_active_val n x hx).symm)
  change (leftUnitNewCommonPermutation.{u} n).symm
    (leftUnitOldCommonPermutation.{u} n x) = x
  rw [hxy, Equiv.symm_apply_apply]

/-- The difference remains even at the common finite rank. -/
public theorem leftUnitDifferencePermutation_sign (n : ℕ) :
    Equiv.Perm.sign (leftUnitDifferencePermutation.{u} n) = 1 := by
  have hold : Equiv.Perm.sign (leftUnitOldCommonPermutation.{u} n) = 1 :=
    (finitePermutationStabilization_sign _ _).trans (leftBlockDoubledPermutation_sign n)
  have hnew : Equiv.Perm.sign (leftUnitNewCommonPermutation.{u} n) = 1 := by
    change Equiv.Perm.sign
      ((finCongr (Nat.add_comm
        ((n + 1) * Fintype.card BlockPairIndex.{u} +
          (n + 1) * Fintype.card BlockPairIndex.{u})
        (n * Fintype.card BlockPairIndex.{u} +
          n * Fintype.card BlockPairIndex.{u}))).permCongr
          (finitePermutationStabilization
            (n * Fintype.card BlockPairIndex.{u} +
              n * Fintype.card BlockPairIndex.{u})
            (leftBlockDoubledPermutation.{u} (n + 1)))) = 1
    rw [Equiv.Perm.sign_permCongr, finitePermutationStabilization_sign,
      leftBlockDoubledPermutation_sign]
  change Equiv.Perm.sign
    ((leftUnitNewCommonPermutation.{u} n)⁻¹ * leftUnitOldCommonPermutation.{u} n) = 1
  rw [map_mul, map_inv, hnew, hold, inv_one, mul_one]

variable (R : Type u) [Ring R]

private theorem oldCommon_matrix (n : ℕ) :
    StableGL.of (Matrix.GeneralLinearGroup.permutationUnitsHom R _
      (leftUnitOldCommonPermutation.{u} n)) =
        (leftBlockElementaryConjugator R n : StableGL R) := by
  change StableGL.of (Matrix.GeneralLinearGroup.permutationUnitsHom R _
    (finitePermutationStabilization (leftUnitMatrixRank.{u} (n + 1))
      (leftBlockDoubledPermutation.{u} n))) = _
  rw [finitePermutationStabilization_matrix, StableGL.of_blockStabilization]
  exact (leftBlockElementaryConjugator_matrix R n).symm

private theorem newCommon_matrix (n : ℕ) :
    StableGL.of (Matrix.GeneralLinearGroup.permutationUnitsHom R _
      (leftUnitNewCommonPermutation.{u} n)) =
        (leftBlockElementaryConjugator R (n + 1) : StableGL R) := by
  change StableGL.of (Matrix.GeneralLinearGroup.permutationUnitsHom R
    (Fin ((n * Fintype.card BlockPairIndex.{u} +
      n * Fintype.card BlockPairIndex.{u}) +
      ((n + 1) * Fintype.card BlockPairIndex.{u} +
        (n + 1) * Fintype.card BlockPairIndex.{u})))
    ((finCongr (Nat.add_comm
      ((n + 1) * Fintype.card BlockPairIndex.{u} +
        (n + 1) * Fintype.card BlockPairIndex.{u})
      (n * Fintype.card BlockPairIndex.{u} +
        n * Fintype.card BlockPairIndex.{u}))).permCongr
        (finitePermutationStabilization
          (n * Fintype.card BlockPairIndex.{u} +
            n * Fintype.card BlockPairIndex.{u})
          (leftBlockDoubledPermutation.{u} (n + 1))))) = _
  rw [← Matrix.GeneralLinearGroup.permutationUnitsHom_reindex,
    StableGL.of_reindex_finCongr, finitePermutationStabilization_matrix,
    StableGL.of_blockStabilization]
  exact (leftBlockElementaryConjugator_matrix R (n + 1)).symm

/-- The actual even difference permutation represents precisely the
original stable difference of consecutive elementary unit matrices. -/
public theorem leftUnitDifferencePermutation_matrix (n : ℕ) :
    StableGL.of (Matrix.GeneralLinearGroup.permutationUnitsHom R _
      (leftUnitDifferencePermutation.{u} n)) =
      (leftBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹ *
        (leftBlockElementaryConjugator R n : StableGL R) := by
  change StableGL.of (Matrix.GeneralLinearGroup.permutationUnitsHom R _
    ((leftUnitNewCommonPermutation.{u} n)⁻¹ * leftUnitOldCommonPermutation.{u} n)) = _
  rw [map_mul, map_inv, StableGL.of_mul, StableGL.of_inv,
    oldCommon_matrix R n, newCommon_matrix R n]

/-- The actual original active set at the common matrix rank. -/
public abbrev leftUnitActiveSet (n : ℕ) : Set (Fin (leftUnitCommonRank.{u} n)) :=
  {x | x.val < n}

/-- The genuine perfect group containing the computed inactive difference. -/
public abbrev LeftUnitDifferencePerfectGroup (n : ℕ) : Type u :=
  InactivePerfectMatrixGroup R (leftUnitCommonRank.{u} n) (leftUnitActiveSet.{u} n)

/-- Perfectness is derived for this actual inactive image, not a caller input. -/
public theorem leftUnitDifferencePerfectGroup_isPerfect (n : ℕ) :
    Group.IsPerfect (LeftUnitDifferencePerfectGroup R n) :=
  inactivePerfectMatrixGroup_isPerfect R _ _

/-- The original consecutive difference gives a computed element of that
perfect inactive group, using its proved fixed set and sign. -/
public def leftUnitDifferencePerfectFactor (n : ℕ) : LeftUnitDifferencePerfectGroup R n :=
  inactivePermutationMatrixFactor R _ _ (leftUnitDifferencePermutation.{u} n)
    (fun x hx => leftUnitDifferencePermutation_fixed n x hx)
    (leftUnitDifferencePermutation_sign n)

/-- Its ambient image is the exact original stable consecutive difference. -/
public theorem leftUnitDifferencePerfectFactor_reconstruct (n : ℕ) :
    inactiveStableMatrixHom R (leftUnitCommonRank.{u} n) (leftUnitActiveSet.{u} n)
        (leftUnitDifferencePerfectFactor R n).val =
      (leftBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹ *
      (leftBlockElementaryConjugator R n : StableGL R) := by
  change inactiveStableMatrixHom R (leftUnitCommonRank.{u} n) (leftUnitActiveSet.{u} n)
    (inactivePermutationMatrixFactor R (leftUnitCommonRank.{u} n) (leftUnitActiveSet.{u} n)
      (leftUnitDifferencePermutation.{u} n)
      (fun x hx => leftUnitDifferencePermutation_fixed n x hx)
      (leftUnitDifferencePermutation_sign n)).val = _
  exact (inactivePermutationMatrixFactor_reconstruct R (leftUnitCommonRank.{u} n)
    (leftUnitActiveSet.{u} n) (leftUnitDifferencePermutation.{u} n)
    (fun x hx => leftUnitDifferencePermutation_fixed n x hx)
    (leftUnitDifferencePermutation_sign n)).trans
      (leftUnitDifferencePermutation_matrix R n)

end AlgebraicKTheory.StableGL

end
