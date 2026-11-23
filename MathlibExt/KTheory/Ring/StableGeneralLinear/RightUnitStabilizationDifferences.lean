/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteUnitStabilizationDifferences
public import MathlibExt.KTheory.Ring.StableGeneralLinear.PermutationStageDifference

/-!
# The original right-unit differences in their actual perfect inactive group

The right-unit conjugator is the ORIGINAL doubled block swap followed by
the ORIGINAL doubled left interleaving. Its second-slot coordinate formula
is independent of the stage. The general prefix-permutation construction
therefore computes its actual consecutive inactive difference, including
the whole ambient matrix equality. Neither a factor nor a homotopy is given.
-/

noncomputable section

open Matrix

universe u

namespace AlgebraicKTheory.StableGL

/-- The actual right-unit permutations and their ORIGINAL second-slot formula. -/
public abbrev rightUnitPermutationStages : PrefixPermutationStages where
  activeRank := id
  activeRank_mono := Nat.le_succ
  rank := leftUnitMatrixRank.{u}
  permutation n :=
    (finCongr ((leftUnitMatrixRank_eq.{u} n).symm)).permCongr
      (rightBlockDoubledPermutation.{u} n)
  rank_bound n := by
    rw [id_eq, leftUnitMatrixRank_eq]
    have hcard : Fintype.card BlockPairIndex.{u} = 2 := by simp [BlockPairIndex]
    rw [hcard]
    omega
  coordinate i :=
    (MatrixDiagram.equivFinMatrix (ι := BlockPairIndex.{u}) (ULift.up (1 : Fin 2))).val +
      Fintype.card BlockPairIndex.{u} * i
  active n i hi := by
    have hi' : i.val < n := by simpa only [id_eq] using hi
    let j : Fin n := ⟨i.val, hi'⟩
    let e := finCongr ((leftUnitMatrixRank_eq.{u} n).symm)
    have h : e (leftBlockActiveIndex.{u} n j) = i := by
      apply Fin.ext
      exact (finCongr_apply_coe ((leftUnitMatrixRank_eq.{u} n).symm)
        (leftBlockActiveIndex.{u} n j)).trans (leftBlockActiveIndex_val n j)
    have hperm :
        ((e.permCongr (rightBlockDoubledPermutation.{u} n))
          (e (leftBlockActiveIndex.{u} n j))).val =
        (rightBlockDoubledPermutation.{u} n (leftBlockActiveIndex.{u} n j)).val := by
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, e, finCongr_apply_coe]
    change ((e.permCongr (rightBlockDoubledPermutation.{u} n)) i).val = _
    exact (congrArg (fun z : Fin (leftUnitMatrixRank.{u} n) =>
      ((e.permCongr (rightBlockDoubledPermutation.{u} n)) z).val) h).symm.trans
        (hperm.trans (rightBlockDoubledPermutation_active_val n j))
  sign n := by
    rw [Equiv.Perm.sign_permCongr]
    exact rightBlockDoubledPermutation_sign n

/-- The actual common matrix rank of two consecutive right-unit conjugators. -/
public abbrev rightUnitCommonRank (n : ℕ) : ℕ := rightUnitPermutationStages.{u}.commonRank n

/-- Every original active coordinate fits in that concrete common rank. -/
public theorem rightUnitCommonRank_bound (n : ℕ) : n ≤ rightUnitCommonRank.{u} n := by
  simpa only [rightUnitCommonRank, PrefixPermutationStages.commonRank,
    rightUnitPermutationStages, id_eq] using
      (rightUnitPermutationStages.{u}.commonRank_bound n)

private theorem rightUnitPermutationStages_activeSet_eq_computed (n : ℕ) :
    rightUnitPermutationStages.{u}.activeSet n =
      initialActiveIndices n (rightUnitCommonRank.{u} n) := by
  apply Set.ext
  intro x
  change x.val < id n ↔ x.val < n
  rw [id_eq]

/-- The original stage's active predicate is the actual initial-coordinate predicate. -/
public theorem rightUnitPermutationStages_activeSet_eq (n : ℕ) :
    rightUnitPermutationStages.{u}.activeSet n =
      initialActiveIndices n (rightUnitCommonRank.{u} n) :=
  rightUnitPermutationStages_activeSet_eq_computed.{u} n

variable (R : Type u) [Ring R]

private theorem rightUnitPermutationStages_matrix (n : ℕ) :
    StableGL.of (GeneralLinearGroup.permutationUnitsHom R
      (Fin (rightUnitPermutationStages.{u}.rank n))
      (rightUnitPermutationStages.{u}.permutation n)) =
        (rightBlockElementaryConjugator R n : StableGL R) := by
  change StableGL.of (GeneralLinearGroup.permutationUnitsHom R
    (Fin (leftUnitMatrixRank.{u} n))
    ((finCongr ((leftUnitMatrixRank_eq.{u} n).symm)).permCongr
      (rightBlockDoubledPermutation.{u} n))) = _
  rw [← GeneralLinearGroup.permutationUnitsHom_reindex, StableGL.of_reindex_finCongr]
  exact (rightBlockElementaryConjugator_matrix R n).symm

/-- The actual perfect inactive image containing the original consecutive difference. -/
public abbrev RightUnitDifferencePerfectGroup (n : ℕ) : Type u :=
  rightUnitPermutationStages.{u}.perfectGroup R n

/-- Perfectness is DERIVED for this actual inactive image. -/
public theorem rightUnitDifferencePerfectGroup_isPerfect (n : ℕ) :
    Group.IsPerfect (RightUnitDifferencePerfectGroup R n) :=
  rightUnitPermutationStages.{u}.perfectGroup_isPerfect R n

/-- The computed element of that actual image, with its sign and fixed set proved. -/
public abbrev rightUnitDifferencePerfectFactor (n : ℕ) : RightUnitDifferencePerfectGroup R n :=
  rightUnitPermutationStages.{u}.perfectFactor R n

private theorem inactiveStableMatrixHom_set_cast
    {N : ℕ} {s t : Set (Fin N)}
    [ds : DecidablePred (· ∈ s)] [dt : DecidablePred (· ∈ t)]
    (h : s = t) (g : GeneralLinearGroup (Equiv.Perm.InactivePaddedIndex s) R) :
    inactiveStableMatrixHom R N t
        (GeneralLinearGroup.reindexMulEquiv
          (Equiv.cast (congrArg (fun q : Set (Fin N) =>
            Equiv.Perm.InactivePaddedIndex q) h)) g) =
      inactiveStableMatrixHom R N s g := by
  cases h
  have hdict : ds = dt := Subsingleton.elim _ _
  cases hdict
  have hreindex :
      GeneralLinearGroup.reindexMulEquiv
        (Equiv.refl (Equiv.Perm.InactivePaddedIndex s)) g = g := by
    apply Units.ext
    simpa only [GeneralLinearGroup.coe_reindexMulEquiv] using
      (Matrix.reindex_refl_refl
        (g.val : Matrix (Equiv.Perm.InactivePaddedIndex s)
          (Equiv.Perm.InactivePaddedIndex s) R))
  simp only [Equiv.cast_refl, hreindex]

/-- The ORIGINAL ambient image is exactly the difference of the ORIGINAL
right-unit conjugators. This is a whole stable matrix equality. -/
public theorem rightUnitDifferencePerfectFactor_reconstruct (n : ℕ) :
    inactiveStableMatrixHom R (rightUnitCommonRank.{u} n)
        (initialActiveIndices n (rightUnitCommonRank.{u} n))
        (GeneralLinearGroup.reindexMulEquiv
          (Equiv.cast (congrArg (fun q : Set (Fin (rightUnitCommonRank.{u} n)) =>
            Equiv.Perm.InactivePaddedIndex q)
              (rightUnitPermutationStages_activeSet_eq.{u} n)))
          (rightUnitDifferencePerfectFactor R n).val) =
      (rightBlockElementaryConjugator R (n + 1) : StableGL R)⁻¹ *
        (rightBlockElementaryConjugator R n : StableGL R) := by
  calc
    _ = inactiveStableMatrixHom R (rightUnitCommonRank.{u} n)
          (rightUnitPermutationStages.{u}.activeSet n)
          (rightUnitDifferencePerfectFactor R n).val :=
      inactiveStableMatrixHom_set_cast R
        (rightUnitPermutationStages_activeSet_eq.{u} n)
        (rightUnitDifferencePerfectFactor R n).val
    _ = _ := by
      have h := rightUnitPermutationStages.{u}.perfectFactor_reconstruct R n
      rw [rightUnitPermutationStages_matrix R (n + 1),
        rightUnitPermutationStages_matrix R n] at h
      exact h

end AlgebraicKTheory.StableGL

end
