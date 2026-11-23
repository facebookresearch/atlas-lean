/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.ElementaryConjugation
public import MathlibExt.KTheory.Ring.StableGeneralLinear.InactivePermutationFactor
public import MathlibExt.KTheory.Ring.StableGeneralLinear.StabilizeTo

/-!
# Actual inactive differences of prefix-compatible permutation matrices

An actual sequence of even finite permutations with a fixed coordinate
formula on the original active prefix has an explicitly computed even
consecutive difference fixing that ENTIRE prefix. The existing alternating
image construction puts that same difference in a genuine perfect inactive
group and computes its original ambient stable matrix. This is finite
permutation data, not a homotopy or inactive-factor witness.
-/

noncomputable section

open Matrix

namespace AlgebraicKTheory.StableGL

/-- Finite permutation data with one ORIGINAL active-coordinate formula.
Every coordinate and sign certificate concerns these actual permutations. -/
public structure PrefixPermutationStages where
  /-- The original active matrix rank at each stage. -/
  activeRank : ℕ → ℕ
  /-- Original active ranks include the previous original prefix. -/
  activeRank_mono : ∀ n, activeRank n ≤ activeRank (n + 1)
  /-- The actual finite matrix rank at each stage. -/
  rank : ℕ → ℕ
  /-- The actual finite permutation at each stage. -/
  permutation : (n : ℕ) → Equiv.Perm (Fin (rank n))
  /-- The original stage fits in that matrix rank. -/
  rank_bound : ∀ n, activeRank n ≤ rank n
  /-- One numerical formula for all original active coordinates. -/
  coordinate : ℕ → ℕ
  /-- The SAME numerical formula holds on the whole original active prefix. -/
  active : ∀ n (i : Fin (rank n)), i.val < activeRank n →
    (permutation n i).val = coordinate i.val
  /-- Each actual permutation is even. -/
  sign : ∀ n, Equiv.Perm.sign (permutation n) = 1

namespace PrefixPermutationStages

variable (S : PrefixPermutationStages)

/-- A concrete common matrix rank for two consecutive original stages. -/
public abbrev commonRank (n : ℕ) : ℕ := S.rank n + S.rank (n + 1)

/-- The original active stage fits in the actual common matrix rank. -/
public theorem commonRank_bound (n : ℕ) : S.activeRank n ≤ S.commonRank n :=
  (S.rank_bound n).trans (Nat.le_add_right (S.rank n) (S.rank (n + 1)))

/-- The previous original permutation with trailing identities only. -/
public abbrev oldPermutation (n : ℕ) : Equiv.Perm (Fin (S.commonRank n)) :=
  finitePermutationStabilization (S.rank (n + 1)) (S.permutation n)

/-- The next original permutation, reindexed only along the rank-sum equality. -/
public abbrev newPermutation (n : ℕ) : Equiv.Perm (Fin (S.commonRank n)) :=
  (finCongr (Nat.add_comm (S.rank (n + 1)) (S.rank n))).permCongr
    (finitePermutationStabilization (S.rank n) (S.permutation (n + 1)))

private theorem old_active_val (n : ℕ) (x : Fin (S.commonRank n)) (hx : x.val < S.activeRank n) :
    (S.oldPermutation n x).val = S.coordinate x.val := by
  let i : Fin (S.rank n) := ⟨x.val, hx.trans_le (S.rank_bound n)⟩
  have hi : Fin.castAdd (S.rank (n + 1)) i = x := Fin.ext rfl
  have h := finitePermutationStabilization_castAdd
    (S.rank (n + 1)) (S.permutation n) i
  exact (congrArg (fun z : Fin (S.commonRank n) => (S.oldPermutation n z).val) hi).symm.trans
    ((congrArg Fin.val h).trans (S.active n i hx))

private theorem new_active_val (n : ℕ) (x : Fin (S.commonRank n)) (hx : x.val < S.activeRank n) :
    (S.newPermutation n x).val = S.coordinate x.val := by
  let i : Fin (S.rank (n + 1)) :=
    ⟨x.val, (hx.trans_le (S.activeRank_mono n)).trans_le (S.rank_bound (n + 1))⟩
  let e := finCongr (Nat.add_comm (S.rank (n + 1)) (S.rank n))
  have hi : e (Fin.castAdd (S.rank n) i) = x := Fin.ext rfl
  have h : S.newPermutation n (e (Fin.castAdd (S.rank n) i)) =
      e (Fin.castAdd (S.rank n) (S.permutation (n + 1) i)) := by
    change e.permCongr (finitePermutationStabilization (S.rank n)
      (S.permutation (n + 1))) (e (Fin.castAdd (S.rank n) i)) = _
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact congrArg e (finitePermutationStabilization_castAdd _ _ i)
  exact (congrArg (fun z : Fin (S.commonRank n) => (S.newPermutation n z).val) hi).symm.trans
    ((congrArg Fin.val h).trans (S.active (n + 1) i (hx.trans_le (S.activeRank_mono n))))

/-- The actual consecutive difference at the concrete common matrix rank. -/
public abbrev difference (n : ℕ) : Equiv.Perm (Fin (S.commonRank n)) :=
  (S.newPermutation n)⁻¹ * S.oldPermutation n

/-- That actual difference fixes EVERY original active coordinate. -/
public theorem difference_fixed (n : ℕ) (x : Fin (S.commonRank n))
    (hx : x.val < S.activeRank n) :
    S.difference n x = x := by
  have h : S.oldPermutation n x = S.newPermutation n x :=
    Fin.ext ((old_active_val S n x hx).trans (new_active_val S n x hx).symm)
  change (S.newPermutation n).symm (S.oldPermutation n x) = x
  rw [h, Equiv.symm_apply_apply]

/-- The original consecutive difference is even at its actual common rank. -/
public theorem difference_sign (n : ℕ) : Equiv.Perm.sign (S.difference n) = 1 := by
  have ho : Equiv.Perm.sign (S.oldPermutation n) = 1 :=
    (finitePermutationStabilization_sign _ _).trans (S.sign n)
  have hn : Equiv.Perm.sign (S.newPermutation n) = 1 := by
    rw [Equiv.Perm.sign_permCongr, finitePermutationStabilization_sign, S.sign]
  change Equiv.Perm.sign ((S.newPermutation n)⁻¹ * S.oldPermutation n) = 1
  rw [map_mul, map_inv, hn, ho, inv_one, mul_one]

/-- The actual active subset in the actual common matrix rank. -/
public abbrev activeSet (n : ℕ) : Set (Fin (S.commonRank n)) := {x | x.val < S.activeRank n}

universe u

variable (R : Type u) [Ring R]

private theorem old_matrix (n : ℕ) :
    StableGL.of (GeneralLinearGroup.permutationUnitsHom R _ (S.oldPermutation n)) =
      StableGL.of (GeneralLinearGroup.permutationUnitsHom R _ (S.permutation n)) := by
  rw [finitePermutationStabilization_matrix, StableGL.of_blockStabilization]

private theorem new_matrix (n : ℕ) :
    StableGL.of (GeneralLinearGroup.permutationUnitsHom R _ (S.newPermutation n)) =
      StableGL.of (GeneralLinearGroup.permutationUnitsHom R _ (S.permutation (n + 1))) := by
  rw [← GeneralLinearGroup.permutationUnitsHom_reindex, StableGL.of_reindex_finCongr,
    finitePermutationStabilization_matrix, StableGL.of_blockStabilization]

/-- The original stable matrix of the computed permutation difference. -/
public theorem difference_matrix (n : ℕ) :
    StableGL.of (GeneralLinearGroup.permutationUnitsHom R _ (S.difference n)) =
      (StableGL.of (GeneralLinearGroup.permutationUnitsHom R _ (S.permutation (n + 1))))⁻¹ *
        StableGL.of (GeneralLinearGroup.permutationUnitsHom R _ (S.permutation n)) := by
  change StableGL.of (GeneralLinearGroup.permutationUnitsHom R _
    ((S.newPermutation n)⁻¹ * S.oldPermutation n)) = _
  rw [map_mul, map_inv, StableGL.of_mul, StableGL.of_inv, old_matrix, new_matrix]

/-- The genuine perfect inactive image group at the original common rank. -/
public abbrev perfectGroup (n : ℕ) : Type u :=
  InactivePerfectMatrixGroup R (S.commonRank n) (S.activeSet n)

/-- Perfectness of this actual image is derived by the existing alternating image. -/
public theorem perfectGroup_isPerfect (n : ℕ) : Group.IsPerfect (S.perfectGroup R n) :=
  inactivePerfectMatrixGroup_isPerfect R _ _

/-- The SAME consecutive difference as an element of its actual perfect image. -/
public def perfectFactor (n : ℕ) : S.perfectGroup R n :=
  inactivePermutationMatrixFactor R _ _ (S.difference n)
    (fun x hx => S.difference_fixed n x hx) (S.difference_sign n)

/-- Its ORIGINAL ambient image is exactly the original consecutive matrix difference. -/
public theorem perfectFactor_reconstruct (n : ℕ) :
    inactiveStableMatrixHom R (S.commonRank n) (S.activeSet n) (S.perfectFactor R n).val =
      (StableGL.of (GeneralLinearGroup.permutationUnitsHom R _ (S.permutation (n + 1))))⁻¹ *
        StableGL.of (GeneralLinearGroup.permutationUnitsHom R _ (S.permutation n)) :=
  (inactivePermutationMatrixFactor_reconstruct R (S.commonRank n) (S.activeSet n)
    (S.difference n) (fun x hx => S.difference_fixed n x hx) (S.difference_sign n)).trans
      (S.difference_matrix R n)

end PrefixPermutationStages

end AlgebraicKTheory.StableGL

end
