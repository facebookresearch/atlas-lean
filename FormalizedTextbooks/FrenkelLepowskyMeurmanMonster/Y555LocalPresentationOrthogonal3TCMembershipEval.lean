/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact 31-point finite membership fingerprints of actual transported source root sets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCMembershipData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3RootMembership

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise

/-- A finite integer fingerprint of actual root-set membership on the 31 declared source vectors. -/
def y322Orthogonal3TCMembershipFingerprint
    (roots : Finset (Matrix (Fin 7) Unit (ZMod 3))) : ℕ :=
  ∑ i : Fin 31, if y322Orthogonal3VectorColumn (y322Orthogonal3TCMembershipPoint i) ∈ roots
    then 2 ^ i.val else 0

/-- Compute the exact inverse root-set membership fingerprint from a forward finite matrix. -/
def y322Orthogonal3TCMembershipEval (matrix : Matrix (Fin 7) (Fin 7) (ZMod 3)) : ℕ :=
  ∑ i : Fin 31, if y322Orthogonal3RootMembershipNat matrix (y322Orthogonal3TCMembershipPoint i)
    then 2 ^ i.val else 0

/-- The bounded matrix evaluator is the fingerprint of the actual inverse transported root set. -/
theorem y322Orthogonal3TCMembershipEval_exact
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :
    y322Orthogonal3TCMembershipEval g.val =
      y322Orthogonal3TCMembershipFingerprint (g⁻¹ • y322Orthogonal3E7Roots) := by
  unfold y322Orthogonal3TCMembershipEval y322Orthogonal3TCMembershipFingerprint
  apply Finset.sum_congr rfl
  intro i _
  simp only [y322Orthogonal3RootMembershipNat_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
