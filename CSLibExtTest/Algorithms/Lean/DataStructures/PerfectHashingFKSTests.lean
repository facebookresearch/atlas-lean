/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing.FKS

/-! A two-key universal family with a colliding and a noncolliding member: the FKS primary
bound holds for the noncolliding member only, so the theorem's witness is forced. -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UniversalHashing

/-- Two hashes of the keys `Fin 2` into `Fintype.card (Fin 2) = 2` buckets: index `0` sends
both keys to bucket `0`, index `1` is the identity. -/
private def twoHashes (i : Fin 2) (x : Fin 2) : Fin (Fintype.card (Fin 2)) :=
  Fin.cast (Fintype.card_fin 2).symm (if i = 0 then 0 else x)

/-- The family is universal: the two keys collide under one of the two indices, and
`1 * 2 ≤ 2`. -/
private theorem twoHashes_universal : IsUniversalOn Finset.univ twoHashes := by
  unfold IsUniversalOn
  decide

/-- Index `0` has two ordered collisions, which is not below `|K| = 2`; the identity has
none. -/
private theorem twoHashes_collisions :
    ∑ b, (Finset.univ.filter fun x => twoHashes 0 x = b).card *
        ((Finset.univ.filter fun x => twoHashes 0 x = b).card - 1) = 2 ∧
    ∑ b, (Finset.univ.filter fun x => twoHashes 1 x = b).card *
        ((Finset.univ.filter fun x => twoHashes 1 x = b).card - 1) = 0 := by
  decide

/-- Only the identity meets the collision bound. -/
private theorem twoHashes_bound_forces_identity (i : Fin 2) :
    ∑ b, (Finset.univ.filter fun x => twoHashes i x = b).card *
        ((Finset.univ.filter fun x => twoHashes i x = b).card - 1) < Fintype.card (Fin 2) →
      i = 1 := by
  revert i
  decide

/-- The theorem applies to the family, and its witness is the noncolliding identity, whose
squared bucket sizes `1 + 1` are below `2 * 2`. -/
example : ∃ i ∈ (Finset.univ : Finset (Fin 2)), i = 1 ∧
    ∑ b, (Finset.univ.filter fun x => twoHashes i x = b).card ^ 2 <
      2 * Fintype.card (Fin 2) := by
  obtain ⟨i, hi, hcoll, hsq⟩ := fks_exists_good_hash twoHashes_universal
  exact ⟨i, hi, twoHashes_bound_forces_identity i hcoll, hsq⟩

end Cslib.Algorithms.Lean.UniversalHashing
