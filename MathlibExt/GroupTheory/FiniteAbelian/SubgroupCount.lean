/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Counting subgroups of finite abelian groups

Character duality gives a bijection from subgroups of index `k` to subgroups of order `k`.
-/

namespace MetaMathlibExt

/-- **Counting subgroups by order and by index.** In a finite abelian group $G$, for every
natural number $k$ the number of subgroups of order $k$ equals the number of subgroups of
index $k$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 3 (`integers-2026-A97-lem-3`). -/
public theorem ncard_addSubgroup_card_eq_ncard_index_eq (G : Type*) [AddCommGroup G]
    [Finite G] (k : ℕ) :
    {H : AddSubgroup G | Nat.card H = k}.ncard = {H : AddSubgroup G | H.index = k}.ncard := by
  let A := Multiplicative G
  let K := AlgebraicClosure ℚ
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity A K
  let annihilator := CommGroup.subgroupOrderIsoSubgroupMonoidHom A K
  let toMul := (AddSubgroup.toSubgroup (A := G)).toEquiv
  -- Identify the character group with the original group to count both families inside `G`.
  let correspondence := toMul.trans <| annihilator.toEquiv.trans <| OrderDual.ofDual.trans <|
    e.mapSubgroup.toEquiv.trans toMul.symm
  apply Eq.symm
  refine Set.ncard_congr' (correspondence.subtypeEquiv fun H ↦ ?_)
  change H.index = k ↔ Nat.card (e.mapSubgroup (annihilator H.toSubgroup).ofDual) = k
  rw [Subgroup.card_mapSubgroup, CommGroup.card_subgroupOrderIsoSubgroupMonoidHom]
  rfl

end MetaMathlibExt
