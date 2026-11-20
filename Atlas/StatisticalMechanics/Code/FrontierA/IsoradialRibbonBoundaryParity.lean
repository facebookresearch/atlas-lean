/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib
import Code.FrontierA.IsoradialDualSubgraphSum












namespace StatMech.FrontierA

open Finset Equiv

variable {D E : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]


def permCycleCount (sigma : Equiv.Perm D) : Nat :=
  Multiset.card sigma.cycleType +
    (Fintype.card D - sigma.cycleType.sum)

theorem permCycleCount_add_cycleType_sum (sigma : Equiv.Perm D) :
    permCycleCount sigma + sigma.cycleType.sum =
      Fintype.card D + Multiset.card sigma.cycleType := by
  unfold permCycleCount
  have hle := sigma.sum_cycleType_le
  omega

theorem card_add_permCycleCount_mod_two (sigma : Equiv.Perm D) :
    (Fintype.card D + permCycleCount sigma) % 2 =
      (sigma.cycleType.sum + Multiset.card sigma.cycleType) % 2 := by
  have hle := sigma.sum_cycleType_le
  unfold permCycleCount
  omega

theorem perm_sign_val_eq_neg_one_pow_cycleCount (sigma : Equiv.Perm D) :
    ((Equiv.Perm.sign sigma : Units Int) : Int) =
      (-1 : Int) ^ (Fintype.card D + permCycleCount sigma) := by
  rw [sigma.sign_of_cycleType]
  change (-1 : Int) ^
      (sigma.cycleType.sum + Multiset.card sigma.cycleType) = _
  calc
    (-1 : Int) ^
        (sigma.cycleType.sum + Multiset.card sigma.cycleType) =
        (-1 : Int) ^
          ((sigma.cycleType.sum + Multiset.card sigma.cycleType) % 2) :=
      neg_one_pow_eq_pow_mod_two _
    _ = (-1 : Int) ^
          ((Fintype.card D + permCycleCount sigma) % 2) := by
      rw [card_add_permCycleCount_mod_two]
    _ = (-1 : Int) ^ (Fintype.card D + permCycleCount sigma) :=
      (neg_one_pow_eq_pow_mod_two _).symm

theorem permCycleCount_mod_two_toggle_of_sign_neg
    (sigma tau : Equiv.Perm D)
    (hsign : ((Equiv.Perm.sign tau : Units Int) : Int) =
      -((Equiv.Perm.sign sigma : Units Int) : Int)) :
    permCycleCount tau % 2 = (permCycleCount sigma + 1) % 2 := by
  have hpow :
      (-1 : Int) ^ (Fintype.card D + permCycleCount tau) =
        (-1 : Int) ^ (Fintype.card D + permCycleCount sigma + 1) := by
    rw [← perm_sign_val_eq_neg_one_pow_cycleCount,
      pow_succ, ← perm_sign_val_eq_neg_one_pow_cycleCount, hsign]
    ring
  have hpowMod :
      (-1 : Int) ^ ((Fintype.card D + permCycleCount tau) % 2) =
        (-1 : Int) ^
          ((Fintype.card D + permCycleCount sigma + 1) % 2) := by
    calc
      (-1 : Int) ^ ((Fintype.card D + permCycleCount tau) % 2) =
          (-1 : Int) ^ (Fintype.card D + permCycleCount tau) :=
        (neg_one_pow_eq_pow_mod_two _).symm
      _ = (-1 : Int) ^
          (Fintype.card D + permCycleCount sigma + 1) := hpow
      _ = (-1 : Int) ^
          ((Fintype.card D + permCycleCount sigma + 1) % 2) :=
        neg_one_pow_eq_pow_mod_two _
  have hleft : (Fintype.card D + permCycleCount tau) % 2 < 2 :=
    Nat.mod_lt _ (by decide)
  have hright :
      (Fintype.card D + permCycleCount sigma + 1) % 2 < 2 :=
    Nat.mod_lt _ (by decide)
  have hexponent :
      (Fintype.card D + permCycleCount tau) % 2 =
        (Fintype.card D + permCycleCount sigma + 1) % 2 := by
    interval_cases hL :
        (Fintype.card D + permCycleCount tau) % 2 <;>
      interval_cases hR :
        (Fintype.card D + permCycleCount sigma + 1) % 2 <;>
      first
      | rfl
      | norm_num [hL, hR] at hpowMod
  omega



structure RibbonPermutationSystem (E D : Type*)
    [Fintype D] [DecidableEq D] where
  rotation : Equiv.Perm D
  edgeFlip : E -> Equiv.Perm D
  edgeFlip_isSwap : forall e, (edgeFlip e).IsSwap
  edgeFlip_commute : forall e f, (e = f -> False) ->
    Commute (edgeFlip e) (edgeFlip f)

namespace RibbonPermutationSystem

variable (R : RibbonPermutationSystem E D)

omit [Fintype E] [DecidableEq E] in
private theorem edgeFlip_pairwise (F : Finset E) :
    (F : Set E).Pairwise fun e f => Commute (R.edgeFlip e) (R.edgeFlip f) := by
  intro e _ f _ hef
  exact R.edgeFlip_commute e f hef


noncomputable def partialEdgeFlip (F : Finset E) : Equiv.Perm D :=
  F.noncommProd R.edgeFlip (R.edgeFlip_pairwise F)


noncomputable def boundaryPerm (F : Finset E) : Equiv.Perm D :=
  R.rotation * R.partialEdgeFlip F


noncomputable def boundaryComponents (F : Finset E) : Nat :=
  permCycleCount (R.boundaryPerm F)

omit [Fintype E] in
theorem partialEdgeFlip_insert (F : Finset E) (e : E)
    (he : e ∈ F -> False) :
    R.partialEdgeFlip (insert e F) =
      R.edgeFlip e * R.partialEdgeFlip F := by
  unfold partialEdgeFlip
  exact Finset.noncommProd_insert_of_notMem F e R.edgeFlip
    (R.edgeFlip_pairwise (insert e F)) he

omit [Fintype E] in
theorem boundaryPerm_insert_sign (F : Finset E) (e : E)
    (he : e ∈ F -> False) :
    ((Equiv.Perm.sign (R.boundaryPerm (insert e F)) : Units Int) : Int) =
      -((Equiv.Perm.sign (R.boundaryPerm F) : Units Int) : Int) := by
  rw [boundaryPerm, partialEdgeFlip_insert R F e he, boundaryPerm]
  simp only [map_mul]
  rw [(R.edgeFlip_isSwap e).sign_eq]
  norm_num

omit [Fintype E] in


theorem boundaryComponents_insert_mod_two (F : Finset E) (e : E)
    (he : e ∈ F -> False) :
    R.boundaryComponents (insert e F) % 2 =
      (R.boundaryComponents F + 1) % 2 := by
  exact permCycleCount_mod_two_toggle_of_sign_neg _ _
    (R.boundaryPerm_insert_sign F e he)

omit [Fintype E] [DecidableEq E] in
@[simp] theorem boundaryPerm_empty :
    R.boundaryPerm (∅ : Finset E) = R.rotation := by
  unfold boundaryPerm partialEdgeFlip
  rw [Finset.noncommProd_empty, mul_one]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem boundaryComponents_empty :
    R.boundaryComponents (∅ : Finset E) =
      permCycleCount R.rotation := by
  simp [boundaryComponents]


theorem boundaryParity_eq_dualVertexCount
    (dualVertexCount : Nat)
    (hEuler : (Fintype.card E + permCycleCount R.rotation) % 2 =
      dualVertexCount % 2) :
    forall F : Finset E,
      (Fᶜ.card + R.boundaryComponents F) % 2 =
        dualVertexCount % 2 := by
  apply compl_card_add_boundary_mod_two_eq_dualVertexCount
    R.boundaryComponents dualVertexCount
  · exact R.boundaryComponents_insert_mod_two
  · simpa using hEuler

end RibbonPermutationSystem

end StatMech.FrontierA
