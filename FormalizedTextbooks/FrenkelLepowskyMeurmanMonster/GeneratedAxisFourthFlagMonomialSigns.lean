/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayCoordinateProjection

/-! Counting genuine Golay sign matrices with equal signs on a selected pair. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The relative sign at two physical coordinates, evaluated on actual codewords. -/
def generatedFourthFlagPairSignPhase (i j : Fin 24) :
    Multiplicative golayCode →* Multiplicative (ZMod 2) where
  toFun c := ofAdd (c.toAdd.val i + c.toAdd.val j)
  map_one' := by rfl
  map_mul' c d := by
    apply toAdd.injective
    change (c.toAdd.val i + d.toAdd.val i) + (c.toAdd.val j + d.toAdd.val j) =
      (c.toAdd.val i + c.toAdd.val j) + (d.toAdd.val i + d.toAdd.val j)
    abel

/-- Every relative sign occurs because any prescription on two coordinates extends. -/
theorem generatedFourthFlagPairSignPhase_surjective (i j : Fin 24) (hij : i ≠ j) :
    Function.Surjective (generatedFourthFlagPairSignPhase i j) := by
  let f : Fin 2 → Fin 24 := ![i, j]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hij]
  intro a
  obtain ⟨c, hc⟩ := golayCoordinateProjection_surjective (by decide) f hf
    (![0, a.toAdd] : Fin 2 → ZMod 2)
  refine ⟨ofAdd c, ?_⟩
  apply toAdd.injective
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  change c.val i = 0 at h0
  change c.val j = a.toAdd at h1
  change c.val i + c.val j = a.toAdd
  rw [h0, h1, zero_add]

/-- Exactly 2048 genuine codewords have equal signs at two distinct coordinates. -/
theorem generatedFourthFlagPairSignPhase_kernel_card (i j : Fin 24) (hij : i ≠ j) :
    Nat.card (generatedFourthFlagPairSignPhase i j).ker = 2048 := by
  have h := (generatedFourthFlagPairSignPhase i j).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
    (generatedFourthFlagPairSignPhase_surjective i j hij), Subgroup.card_top] at h
  have hd : Nat.card (Multiplicative golayCode) = 4096 := golayCode_card
  have ht : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp [ZMod.card]
  rw [hd, ht] at h
  omega

/-- The subgroup of actual Leech sign matrices with matching signs at eight and eleven. -/
def generatedFourthFlagEqualSignSubgroup : Subgroup leechIsomSubgroup :=
  ((generatedFourthFlagPairSignPhase 8 11).ker).map golaySignHom

/-- Passing to physical sign matrices loses no actual codewords. -/
theorem generatedFourthFlagEqualSignSubgroup_card :
    Nat.card generatedFourthFlagEqualSignSubgroup = 2048 := by
  rw [generatedFourthFlagEqualSignSubgroup,
    Subgroup.card_map_of_injective golaySignHom_injective]
  exact generatedFourthFlagPairSignPhase_kernel_card 8 11 (by decide)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
