/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine matrix, short and spin block spaces for actual Griess trace computations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTrace
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual physical symmetric matrices, as a genuine submodule of the full matrix space. -/
def monsterGeometrySymmetricMatrices : Submodule ℝ (Matrix (Fin 24) (Fin 24) ℝ) where
  carrier := {A | ∀ i j, A i j = A j i}
  zero_mem' := fun _ _ => rfl
  add_mem' ha hb := fun i j => by simp only [Matrix.add_apply, ha i j, hb i j]
  smul_mem' c A hA := fun i j => by simp only [Matrix.smul_apply, hA i j]

/-- The physical symmetric Conway space is exactly the product of its three genuine blocks. -/
def monsterGeometryTraceBlocksEquiv : conwaySymmetricSpace ≃ₗ[ℝ]
    (monsterGeometrySymmetricMatrices ×
      ((GriessShortIndex → ℝ) × (SpinIndex → Fin 24 → ℝ))) where
  toFun x := (⟨x.val.1, x.property⟩, x.val.2)
  invFun x := ⟨(x.1.val, x.2), x.1.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := by apply Prod.ext <;> rfl
  map_add' x y := by apply Prod.ext <;> rfl
  map_smul' c x := by apply Prod.ext <;> rfl

/-- The actual source dictionary identifies Griess operators with these physical trace blocks. -/
def monsterGeometryGriessTraceBlocks : GriessSpace ≃ₗ[ℝ]
    (monsterGeometrySymmetricMatrices ×
      ((GriessShortIndex → ℝ) × (SpinIndex → Fin 24 → ℝ))) :=
  griessConwayEquiv.trans monsterGeometryTraceBlocksEquiv

/-- The actual physical symmetric matrix block has real dimension 300. -/
theorem monsterGeometrySymmetricMatrices_finrank :
    Module.finrank ℝ monsterGeometrySymmetricMatrices = 300 := by
  have h := monsterGeometryGriessTraceBlocks.finrank_eq
  have hs : Module.finrank ℝ (GriessShortIndex → ℝ) = 98280 := by
    simp only [Module.finrank_pi, griessShortIndex_card]
  have ht : Module.finrank ℝ (SpinIndex → Fin 24 → ℝ) = 98304 := by
    have hn : Fintype.card SpinIndex = 4096 := by
      change Fintype.card (Fin 12 → ZMod 2) = 4096
      simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
      norm_num
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_pi, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, hn, nsmul_eq_mul]
    norm_num
  have hg : Module.finrank ℝ GriessSpace = 196884 := by simp [GriessSpace]
  rw [Module.finrank_prod, Module.finrank_prod, hs, ht, hg] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
