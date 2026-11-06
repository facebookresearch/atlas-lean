/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual split binary twenty-four-dimensional quadratic form has 8,390,656 zeroes. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryBinaryDot

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Exact zero-fiber size for each literal twelve-bit dot functional. -/
theorem monsterGeometryBinaryDot_zero_fiber_card (a : Fin 12 → ZMod 2) :
    Nat.card {b : Fin 12 → ZMod 2 // monsterGeometryBinaryDot a b = 0} =
      if a = 0 then 4096 else 2048 := by
  classical
  by_cases ha : a = 0
  · rw [ha, ite_eq_left rfl]
    let e : {b : Fin 12 → ZMod 2 // monsterGeometryBinaryDot 0 b = 0} ≃
        (Fin 12 → ZMod 2) :=
      { toFun := Subtype.val
        invFun := fun b => ⟨b, by simp [monsterGeometryBinaryDot]⟩
        left_inv := fun b => Subtype.ext rfl
        right_inv := fun b => rfl }
    rw [Nat.card_congr e]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_fin, ZMod.card]
    norm_num
  · rw [ite_eq_right ha]
    exact monsterGeometryBinaryDot_twelve_ker_card a ha

/-- Ordered hyperbolic zero pairs are exactly the dependent zero fibers of their first half. -/
def monsterGeometryHyperbolicZeroFiberEquiv :
    {p : (Fin 12 → ZMod 2) × (Fin 12 → ZMod 2) // hyperbolicFun p = 0} ≃
      Σ a : Fin 12 → ZMod 2, {b : Fin 12 → ZMod 2 // monsterGeometryBinaryDot a b = 0} where
  toFun p := ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
  invFun p := ⟨(p.1, p.2.val), p.2.property⟩
  left_inv p := by rcases p with ⟨⟨a, b⟩, h⟩; rfl
  right_inv p := by rcases p with ⟨a, ⟨b, h⟩⟩; rfl

/-- The actual hyperbolic form has exactly 4096 + 4095 times 2048 zeroes. -/
theorem monsterGeometryHyperbolic_zero_card :
    Nat.card {p : (Fin 12 → ZMod 2) × (Fin 12 → ZMod 2) // hyperbolicFun p = 0} =
      8390656 := by
  classical
  rw [Nat.card_congr monsterGeometryHyperbolicZeroFiberEquiv, Nat.card_sigma]
  simp_rw [monsterGeometryBinaryDot_zero_fiber_card]
  have hterm : ∀ a : Fin 12 → ZMod 2,
      (if a = 0 then 4096 else 2048 : ℕ) = 2048 + if a = 0 then 2048 else 0 := by
    intro a
    by_cases h : a = 0 <;> simp only [h, ite_true, ite_false]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, ZMod.card, smul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  norm_num

/-- The actual extraspecial square form has precisely the same zeroes under its checked split. -/
theorem monsterGeometrySquareQuad_singular_card :
    Nat.card {v : Fin 24 → ZMod 2 // squareQuad v = 0} = 8390656 := by
  let e : {v : Fin 24 → ZMod 2 // squareQuad v = 0} ≃
      {p : (Fin 12 → ZMod 2) × (Fin 12 → ZMod 2) // hyperbolicFun p = 0} :=
    { toFun := fun v => ⟨qHyperbolicEquiv v.val, v.property⟩
      invFun := fun p => ⟨qHyperbolicEquiv.symm p.val, by
        rw [qHyperbolicEquiv_form, qHyperbolicEquiv.apply_symm_apply]
        exact p.property⟩
      left_inv := fun v => Subtype.ext (qHyperbolicEquiv.symm_apply_apply v.val)
      right_inv := fun p => Subtype.ext (qHyperbolicEquiv.apply_symm_apply p.val) }
  rw [Nat.card_congr e]
  exact monsterGeometryHyperbolic_zero_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
