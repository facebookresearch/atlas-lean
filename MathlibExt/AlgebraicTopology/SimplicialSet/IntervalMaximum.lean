/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.MonoidalCompat

/-!
# Maximum on the simplicial interval

The map on `Δ[1] ⊗ Δ[1]` takes the maximum of the two monotone `Fin 2`
coordinates. Geometric zero is the endpoint `stdSimplex.δ 1`, and geometric
one is `stdSimplex.δ 0`. Zero is a two-sided unit, one is absorbing,
and the operation is commutative and associative.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory MonoidalCategory Simplicial Opposite
open scoped MonoidalCategory Simplicial

namespace SSet

universe u

private def intervalMaxOrderHom : Fin 2 × Fin 2 →o Fin 2 where
  toFun p := max p.1 p.2
  monotone' _ _ h := max_le_max h.1 h.2

/-- The actual simplicial interval maximum, applied to the original two simplex coordinates. -/
@[no_expose]
def intervalMaxMap : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] where
  app _ := ↾fun z ↦ stdSimplex.objEquiv.symm
    (SimplexCategory.Hom.mk
      (intervalMaxOrderHom.comp (prodStdSimplex.objEquiv z)))
  naturality _ _ f := by
    ext z
    apply stdSimplex.objEquiv.injective
    ext i
    rfl

/-- On every simplex coordinate, the interval operation is the literal maximum in `Fin 2`. -/
theorem intervalMaxMap_apply {n : ℕ} (x y : (Δ[1] : SSet.{u}) _⦋n⦌) (i : Fin (n + 1)) :
    (intervalMaxMap.app (op ⦋n⦌) (x, y) : (Δ[1] : SSet.{u}) _⦋n⦌) i = max (x i) (y i) := by
  with_unfolding_all
    rfl

private theorem endpointZero_apply {n : ℕ} (x : (Δ[0] : SSet.{u}) _⦋n⦌)
    (i : Fin (n + 1)) :
    ((stdSimplex.δ (1 : Fin 2)).app (op ⦋n⦌) x : (Δ[1] : SSet.{u}) _⦋n⦌) i = 0 := by
  rw [stdSimplex.δ_one_eq_const]
  rfl

private theorem endpointOne_apply {n : ℕ} (x : (Δ[0] : SSet.{u}) _⦋n⦌)
    (i : Fin (n + 1)) :
    ((stdSimplex.δ (0 : Fin 2)).app (op ⦋n⦌) x : (Δ[1] : SSet.{u}) _⦋n⦌) i = 1 := by
  rw [stdSimplex.δ_zero_eq_const]
  rfl

/-- Geometric zero, at endpoint index one, is the right unit for interval maximum. -/
theorem intervalMaxMap_zero_right :
    (Δ[1] : SSet.{u}) ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]) ≫ intervalMaxMap =
      (stdSimplex.rightUnitor (Δ[1] : SSet.{u})).hom := by
  ext ⟨⟨n⟩⟩ z i
  change (max (z.1 i) (((stdSimplex.δ (1 : Fin 2)).app (op ⦋n⦌) z.2) i)).val = (z.1 i).val
  rw [endpointZero_apply]
  exact congrArg Fin.val (max_eq_left (Fin.zero_le _))

/-- Geometric zero, at endpoint index one, is the left unit for interval maximum. -/
theorem intervalMaxMap_zero_left :
    (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ▷ Δ[1] ≫ intervalMaxMap =
      (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom := by
  ext ⟨⟨n⟩⟩ z i
  change (max (((stdSimplex.δ (1 : Fin 2)).app (op ⦋n⦌) z.1) i) (z.2 i)).val = (z.2 i).val
  rw [endpointZero_apply]
  exact congrArg Fin.val (max_eq_right (Fin.zero_le _))

/-- Geometric one, at endpoint index zero, absorbs on the right. -/
theorem intervalMaxMap_one_right :
    (Δ[1] : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]) ≫ intervalMaxMap =
      SSet.const (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) := by
  ext ⟨⟨n⟩⟩ z i
  change (max (z.1 i) (((stdSimplex.δ (0 : Fin 2)).app (op ⦋n⦌) z.2) i)).val = 1
  rw [endpointOne_apply]
  exact congrArg Fin.val (max_eq_right (Fin.le_last _))

/-- Geometric one, at endpoint index zero, absorbs on the left. -/
theorem intervalMaxMap_one_left :
    (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ▷ Δ[1] ≫ intervalMaxMap =
      SSet.const (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) := by
  ext ⟨⟨n⟩⟩ z i
  change (max (((stdSimplex.δ (0 : Fin 2)).app (op ⦋n⦌) z.1) i) (z.2 i)).val = 1
  rw [endpointOne_apply]
  exact congrArg Fin.val (max_eq_left (Fin.le_last _))

/-- Swapping the original two interval factors preserves their maximum. -/
theorem intervalMaxMap_comm :
    (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ intervalMaxMap = intervalMaxMap := by
  ext ⟨⟨n⟩⟩ z i
  change (max (z.2 i) (z.1 i)).val = (max (z.1 i) (z.2 i)).val
  exact congrArg Fin.val (max_comm _ _)

/-- Interval maximum is associative along the actual monoidal associator. -/
theorem intervalMaxMap_assoc :
    intervalMaxMap.{u} ▷ (Δ[1] : SSet.{u}) ≫ intervalMaxMap =
      (α_ (Δ[1] : SSet.{u}) Δ[1] Δ[1]).hom ≫
        (Δ[1] : SSet.{u}) ◁ intervalMaxMap ≫ intervalMaxMap := by
  ext ⟨⟨n⟩⟩ z i
  change (max (max (z.1.1 i) (z.1.2 i)) (z.2 i)).val =
    (max (z.1.1 i) (max (z.1.2 i) (z.2 i))).val
  exact congrArg Fin.val (max_assoc _ _ _)

end SSet
