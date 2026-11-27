/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.MonoidalCompat

/-!
# Maximum on the simplicial interval

In every universe u, the standard simplicial interval A=Δ[1] has a commutative associative
operation m:A⊗A→A given by pointwise maximum. An n-simplex of A is a monotone function
Fin(n+1)→Fin 2, and m acts coordinatewise.

The geometric vertex 0, represented by δ₁:Δ[0]→A, is a unit on either side; vertex 1,
represented by δ₀, is absorbing. The unit equations use the standard-simplex unitors, and
associativity uses the tensor associator.
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

/-- For A=Δ[1] in simplicial-set universe u, define m:A⊗A→A by m_n(x,y)(i)=max(x(i),y(i)) for every
n∈ℕ and i∈Fin(n+1). The two inputs are monotone maps Fin(n+1)→Fin 2, and their pointwise maximum
is again monotone. -/
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

/-- Let A=Δ[1] in universe u. For n∈ℕ, n-simplices x,y of A and i∈Fin(n+1), the i-th coordinate of
the n-simplex m_n(x,y) is max(x(i),y(i)). -/
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

/-- For A=Δ[1] in universe u and m the pointwise maximum, (id_A⊗δ₁)≫m=ρ_A.hom:A⊗Δ[0]→A. The map δ₁
selects geometric vertex 0, and ρ_A is the standard-simplex right unitor. -/
theorem intervalMaxMap_zero_right :
    (Δ[1] : SSet.{u}) ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]) ≫ intervalMaxMap =
      (stdSimplex.rightUnitor (Δ[1] : SSet.{u})).hom := by
  ext ⟨⟨n⟩⟩ z i
  change (max (z.1 i) (((stdSimplex.δ (1 : Fin 2)).app (op ⦋n⦌) z.2) i)).val = (z.1 i).val
  rw [endpointZero_apply]
  exact congrArg Fin.val (max_eq_left (Fin.zero_le _))

/-- For A=Δ[1] in universe u and m the pointwise maximum, (δ₁⊗id_A)≫m=λ_A.hom:Δ[0]⊗A→A. The map δ₁
selects geometric vertex 0, and λ_A is the standard-simplex left unitor. -/
theorem intervalMaxMap_zero_left :
    (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ▷ Δ[1] ≫ intervalMaxMap =
      (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom := by
  ext ⟨⟨n⟩⟩ z i
  change (max (((stdSimplex.δ (1 : Fin 2)).app (op ⦋n⦌) z.1) i) (z.2 i)).val = (z.2 i).val
  rw [endpointZero_apply]
  exact congrArg Fin.val (max_eq_right (Fin.zero_le _))

/-- For A=Δ[1] in universe u and m the pointwise maximum, (id_A⊗δ₀)≫m:A⊗Δ[0]→A is the constant map
at vertex 1. Here δ₀ selects geometric vertex 1. -/
theorem intervalMaxMap_one_right :
    (Δ[1] : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]) ≫ intervalMaxMap =
      SSet.const (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) := by
  ext ⟨⟨n⟩⟩ z i
  change (max (z.1 i) (((stdSimplex.δ (0 : Fin 2)).app (op ⦋n⦌) z.2) i)).val = 1
  rw [endpointOne_apply]
  exact congrArg Fin.val (max_eq_right (Fin.le_last _))

/-- For A=Δ[1] in universe u and m the pointwise maximum, (δ₀⊗id_A)≫m:Δ[0]⊗A→A is the constant map
at vertex 1. Here δ₀ selects geometric vertex 1. -/
theorem intervalMaxMap_one_left :
    (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ▷ Δ[1] ≫ intervalMaxMap =
      SSet.const (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) := by
  ext ⟨⟨n⟩⟩ z i
  change (max (((stdSimplex.δ (0 : Fin 2)).app (op ⦋n⦌) z.1) i) (z.2 i)).val = 1
  rw [endpointOne_apply]
  exact congrArg Fin.val (max_eq_left (Fin.le_last _))

/-- For A=Δ[1] in universe u and m:A⊗A→A the pointwise maximum, β_{A,A}.hom≫m=m. The tensor symmetry
β swaps the two interval coordinates. -/
theorem intervalMaxMap_comm :
    (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ intervalMaxMap = intervalMaxMap := by
  ext ⟨⟨n⟩⟩ z i
  change (max (z.2 i) (z.1 i)).val = (max (z.1 i) (z.2 i)).val
  exact congrArg Fin.val (max_comm _ _)

/-- For A=Δ[1] in universe u and m the pointwise maximum, (m⊗id_A)≫m=α_{A,A,A}.hom≫(id_A⊗m)≫m as
maps (A⊗A)⊗A→A. The associator α goes from (A⊗A)⊗A to A⊗(A⊗A). -/
theorem intervalMaxMap_assoc :
    intervalMaxMap.{u} ▷ (Δ[1] : SSet.{u}) ≫ intervalMaxMap =
      (α_ (Δ[1] : SSet.{u}) Δ[1] Δ[1]).hom ≫
        (Δ[1] : SSet.{u}) ◁ intervalMaxMap ≫ intervalMaxMap := by
  ext ⟨⟨n⟩⟩ z i
  change (max (max (z.1.1 i) (z.1.2 i)) (z.2 i)).val =
    (max (z.1.1 i) (max (z.1.2 i) (z.2 i))).val
  exact congrArg Fin.val (max_assoc _ _ _)

end SSet
