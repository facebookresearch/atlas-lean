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

public import MathlibExt.AlgebraicTopology.SimplicialSet.IntervalMaximum
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexParameterMinimum

/-!
# Minimum on the simplicial interval

In every universe u, the standard simplicial interval A=Δ[1] has a commutative associative
operation a:A⊗A→A given by pointwise minimum of monotone Fin(n+1)→Fin 2 coordinates. Geometric
vertex 0 is absorbing and vertex 1 is a unit; these vertices are δ₁ and δ₀, respectively.

The minimum is the second projection of the canonical parameter-minimum comparison for the two
identity maps of [1]. Synchronized minimum distributes over interval maximum:
min(max(x,y),t)=max(min(x,t),min(y,t)).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory MonoidalCategory Simplicial Opposite CartesianMonoidalCategory
open scoped MonoidalCategory Simplicial

namespace SSet


universe u

/-- For A=Δ[1] in simplicial-set universe u, define a:A⊗A→A by a_n(x,y)(i)=min(x(i),y(i)) for n∈ℕ
and i∈Fin(n+1). The inputs and output are monotone Fin(n+1)→Fin 2 maps. -/
def intervalMinMap : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] :=
  SimplexParameterComparison.minimumMap (𝟙 ⦋1⦌) (𝟙 ⦋1⦌) ≫
    CartesianMonoidalCategory.snd _ _

/-- For A=Δ[1] in universe u, the pointwise minimum equals μ(id_[1],id_[1])≫pr₂, where μ is the
canonical parameter-minimum comparison and pr₂ its second projection. On an n-simplex (x,y),
this composite has i-th coordinate min(x(i),y(i)). -/
theorem intervalMinMap_eq_parameterMinimum :
    intervalMinMap.{u} =
      SimplexParameterComparison.minimumMap (𝟙 ⦋1⦌) (𝟙 ⦋1⦌) ≫
        CartesianMonoidalCategory.snd _ _ := rfl

/-- For A=Δ[1] in universe u, n∈ℕ, n-simplices x,y of A and i∈Fin(n+1), a_n(x,y)(i)=min(x(i),y(i)),
where a:A⊗A→A is interval minimum. -/
theorem intervalMinMap_apply {n : ℕ} (x y : (Δ[1] : SSet.{u}) _⦋n⦌)
    (i : Fin (n + 1)) :
    (intervalMinMap.app (op ⦋n⦌) (x, y) : (Δ[1] : SSet.{u}) _⦋n⦌) i =
      min (x i) (y i) := by
  with_unfolding_all rfl

/-- Let A=Δ[1] in universe u, let c be an object of the opposite simplex category, and let z be a
c-simplex of A⊗A. Under the ordinal presentations z(i)=(z₁(i),z₂(i)) for i∈Fin(c.unop.len+1),
the image under interval minimum is the monotone map i↦min(z₁(i),z₂(i)). -/
theorem intervalMinMap_objEquiv_toFun_apply (a : SimplexCategoryᵒᵖ)
    (z : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).obj a)
    (i : Fin (a.unop.len + 1)) :
    (stdSimplex.objEquiv
        ((ConcreteCategory.hom (NatTrans.app intervalMinMap a)).toFun z)).toOrderHom i =
      min ((prodStdSimplex.objEquiv z i).1) ((prodStdSimplex.objEquiv z i).2) := by
  with_unfolding_all rfl

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

/-- For A=Δ[1] in universe u and a the pointwise minimum, (id_A⊗δ₁)≫a:A⊗Δ[0]→A is the constant map
at vertex 0. Here δ₁ selects geometric vertex 0. -/
theorem intervalMinMap_zero_right :
    (Δ[1] : SSet.{u}) ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]) ≫ intervalMinMap =
      SSet.const (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) := by
  ext ⟨⟨n⟩⟩ z i
  change (min (z.1 i) (((stdSimplex.δ (1 : Fin 2)).app (op ⦋n⦌) z.2) i)).val = 0
  rw [endpointZero_apply]
  exact congrArg Fin.val (min_eq_right (Fin.zero_le _))

/-- For A=Δ[1] in universe u and a the pointwise minimum, (δ₁⊗id_A)≫a:Δ[0]⊗A→A is the constant map
at vertex 0. Here δ₁ selects geometric vertex 0. -/
theorem intervalMinMap_zero_left :
    (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ▷ Δ[1] ≫ intervalMinMap =
      SSet.const (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) := by
  ext ⟨⟨n⟩⟩ z i
  change (min (((stdSimplex.δ (1 : Fin 2)).app (op ⦋n⦌) z.1) i) (z.2 i)).val = 0
  rw [endpointZero_apply]
  exact congrArg Fin.val (min_eq_left (Fin.zero_le _))

/-- For A=Δ[1] in universe u and a the pointwise minimum, (id_A⊗δ₀)≫a=ρ_A.hom:A⊗Δ[0]→A. The map δ₀
selects geometric vertex 1, and ρ_A is the standard-simplex right unitor. -/
theorem intervalMinMap_one_right :
    (Δ[1] : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]) ≫ intervalMinMap =
      (stdSimplex.rightUnitor (Δ[1] : SSet.{u})).hom := by
  ext ⟨⟨n⟩⟩ z i
  change (min (z.1 i) (((stdSimplex.δ (0 : Fin 2)).app (op ⦋n⦌) z.2) i)).val = (z.1 i).val
  rw [endpointOne_apply]
  exact congrArg Fin.val (min_eq_left (Fin.le_last _))

/-- For A=Δ[1] in universe u and a the pointwise minimum, (δ₀⊗id_A)≫a=λ_A.hom:Δ[0]⊗A→A. The map δ₀
selects geometric vertex 1, and λ_A is the standard-simplex left unitor. -/
theorem intervalMinMap_one_left :
    (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ▷ Δ[1] ≫ intervalMinMap =
      (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom := by
  ext ⟨⟨n⟩⟩ z i
  change (min (((stdSimplex.δ (0 : Fin 2)).app (op ⦋n⦌) z.1) i) (z.2 i)).val = (z.2 i).val
  rw [endpointOne_apply]
  exact congrArg Fin.val (min_eq_right (Fin.le_last _))

/-- For A=Δ[1] in universe u and a:A⊗A→A the pointwise minimum, β_{A,A}.hom≫a=a, where β swaps the
two interval coordinates. -/
theorem intervalMinMap_comm :
    (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ intervalMinMap = intervalMinMap := by
  ext ⟨⟨n⟩⟩ z i
  change (min (z.2 i) (z.1 i)).val = (min (z.1 i) (z.2 i)).val
  exact congrArg Fin.val (min_comm _ _)

/-- For A=Δ[1] in universe u and a the pointwise minimum, (a⊗id_A)≫a=α_{A,A,A}.hom≫(id_A⊗a)≫a as
maps (A⊗A)⊗A→A. The associator α goes from (A⊗A)⊗A to A⊗(A⊗A). -/
theorem intervalMinMap_assoc :
    intervalMinMap.{u} ▷ (Δ[1] : SSet.{u}) ≫ intervalMinMap =
      (α_ (Δ[1] : SSet.{u}) Δ[1] Δ[1]).hom ≫
        (Δ[1] : SSet.{u}) ◁ intervalMinMap ≫ intervalMinMap := by
  ext ⟨⟨n⟩⟩ z i
  change (min (min (z.1.1 i) (z.1.2 i)) (z.2 i)).val =
    (min (z.1.1 i) (min (z.1.2 i) (z.2 i))).val
  exact congrArg Fin.val (min_assoc _ _ _)

/-- For the pointwise minimum a and maximum m on A=Δ[1] in universe u, the two maps (A⊗A)⊗A→A have
coordinate values min(max(x,y),t)=max(min(x,t),min(y,t)). On the right, the last interval
coordinate t is paired with both x and y before applying minimum and then maximum. -/
theorem intervalMinMap_max_distrib :
    intervalMaxMap.{u} ▷ (Δ[1] : SSet.{u}) ≫ intervalMinMap =
      lift
        (lift (fst _ _ ≫ fst _ _) (snd _ _) ≫ intervalMinMap)
        (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ intervalMinMap) ≫ intervalMaxMap := by
  ext ⟨⟨n⟩⟩ z i
  rcases z with ⟨⟨x, y⟩, t⟩
  change ((intervalMinMap.app (op ⦋n⦌)
      (intervalMaxMap.app (op ⦋n⦌) (x, y), t) : (Δ[1] : SSet.{u}) _⦋n⦌) i).val =
    ((intervalMaxMap.app (op ⦋n⦌)
      (intervalMinMap.app (op ⦋n⦌) (x, t),
        intervalMinMap.app (op ⦋n⦌) (y, t)) : (Δ[1] : SSet.{u}) _⦋n⦌) i).val
  simp only [intervalMinMap_apply, intervalMaxMap_apply]
  exact congrArg Fin.val (min_max_distrib_right _ _ _)

/-- For any simplicial set Z in universe u and A=Δ[1], (const₀:Z→A)⊗id_A followed by interval
minimum is const₀:Z⊗A→A. The vertex 0 is absorbing for minimum. -/
theorem intervalMinMap_const_zero_left (Z : SSet.{u}) :
    (SSet.const (X := Z) (stdSimplex.obj₀Equiv.{u}.symm 0) ▷ (Δ[1] : SSet.{u})) ≫
        intervalMinMap = SSet.const (stdSimplex.obj₀Equiv.{u}.symm 0) := by
  ext ⟨⟨n⟩⟩ z i
  change (min (0 : Fin 2) (z.2 i)).val = 0
  exact congrArg Fin.val (min_eq_left (Fin.zero_le _))

end SSet
