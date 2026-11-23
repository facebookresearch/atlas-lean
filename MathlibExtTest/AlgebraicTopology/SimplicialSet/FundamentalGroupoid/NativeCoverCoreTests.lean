/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.PathGroupoidCover
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Native covers and path-cover actions

The three-cycle distinguishes inverse deck action from positive precomposition.
The two-edge simplex distinguishes the order of noncommuting permutations.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits SSet SSet.KanComplex
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace MathlibExtTest.NativeCoverCore

/-- Ordinary groupoid fibers infer their published groupoid and lift instances. -/
theorem fresh_under_instances :
    let y := SingleObj.star (Equiv.Perm (Fin 3))
    (Under.forget y).IsIsofibration ∧ CategoryTheory.IsGroupoid (Under y) := by
  exact ⟨inferInstance, inferInstance⟩

/-- Kan-ness is derived for an actual nontrivial group nerve and its original cover. -/
theorem nontrivial_group_nerve_and_native_cover_kan :
    let X : SSet := nerve (SingleObj (Equiv.Perm (Fin 3)))
    let x : X _⦋0⦌ := ComposableArrows.mk₀ (SingleObj.star (Equiv.Perm (Fin 3)))
    SSet.KanComplex X ∧ SSet.KanComplex (nativeCover X x) := by
  let X : SSet := nerve (SingleObj (Equiv.Perm (Fin 3)))
  let x : X _⦋0⦌ := ComposableArrows.mk₀ (SingleObj.star (Equiv.Perm (Fin 3)))
  let : SSet.KanComplex X := SSet.kanComplex_nerve_of_groupoid _
  exact ⟨inferInstance, nativeCover_kanComplex X x⟩

/-- The deck of a three-cycle acts by its inverse on the original identity path. -/
theorem three_cycle_deck_is_inverse_not_positive :
    let G := Equiv.Perm (Fin 3)
    let y := SingleObj.star G
    let a : G := Equiv.swap 0 1
    let b : G := Equiv.swap 1 2
    let D := CategoryTheory.Under.nativePathGroupoidCover y
    (show G from ((D.deck (SingleObj.toEnd G (a * b))).obj
      (Under.mk (X := y) (Y := y) (1 : G))).hom)
        (0 : Fin 3) = 2 ∧
      (a * b) 0 ≠ 2 := by
  let G := Equiv.Perm (Fin 3)
  let y := SingleObj.star G
  let a : G := Equiv.swap 0 1
  let b : G := Equiv.swap 1 2
  let D := CategoryTheory.Under.nativePathGroupoidCover y
  constructor
  · change ((1 : G) * (a * b)⁻¹) (0 : Fin 3) = 2
    rw [one_mul]
    decide
  · decide

/-- The original two-edge lift ends at the covariantly ordered composite. -/
theorem noncommuting_two_edge_cover_coordinate :
    let G := Equiv.Perm (Fin 3)
    let y := SingleObj.star G
    let a : y ⟶ y := Equiv.swap (0 : Fin 3) 1
    let b : y ⟶ y := Equiv.swap (1 : Fin 3) 2
    let σ : ComposableArrows (SingleObj G) 2 := ComposableArrows.mk₂ a b
    let D := CategoryTheory.Under.nativePathGroupoidCover y
    (show G from (((D.simplex_equiv 2).symm ⟨σ, (1 : G)⟩).obj 2).hom)
        (0 : Fin 3) = 2 ∧
      D.simplex_equiv 2 ((D.simplex_equiv 2).symm ⟨σ, (1 : G)⟩) = ⟨σ, (1 : G)⟩ := by
  let G := Equiv.Perm (Fin 3)
  let y := SingleObj.star G
  let a : y ⟶ y := Equiv.swap (0 : Fin 3) 1
  let b : y ⟶ y := Equiv.swap (1 : Fin 3) 2
  let σ : ComposableArrows (SingleObj G) 2 := ComposableArrows.mk₂ a b
  let D := CategoryTheory.Under.nativePathGroupoidCover y
  constructor
  · change
      (show G from (((CategoryTheory.Under.nerveSimplexEquiv y 2).symm
        ⟨σ, (1 : G)⟩).obj 2).hom) (0 : Fin 3) = 2
    rw [CategoryTheory.Under.nerveSimplexEquiv_symm_obj]
    change ((show G from b) * ((show G from a) * (1 : G))) (0 : Fin 3) = 2
    decide
  · exact (D.simplex_equiv 2).apply_symm_apply ⟨σ, (1 : G)⟩

/-- Both constructed deck maps cancel on the actual original identity vertex. -/
theorem native_deck_both_roundtrips_at_original_vertex
    (X : SSet.{u}) (x : X _⦋0⦌) (g : End (SSet.FundamentalGroupoid.mk x)) :
    let e := nativeCoverDeckIso (X := X) (x := x) g
    let v := nativeCoverIdentityPoint X x
    e.inv.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) v) = v ∧
      e.hom.app (Opposite.op ⦋0⦌) (e.inv.app (Opposite.op ⦋0⦌) v) = v := by
  let e := nativeCoverDeckIso (X := X) (x := x) g
  let v := nativeCoverIdentityPoint X x
  constructor
  · exact congrArg (fun f : nativeCover X x ⟶ nativeCover X x =>
      f.app (Opposite.op ⦋0⦌) v) e.hom_inv_id
  · exact congrArg (fun f : nativeCover X x ⟶ nativeCover X x =>
      f.app (Opposite.op ⦋0⦌) v) e.inv_hom_id

/-- The actual native vertex action takes coordinate ψ(b) to ψ(b*a⁻¹). -/
theorem native_vertex_action_original_inverse_right_coordinate
    (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌) (a b : π 1 X x) :
    let ψ := piOneMulEquivFundamentalGroupoidEnd x
    let e := nativeCoverVertexPathEquiv (X := X) (x := x) x
    let v := e.symm (ψ b).asHom
    letI := nativeCoverPiOneVertexFiberAction x x
    e (a • v) = (ψ (b * a⁻¹)).asHom := by
  let ψ := piOneMulEquivFundamentalGroupoidEnd x
  let e := nativeCoverVertexPathEquiv (X := X) (x := x) x
  let v := e.symm (ψ b).asHom
  let := nativeCoverPiOneVertexFiberAction x x
  have hAct := nativeCoverVertexPathEquiv_smul x x a v
  have hCoordinate : e v = (ψ b).asHom := e.apply_symm_apply (ψ b).asHom
  have hProduct : ψ (b * a⁻¹) = ψ b * (ψ a)⁻¹ := by
    rw [map_mul, map_inv]
  have hArrow : ((ψ a)⁻¹).asHom ≫ (ψ b).asHom = (ψ (b * a⁻¹)).asHom :=
    (congrArg (fun f : End (SSet.FundamentalGroupoid.mk x) => f.asHom) hProduct).symm
  exact hAct.trans
    ((congrArg (fun γ => ((ψ a)⁻¹).asHom ≫ γ) hCoordinate).trans hArrow)

/-- Identity and both ordinary map legs act on the same original cover vertex. -/
theorem native_cover_map_identity_composition_on_original_vertices
    {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X _⦋0⦌)
    (v : (nativeCover X x) _⦋0⦌) :
    (nativeCoverMap (𝟙 X) x).app (Opposite.op ⦋0⦌) v = v ∧
      (nativeCoverMap (f ≫ g) x).app (Opposite.op ⦋0⦌) v =
        (nativeCoverMap g (f.app (Opposite.op ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
          ((nativeCoverMap f x).app (Opposite.op ⦋0⦌) v) := by
  constructor
  · exact congrArg (fun h : nativeCover X x ⟶ nativeCover X x =>
      h.app (Opposite.op ⦋0⦌) v) (nativeCoverMap_id x)
  · exact congrArg (fun h : nativeCover X x ⟶
      nativeCover Z ((f ≫ g).app (Opposite.op ⦋0⦌) x) =>
        h.app (Opposite.op ⦋0⦌) v) (nativeCoverMap_comp f g x).symm

end MathlibExtTest.NativeCoverCore

end
