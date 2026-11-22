/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeImageComposition

/-!
# The genuine cosimplicial original quotient-cube diagram

The actual right-join quotient operators preserve identity and
composition on every original path representative. The structural zero
adjunction is retained literally, and repeated adjunction is idempotent.
No frame or realized-Hom identification is part of this diagram.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.RightCubeCosimplicial
open PathLastMaximum RightCubeRelations PathMaximumOperators
variable {n m k : ℕ}

/-- The whole original identity operator retains every supplied original source-to-last path. -/
theorem functor_id (n : ℕ) : RightCubeOperator.functor.{u} (𝟙 (SimplexCategory.mk n)) = 𝟭 (LastPath.{u} (0 :
    Fin (n + 1))) := by
  refine Functor.ext (fun p => ?_) ?_
  · apply SimplicialThickening.Path.ext
    ext x
    have hExt := FixedFrontOperators.extension_id n
    change (x = ULift.up.{u} (0 : Fin (n + 2)) ∨ x ∈ (extension (𝟙 (SimplexCategory.mk
      n))).toOrderHom.uliftMap '' p.I) ↔ x ∈ p.I
    have hMap : (fun x : ULift.{u} (Fin (n + 2)) => ULift.up.{u} ((extension (𝟙 (SimplexCategory.mk
      n))).toOrderHom x.down)) = id := by
      funext x
      exact (congrArg ULift.up (congrArg (fun f => f.toOrderHom x.down) hExt)).trans (ULift.up_down x)
    change (x = ULift.up.{u} (0 : Fin (n + 2)) ∨
      x ∈ (fun x : ULift.{u} (Fin (n + 2)) => ULift.up.{u} ((extension (𝟙 (SimplexCategory.mk
        n))).toOrderHom x.down)) '' p.I) ↔ x ∈ p.I
    rw [hMap, Set.image_id]
    constructor
    · rintro (rfl | hx)
      · exact p.left
      · exact hx
    · intro hx
      exact Or.inr hx
  · intro p q f
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The actual whole identity quotient operator is the original identity. -/
theorem map_id (n : ℕ) : RightCubeCosimplicialMaps.map.{u} (𝟙 (SimplexCategory.mk n)) = 𝟙
    (RightCubeRelations.object n) := by
  ext q a
  induction a using _root_.Quotient.inductionOn with
  | _ a =>
    change _root_.Quotient.mk _ (a ⋙ RightCubeOperator.functor (𝟙 (SimplexCategory.mk n))) = _root_.Quotient.mk _ a
    exact congrArg (fun F => _root_.Quotient.mk _ (a ⋙ F)) (functor_id n)

/-- The actual quotient-cube diagram of original resolving simplex operators. -/
def diagram : SimplexCategory ⥤ SSet.{u} where
  obj n := RightCubeRelations.object.{u} n.len
  map θ := RightCubeCosimplicialMaps.map θ
  map_id n := by
    induction n using SimplexCategory.rec with
    | _ n => exact map_id n
  map_comp θ ψ := by
    ext q a
    induction a using _root_.Quotient.inductionOn with
    | _ a =>
      change _root_.Quotient.mk _ (a ⋙ RightCubeOperator.functor (θ ≫ ψ)) =
        _root_.Quotient.mk _ (a ⋙ RightCubeOperator.functor θ ⋙ RightCubeOperator.functor ψ)
      have h := RightCubeOperatorRelations.image_prepend_relation ψ (θ.toOrderHom 0)
        (a ⋙ PathMaximumOperators.imageFunctor θ 0)
      have hC : a ⋙ RightCubeOperator.functor (θ ≫ ψ) =
          a ⋙ PathMaximumOperators.imageFunctor θ 0 ⋙ PathMaximumOperators.imageFunctor ψ (θ.toOrderHom 0) ⋙
            RightCubeRelations.prependFunctor (ψ.toOrderHom (θ.toOrderHom 0)) := by
        refine Functor.ext (fun j => ?_) ?_
        · apply SimplicialThickening.Path.ext
          change ({_} ∪ (PathMaximumOperators.image (θ ≫ ψ) 0 (a.obj j)).I) =
            ({_} ∪ (PathMaximumOperators.image ψ (θ.toOrderHom 0) (PathMaximumOperators.image θ 0 (a.obj j))).I)
          exact congrArg (fun s => ({ULift.up.{u} 0} ∪ s))
            (RightCubeImageComposition.image_comp_I θ ψ 0 (a.obj j)).symm
        · intro j k f
          apply InducedCategory.Hom.ext
          exact Subsingleton.elim _ _
      exact _root_.Quotient.sound (hC ▸ Relation.EqvGen.symm _ _ h)

end CategoryTheory.CoherentRealization.RightCubeCosimplicial
