/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.OuterEdgewiseDiagonal

/-!
# Outer-edgewise diagonal regression tests

These tests pin outer precomposition, functoriality, outer and inner faces and
degeneracies, the literal fixed-inner `esdComparison`, low diagonal degrees,
the target-vertex orientation, constant and representable bisimplicial
objects, universe polymorphism, standard axioms, and the absence of later
Stage, pointed, or Q/S claims.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Opposite

open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace OuterEdgewiseDiagonalTests

section Functoriality

variable (B : SimplicialObject SSet.{u})

example (a : SimplexCategoryᵒᵖ) :
    (SSet.outerEdgewise.obj B).obj a =
      B.obj (SimplexCategory.edgewiseQ.op.obj a) :=
  SSet.outerEdgewise_obj_obj B a

example {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (SSet.outerEdgewise.obj B).map f =
      B.map (SimplexCategory.edgewiseQ.op.map f) :=
  SSet.outerEdgewise_obj_map B f

example :
    SSet.outerEdgewise.map (𝟙 B) =
      𝟙 (SSet.outerEdgewise.obj B) :=
  SSet.outerEdgewise.map_id B

example {C D : SimplicialObject SSet.{u}}
    (f : B ⟶ C) (g : C ⟶ D) :
    SSet.outerEdgewise.map (f ≫ g) =
      SSet.outerEdgewise.map f ≫ SSet.outerEdgewise.map g :=
  SSet.outerEdgewise.map_comp f g

example {C : SimplicialObject SSet.{u}} (η : B ⟶ C)
    (a : SimplexCategoryᵒᵖ) :
    (SSet.outerEdgewise.map η).app a =
      η.app (SimplexCategory.edgewiseQ.op.obj a) :=
  SSet.outerEdgewise_map_app η a

example {C : SimplicialObject SSet.{u}} (η : B ⟶ C) :
    SSet.outerEdgewise.map η ≫
        SSet.outerEdgewiseComparison.app C =
      SSet.outerEdgewiseComparison.app B ≫ η :=
  SSet.outerEdgewiseComparison.naturality η

end Functoriality

section OuterAndInnerOperators

variable (B : SimplicialObject SSet.{u})

example {n : ℕ} (i : Fin (n + 2)) :
    (SSet.outerEdgewise.obj B).δ i =
      B.map
        (SimplexCategory.edgewiseQ.map
          (SimplexCategory.δ i)).op :=
  rfl

example {n : ℕ} (i : Fin (n + 1)) :
    (SSet.outerEdgewise.obj B).σ i =
      B.map
        (SimplexCategory.edgewiseQ.map
          (SimplexCategory.σ i)).op :=
  rfl

example (a : SimplexCategoryᵒᵖ) {n : ℕ} (i : Fin (n + 2)) :
    ((SSet.outerEdgewise.obj B).obj a).δ i =
      (B.obj (SimplexCategory.edgewiseQ.op.obj a)).δ i :=
  rfl

example (a : SimplexCategoryᵒᵖ) {n : ℕ} (i : Fin (n + 1)) :
    ((SSet.outerEdgewise.obj B).obj a).σ i =
      (B.obj (SimplexCategory.edgewiseQ.op.obj a)).σ i :=
  rfl

end OuterAndInnerOperators

section Components

variable (B : SimplicialObject SSet.{u})

example (a b : SimplexCategoryᵒᵖ) :
    ((SSet.outerEdgewiseComparison.app B).app a).app b =
      (B.map
        (SimplexCategory.edgewiseRightInclusion.app a.unop).op).app b :=
  SSet.outerEdgewiseComparison_app_app_app B a b

example :
    (SSet.simplicialTransposeFunctor.map
      (SSet.outerEdgewiseComparison.app B)).app
        (op (SimplexCategory.mk 0)) =
      SSet.esdComparison.app
        (SSet.simplicialRow B (op (SimplexCategory.mk 0))) :=
  SSet.outerEdgewiseComparison_transpose_app B 0

example :
    (SSet.simplicialTransposeFunctor.map
      (SSet.outerEdgewiseComparison.app B)).app
        (op (SimplexCategory.mk 1)) =
      SSet.esdComparison.app
        (SSet.simplicialRow B (op (SimplexCategory.mk 1))) :=
  SSet.outerEdgewiseComparison_transpose_app B 1

example :
    (SSet.simplicialTransposeFunctor.map
      (SSet.outerEdgewiseComparison.app B)).app
        (op (SimplexCategory.mk 2)) =
      SSet.esdComparison.app
        (SSet.simplicialRow B (op (SimplexCategory.mk 2))) :=
  SSet.outerEdgewiseComparison_transpose_app B 2

example :
    (SSet.outerEdgewiseDiagonalComparison B).app
        (op (SimplexCategory.mk 0)) =
      (B.map
        (SimplexCategory.edgewiseRightInclusion.app
          (SimplexCategory.mk 0)).op).app
            (op (SimplexCategory.mk 0)) :=
  SSet.outerEdgewiseDiagonalComparison_app B _

example :
    (SSet.outerEdgewiseDiagonalComparison B).app
        (op (SimplexCategory.mk 1)) =
      (B.map
        (SimplexCategory.edgewiseRightInclusion.app
          (SimplexCategory.mk 1)).op).app
            (op (SimplexCategory.mk 1)) :=
  SSet.outerEdgewiseDiagonalComparison_app B _

example :
    (SSet.outerEdgewiseDiagonalComparison B).app
        (op (SimplexCategory.mk 2)) =
      (B.map
        (SimplexCategory.edgewiseRightInclusion.app
          (SimplexCategory.mk 2)).op).app
            (op (SimplexCategory.mk 2)) :=
  SSet.outerEdgewiseDiagonalComparison_app B _

example :
    SSet.realizationWeakEquivalences
      (SSet.outerEdgewiseDiagonalComparison B) :=
  SSet.outerEdgewiseDiagonalComparison_mem_realizationWeakEquivalences B

end Components

section BoundaryObjects

/-- A simplicial set in the outer variable, made constant in the inner
variable. -/
private def outerVariable (X : SSet.{u}) :
    SimplicialObject SSet.{u} :=
  X ⋙ SimplicialObject.const (Type u)

private def deltaOneIdentity :
    (SSet.stdSimplex.{u}.obj (SimplexCategory.mk 1)).obj
      (op (SimplexCategory.mk 1)) :=
  SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.Hom.mk OrderHom.id :
      SimplexCategory.mk 1 ⟶ SimplexCategory.mk 1)

/-- In outer degree zero, the comparison takes the identity edge to its
target vertex. -/
example :
    (((SSet.outerEdgewiseComparison.app
      (outerVariable (SSet.stdSimplex.{u}.obj
        (SimplexCategory.mk 1)))).app
          (op (SimplexCategory.mk 0))).app
            (op (SimplexCategory.mk 0))) deltaOneIdentity =
      (SSet.stdSimplex.{u}.obj (SimplexCategory.mk 1)).δ 0
        deltaOneIdentity := by
  rw [SSet.outerEdgewiseComparison_app_app_app]
  change (SSet.stdSimplex.{u}.obj (SimplexCategory.mk 1)).map
    (SimplexCategory.edgewiseRightInclusion.app
      (SimplexCategory.mk 0)).op deltaOneIdentity = _
  rw [SimplexCategory.edgewiseRightInclusion_app_zero]
  rfl

/-- The same component does not select the source vertex. -/
example :
    (((SSet.outerEdgewiseComparison.app
      (outerVariable (SSet.stdSimplex.{u}.obj
        (SimplexCategory.mk 1)))).app
          (op (SimplexCategory.mk 0))).app
            (op (SimplexCategory.mk 0))) deltaOneIdentity ≠
      SSet.stdSimplex.objEquiv.symm
        (SimplexCategory.δ (1 : Fin 2)) := by
  rw [SSet.outerEdgewiseComparison_app_app_app]
  change (SSet.stdSimplex.{u}.obj (SimplexCategory.mk 1)).map
    (SimplexCategory.edgewiseRightInclusion.app
      (SimplexCategory.mk 0)).op deltaOneIdentity ≠ _
  rw [SimplexCategory.edgewiseRightInclusion_app_zero]
  change SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.δ (0 : Fin 2)) ≠
    SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.δ (1 : Fin 2))
  intro h
  exact (by decide : SimplexCategory.δ (0 : Fin 2) ≠
    SimplexCategory.δ (1 : Fin 2))
      (SSet.stdSimplex.objEquiv.symm.injective h)

/-- A constant bisimplicial set. -/
private def constantBisimplicial (A : Type u) :
    SimplicialObject SSet.{u} :=
  (SimplicialObject.const SSet.{u}).obj
    ((SimplicialObject.const (Type u)).obj A)

example (A : Type u) (a b : SimplexCategoryᵒᵖ) (x : A) :
    ((SSet.outerEdgewiseComparison.app
      (constantBisimplicial A)).app a).app b x = x :=
  rfl

/-- A bisimplicial object that is outer-constant at a representable
simplicial set. -/
private def representableBisimplicial (n : SimplexCategory) :
    SimplicialObject SSet.{u} :=
  (SimplicialObject.const SSet.{u}).obj (SSet.stdSimplex.{u}.obj n)

example (n : SimplexCategory) (a b : SimplexCategoryᵒᵖ)
    (x : (SSet.stdSimplex.{u}.obj n).obj b) :
    ((SSet.outerEdgewiseComparison.app
      (representableBisimplicial n)).app a).app b x = x :=
  rfl

example (n : SimplexCategory) :
    SSet.realizationWeakEquivalences
      (SSet.outerEdgewiseDiagonalComparison
        (representableBisimplicial.{u} n)) :=
  SSet.outerEdgewiseDiagonalComparison_mem_realizationWeakEquivalences _

end BoundaryObjects

section Universes

variable (B₀ : SimplicialObject SSet.{0})
variable (B₁ : SimplicialObject SSet.{1})

example : SimplicialObject SSet.{0} ⥤ SimplicialObject SSet.{0} :=
  SSet.outerEdgewise

example : SimplicialObject SSet.{1} ⥤ SimplicialObject SSet.{1} :=
  SSet.outerEdgewise

example :
    SSet.realizationWeakEquivalences
      (SSet.outerEdgewiseDiagonalComparison B₀) :=
  SSet.outerEdgewiseDiagonalComparison_mem_realizationWeakEquivalences B₀

example :
    SSet.realizationWeakEquivalences
      (SSet.outerEdgewiseDiagonalComparison B₁) :=
  SSet.outerEdgewiseDiagonalComparison_mem_realizationWeakEquivalences B₁

end Universes

section Nonclaims

/- error: Unknown identifier -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.outerEdgewiseStageDiagonalComparison

/- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.outerEdgewiseQSComparison

/- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.outerEdgewisePointedComparison

/- failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth SSet.outerEdgewise.IsEquivalence

example : True := by
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory SSet.{u} := inferInstance
  trivial

end Nonclaims

#print axioms SSet.outerEdgewise
#print axioms SSet.outerEdgewise_obj_obj
#print axioms SSet.outerEdgewise_obj_map
#print axioms SSet.outerEdgewiseComparison
#print axioms SSet.outerEdgewiseComparison_transpose_app
#print axioms SSet.outerEdgewiseDiagonalComparison
#print axioms
  SSet.outerEdgewiseDiagonalComparison_mem_realizationWeakEquivalences

end OuterEdgewiseDiagonalTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
