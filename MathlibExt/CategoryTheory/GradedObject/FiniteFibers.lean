/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import MathlibExt.CategoryTheory.GradedObject.Preadditive

/-!
# Pushforward of graded objects along fiber maps

Pushforward along a map of grading types is a coproduct over each
fiber. Exactness of the fiber coproducts gives preservation of finite
limits; colimits are preserved whenever they exist. For finite fibers,
finite coproducts give existence and finite biproducts give the
finite-limit preservation theorem.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe w w' v u

namespace GradedObject

variable {I : Type w} {J : Type w'} {C : Type u} [Category.{v} C]

/-- A map of grading types has finite fibers when every inverse image of a
point is finite. -/
abbrev FiniteFibers (p : I → J) : Prop := ∀ j, Finite (p ⁻¹' {j})

/-- A graded object admits pushforward along a finite-fiber map whenever the
target category has finite coproducts. -/
instance hasMap_of_finiteFibers (X : GradedObject I C) (p : I → J)
    [FiniteFibers p] [HasFiniteCoproducts C] : X.HasMap p := by
  intro j
  infer_instance

/-- The inclusion of a fiber of a map of grading types. -/
def fiberInclusion (p : I → J) (j : J) :
    Discrete (p ⁻¹' {j}) ⥤ Discrete I :=
  Discrete.functor fun i => ⟨i.1⟩

/-- Evaluation after pushing a graded object forward is the coproduct of its
restriction to the corresponding fiber. -/
noncomputable def mapCompEvalIso (p : I → J)
    [∀ j, HasColimitsOfShape (Discrete (p ⁻¹' {j})) C] (j : J) :
    map C p ⋙ eval j ≅
      (piEquivalenceFunctorDiscrete I C).functor ⋙
        (Functor.whiskeringLeft (Discrete (p ⁻¹' {j})) (Discrete I) C).obj
          (fiberInclusion p j) ⋙ colim :=
  Iso.refl _

/-- Pushforward preserves limits of a finite shape when the coproduct over
each fiber is exact and the target category has limits of that shape. -/
noncomputable instance preservesLimitsOfShape_map_of_exact_fibers
    (K : Type) [SmallCategory K] [FinCategory K] (p : I → J)
    [∀ j, HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [∀ j, HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasLimitsOfShape K C] : PreservesLimitsOfShape K (map C p) := by
  let E := (piEquivalenceFunctorDiscrete J C).functor
  let : PreservesLimitsOfShape K (map C p ⋙ E) := by
    apply preservesLimitsOfShape_of_evaluation _ K
    rintro ⟨j⟩
    change PreservesLimitsOfShape K (map C p ⋙ eval j)
    let : PreservesLimitsOfShape K (piEquivalenceFunctorDiscrete I C).functor :=
      inferInstance
    let : PreservesLimitsOfShape K
        ((Functor.whiskeringLeft (Discrete (p ⁻¹' {j})) (Discrete I) C).obj
          (fiberInclusion p j)) :=
      CategoryTheory.whiskeringLeft_preservesLimitsOfShape K (fiberInclusion p j)
    let : PreservesFiniteLimits (colim (J := Discrete (p ⁻¹' {j})) (C := C)) :=
      HasExactColimitsOfShape.preservesFiniteLimits
    let : PreservesLimitsOfShape K (colim (J := Discrete (p ⁻¹' {j})) (C := C)) :=
      inferInstance
    exact preservesLimitsOfShape_of_natIso (mapCompEvalIso (C := C) p j).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves (map C p) E

/-- Pushforward preserves finite limits when the coproduct over each fiber is
exact. -/
noncomputable instance preservesFiniteLimits_map_of_exact_fibers (p : I → J)
    [∀ j, HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [∀ j, HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasFiniteLimits C] : PreservesFiniteLimits (map C p) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Pushforward preserves colimits of a shape whenever they exist in the
target category. -/
noncomputable instance preservesColimitsOfShape_map
    (K : Type*) [Category* K] (p : I → J)
    [∀ j, HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasColimitsOfShape K C] : PreservesColimitsOfShape K (map C p) := by
  let E := (piEquivalenceFunctorDiscrete J C).functor
  let : PreservesColimitsOfShape K (map C p ⋙ E) := by
    apply preservesColimitsOfShape_of_evaluation _ K
    rintro ⟨j⟩
    change PreservesColimitsOfShape K (map C p ⋙ eval j)
    let : PreservesColimitsOfShape K (piEquivalenceFunctorDiscrete I C).functor :=
      inferInstance
    let : PreservesColimitsOfShape K
        ((Functor.whiskeringLeft (Discrete (p ⁻¹' {j})) (Discrete I) C).obj
          (fiberInclusion p j)) :=
      CategoryTheory.whiskeringLeft_preservesColimitsOfShape K (fiberInclusion p j)
    let : PreservesColimitsOfShape K (colim (J := Discrete (p ⁻¹' {j})) (C := C)) :=
      inferInstance
    exact preservesColimitsOfShape_of_natIso (mapCompEvalIso (C := C) p j).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (map C p) E

/-- Pushforward preserves finite colimits whenever they exist in the target
category. -/
noncomputable instance preservesFiniteColimits_map (p : I → J)
    [∀ j, HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasFiniteColimits C] : PreservesFiniteColimits (map C p) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- Finite-fiber pushforward preserves finite limits in a category with
finite biproducts. -/
theorem preservesFiniteLimits_map_of_finiteFibers (p : I → J)
    [FiniteFibers p] [HasZeroMorphisms C] [HasFiniteBiproducts C]
    [HasFiniteLimits C] : PreservesFiniteLimits (map C p) :=
  inferInstance

/-- Finite-fiber pushforward preserves finite colimits whenever they exist. -/
theorem preservesFiniteColimits_map_of_finiteFibers (p : I → J)
    [FiniteFibers p] [HasFiniteColimits C] :
    PreservesFiniteColimits (map C p) :=
  inferInstance


section Total

variable (β : Type) [HasCoproducts.{0} C]

/-- The total functor preserves finite limits when coproducts of the grading
shape are exact. -/
noncomputable instance total_preservesFiniteLimits_of_exact
    [HasExactColimitsOfShape (Discrete β) C] :
    PreservesFiniteLimits (total β C) := by
  change PreservesFiniteLimits (Limits.Sigma.functor β)
  exact preservesFiniteLimits_of_natIso
    (piEquivalenceFunctorDiscreteCompColim β)

/-- The total functor preserves every existing finite colimit. -/
noncomputable instance total_preservesFiniteColimits :
    PreservesFiniteColimits (total β C) := by
  change PreservesFiniteColimits (Limits.Sigma.functor β)
  exact preservesFiniteColimits_of_natIso
    (piEquivalenceFunctorDiscreteCompColim β)

end Total

end GradedObject

end CategoryTheory


namespace CategoryTheory.GradedObject

universe u v w uD vD wJ

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {I : Type w} {J : Type wJ} (F : C ⥤ D) (X : GradedObject I C) (p : I → J)
  [X.HasMap p]
  [∀ j, PreservesColimit (Discrete.functor (X.mapObjFun p j)) F]

/-- Preserving each actual fiber coproduct supplies the mapped graded-object coproducts. -/
theorem hasMap_of_preserves :
    GradedObject.HasMap (fun i => F.obj (X i) : GradedObject I D) p := by
  intro j
  exact ⟨⟨⟨_, isColimitOfHasCoproductOfPreservesColimit F (X.mapObjFun p j)⟩⟩⟩

end CategoryTheory.GradedObject
