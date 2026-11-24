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

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import MathlibExt.CategoryTheory.GradedObject.Preadditive

/-!
# Pushforward of graded objects along finite-fiber maps

For a map `p : I → J`, pushforward is defined when the coproduct indexed by each
fiber exists. In particular, finite coproducts suffice when the fibers are finite.
Evaluation of the pushforward at `j` is naturally isomorphic to restriction to
`p ⁻¹' {j}` followed by the coproduct functor. Exact fiber coproducts give preservation
of finite limits when those limits exist; finite fibers and finite biproducts give
this exactness in a category with zero morphisms. Pushforward also preserves finite
colimits when the category has them and the fiber coproducts exist.
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

/-- Suppose `C` has coproducts indexed by every fiber of `p`. There is a natural isomorphism
from pushforward followed by evaluation at `j` to restriction along `fiberInclusion p j`
followed by the coproduct functor, viewing graded objects as functors on a discrete category. -/
noncomputable def mapCompEvalIso (p : I → J)
    [∀ j, HasColimitsOfShape (Discrete (p ⁻¹' {j})) C] (j : J) :
    map C p ⋙ eval j ≅
      (piEquivalenceFunctorDiscrete I C).functor ⋙
        (Functor.whiskeringLeft (Discrete (p ⁻¹' {j})) (Discrete I) C).obj
          (fiberInclusion p j) ⋙ colim :=
  Iso.refl _

/-- For a finite category `K`, pushforward along `p` preserves `K`-shaped limits if `C`
has `K`-shaped limits and the coproducts indexed by each fiber of `p` exist and are exact. -/
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
    exact preservesLimitsOfShape_of_natIso (mapCompEvalIso (C := C) p j).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves (map C p) E

/-- Pushforward along `p` preserves finite limits if `C` has finite limits and the
coproducts indexed by each fiber of `p` exist and are exact. -/
noncomputable instance preservesFiniteLimits_map_of_exact_fibers (p : I → J)
    [∀ j, HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [∀ j, HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasFiniteLimits C] : PreservesFiniteLimits (map C p) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Pushforward along `p` preserves `K`-shaped colimits if `C` has `K`-shaped colimits
and coproducts indexed by each fiber of `p`. -/
noncomputable instance preservesColimitsOfShape_map
    (K : Type*) [Category* K] (p : I → J)
    [∀ j, HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasColimitsOfShape K C] : PreservesColimitsOfShape K (map C p) := by
  let E := (piEquivalenceFunctorDiscrete J C).functor
  let : PreservesColimitsOfShape K (map C p ⋙ E) := by
    apply preservesColimitsOfShape_of_evaluation _ K
    rintro ⟨j⟩
    change PreservesColimitsOfShape K (map C p ⋙ eval j)
    exact preservesColimitsOfShape_of_natIso (mapCompEvalIso (C := C) p j).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (map C p) E

/-- Pushforward along `p` preserves finite colimits if `C` has finite colimits and
coproducts indexed by each fiber of `p`. -/
noncomputable instance preservesFiniteColimits_map (p : I → J)
    [∀ j, HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasFiniteColimits C] : PreservesFiniteColimits (map C p) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- Pushforward along a finite-fiber map `p` preserves finite limits if `C` has zero
morphisms, finite biproducts, and finite limits. -/
theorem preservesFiniteLimits_map_of_finiteFibers (p : I → J)
    [FiniteFibers p] [HasZeroMorphisms C] [HasFiniteBiproducts C]
    [HasFiniteLimits C] : PreservesFiniteLimits (map C p) :=
  inferInstance

/-- Pushforward along a finite-fiber map `p` preserves finite colimits if `C` has finite
colimits. -/
theorem preservesFiniteColimits_map_of_finiteFibers (p : I → J)
    [FiniteFibers p] [HasFiniteColimits C] :
    PreservesFiniteColimits (map C p) :=
  inferInstance


section Total

variable (β : Type) [HasCoproducts.{0} C]

/-- For `β : Type`, if `C` has small coproducts and its `β`-indexed coproducts are exact,
the total functor, which takes the coproduct over all grades, preserves finite limits. -/
noncomputable instance total_preservesFiniteLimits_of_exact
    [HasExactColimitsOfShape (Discrete β) C] :
    PreservesFiniteLimits (total β C) := by
  change PreservesFiniteLimits (Limits.Sigma.functor β)
  exact preservesFiniteLimits_of_natIso
    (piEquivalenceFunctorDiscreteCompColim β)

/-- For `β : Type` and `C` with small coproducts, the total functor preserves finite colimits. -/
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
