/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

public import MathlibExt.Algebra.Homology.HomologicalComplex.EndpointCofreeBasic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# The adjunction for endpoint cofree complexes

Let C be an abelian category and c a complex shape on an arbitrary index type ι.
The functor forgetting the differential is left adjoint to the endpoint cofree
complex functor on GradedObject ι C. The right adjoint uses the cofree terms
Iᵢ ⊕ Eᵢ, where Eᵢ is I(c.next i) on an outgoing edge and zero at an endpoint.

The hom equivalence is the existing coefficient-family equivalence, with its
orientation reversed. The unit has first coefficient the identity and second
coefficient the source differential along an outgoing edge. The counit is the
family of first projections. Faithfulness of the forgetful functor makes the
unit a monomorphism of complexes.

The index, object and morphism universes are independent. The construction
uses the existing cofree complex and coefficient maps for every shape.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w

variable (C : Type u) [Category.{v} C] [Abelian C]
  {ι : Type w} (c : ComplexShape ι)

/-- The endpoint cofree construction is a functor from coefficient families to
complexes of any shape. Its coefficient maps are the existing cofree maps. -/
def endpointCofreeFunctor : GradedObject ι C ⥤ HomologicalComplex C c where
  obj I := endpointCofree (c := c) I
  map a := endpointCofreeMap (c := c) a
  map_id I := endpointCofreeMap_id (c := c) I
  map_comp a b := (endpointCofreeMap_comp (c := c) a b).symm

/-- Forgetting the differential is left adjoint to the endpoint cofree functor,
using the existing bijection between complex maps and coefficient families. -/
def endpointCofreeAdjunction : forget C c ⊣ endpointCofreeFunctor C c :=
  Adjunction.mkOfHomEquiv
    { homEquiv K I := (endpointCofreeHomEquiv K I).symm
      homEquiv_naturality_left_symm := by
        intro K' K I f g
        funext i
        change (f.f i ≫ g.f i) ≫ endpointCofreeProjection (c := c) I i =
          f.f i ≫ (g.f i ≫ endpointCofreeProjection (c := c) I i)
        exact Category.assoc _ _ _
      homEquiv_naturality_right := by
        intro K I J a b
        exact (endpointCofreeHom_naturality K a b).symm }

/-- The forgetful functor on complexes of an arbitrary shape has the endpoint
cofree complex functor as a right adjoint. -/
instance forget_isLeftAdjoint_endpointCofree : (forget C c).IsLeftAdjoint where
  exists_rightAdjoint := ⟨endpointCofreeFunctor C c, ⟨endpointCofreeAdjunction C c⟩⟩

/-- The endpoint cofree functor is a right adjoint to forgetting the differential,
including for shapes with endpoints. -/
instance endpointCofreeFunctor_isRightAdjoint :
    (endpointCofreeFunctor C c).IsRightAdjoint where
  exists_leftAdjoint := ⟨forget C c, ⟨endpointCofreeAdjunction C c⟩⟩

/-- The native adjunction hom equivalence is the existing coefficient-family
equivalence with its orientation reversed. -/
theorem endpointCofreeAdjunction_homEquiv (K : HomologicalComplex C c)
    (I : GradedObject ι C) :
    (endpointCofreeAdjunction C c).homEquiv K I = (endpointCofreeHomEquiv K I).symm := by
  unfold endpointCofreeAdjunction
  exact congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) K) I

/-- A coefficient family is sent by the native adjunction equivalence to the
existing prescribed cofree complex morphism. -/
@[simp]
theorem endpointCofreeAdjunction_homEquiv_apply (K : HomologicalComplex C c)
    (I : GradedObject ι C) (a : (forget C c).obj K ⟶ I) :
    (endpointCofreeAdjunction C c).homEquiv K I a = endpointCofreeHom K I a :=
  congrArg
    (fun e : ((forget C c).obj K ⟶ I) ≃ (K ⟶ (endpointCofreeFunctor C c).obj I) => e a)
    (endpointCofreeAdjunction_homEquiv C c K I)

/-- The inverse native adjunction equivalence takes the first coefficient of a
complex morphism in each degree. -/
@[simp]
theorem endpointCofreeAdjunction_homEquiv_symm_apply (K : HomologicalComplex C c)
    (I : GradedObject ι C) (f : K ⟶ (endpointCofreeFunctor C c).obj I) :
    ((endpointCofreeAdjunction C c).homEquiv K I).symm f =
      fun i => f.f i ≫ endpointCofreeProjection (c := c) I i :=
  congrArg
    (fun e : ((forget C c).obj K ⟶ I) ≃ (K ⟶ (endpointCofreeFunctor C c).obj I) => e.symm f)
    (endpointCofreeAdjunction_homEquiv C c K I)

/-- The native adjunction unit maps each complex into the cofree complex on its
underlying graded family. -/
abbrev endpointCofreeUnit :
    𝟭 (HomologicalComplex C c) ⟶ forget C c ⋙ endpointCofreeFunctor C c :=
  (endpointCofreeAdjunction C c).unit

/-- The native adjunction counit is a morphism of coefficient families from the
underlying graded object of a cofree complex to its coefficients. -/
abbrev endpointCofreeCounit :
    endpointCofreeFunctor C c ⋙ forget C c ⟶ 𝟭 (GradedObject ι C) :=
  (endpointCofreeAdjunction C c).counit

/-- The unit is the prescribed cofree map with identity first coefficients. -/
@[simp]
theorem endpointCofreeUnit_app (K : HomologicalComplex C c) :
    (endpointCofreeUnit C c).app K =
      endpointCofreeHom K K.X (fun i => 𝟙 (K.X i)) := by
  calc
    _ = (endpointCofreeAdjunction C c).homEquiv K ((forget C c).obj K) (𝟙 _) :=
      ((endpointCofreeAdjunction C c).homEquiv_id K).symm
    _ = _ :=
      endpointCofreeAdjunction_homEquiv_apply C c K ((forget C c).obj K) (𝟙 _)

/-- The first coefficient of the unit is the identity in every degree. -/
@[reassoc (attr := simp)]
theorem endpointCofreeUnit_fst (K : HomologicalComplex C c) (i : ι) :
    ((endpointCofreeUnit C c).app K).f i ≫
        endpointCofreeProjection (c := c) K.X i = 𝟙 (K.X i) := by
  simpa only [endpointCofreeUnit_app, Functor.id_obj] using
    endpointCofreeHom_fst K K.X (fun i => 𝟙 (K.X i)) i

/-- Along an outgoing edge, the second coefficient of the unit, identified with
the next source term, is the source differential. -/
@[reassoc]
theorem endpointCofreeUnit_snd_of_rel (K : HomologicalComplex C c)
    {i j : ι} (hij : c.Rel i j) :
    (((endpointCofreeUnit C c).app K).f i ≫
        endpointCofreeSecondProjection (c := c) K.X i) ≫
        (endpointCofreeNextTermIso K.X hij).hom = K.d i j := by
  simpa only [endpointCofreeUnit_app, Functor.id_obj, Category.comp_id] using
    endpointCofreeHom_snd_of_rel K K.X (fun i => 𝟙 (K.X i)) hij

/-- At an index without an outgoing edge, the second coefficient of the unit is
the zero morphism to the optional zero term. -/
@[reassoc]
theorem endpointCofreeUnit_snd_of_no_next (K : HomologicalComplex C c) (i : ι)
    (hi : ¬ c.Rel i (c.next i)) :
    ((endpointCofreeUnit C c).app K).f i ≫
        endpointCofreeSecondProjection (c := c) K.X i = 0 :=
  (endpointCofreeNextTerm_isZero K.X i hi).eq_of_tgt _ _

/-- The cofree unit is a monomorphism of complexes, by the native theorem for a
faithful left adjoint. -/
theorem endpointCofreeUnit_mono (K : HomologicalComplex C c) :
    Mono ((endpointCofreeUnit C c).app K) :=
  Adjunction.unit_mono_of_L_faithful (endpointCofreeAdjunction C c) K

/-- The counit in degree i is the first projection from the cofree term to its
coefficient object Iᵢ. -/
@[simp]
theorem endpointCofreeCounit_app (I : GradedObject ι C) (i : ι) :
    ((endpointCofreeCounit C c).app I) i = endpointCofreeProjection (c := c) I i := by
  have h := (endpointCofreeAdjunction C c).homEquiv_symm_id I
  have h' := endpointCofreeAdjunction_homEquiv_symm_apply C c
    ((endpointCofreeFunctor C c).obj I) I (𝟙 _)
  simpa only [endpointCofreeFunctor, Functor.id_obj,
    HomologicalComplex.id_f, Category.id_comp] using congrFun (h.symm.trans h') i

/-- A cofree functor map followed by the first projection is the first projection
followed by the corresponding coefficient map. -/
@[reassoc (attr := simp)]
theorem endpointCofreeFunctor_map_fst {I J : GradedObject ι C} (a : I ⟶ J) (i : ι) :
    ((endpointCofreeFunctor C c).map a).f i ≫
        endpointCofreeProjection (c := c) J i =
      endpointCofreeProjection (c := c) I i ≫ a i :=
  endpointCofreeMap_fst (c := c) a i

/-- Forgetting a complex's differential preserves monomorphisms: cancellation
holds degreewise in the underlying graded family. -/
instance forget_preservesMonomorphisms : (forget C c).PreservesMonomorphisms where
  preserves f hf := by
    letI : Mono f := hf
    refine ⟨fun {Z} g h hgh => ?_⟩
    funext i
    exact (cancel_mono (f.f i)).1 (congrFun hgh i)

/-- The endpoint cofree right adjoint preserves injective graded objects, since
its forgetful left adjoint preserves monomorphisms. -/
instance endpointCofreeFunctor_preservesInjectiveObjects :
    (endpointCofreeFunctor C c).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (endpointCofreeAdjunction C c)

end HomologicalComplex
