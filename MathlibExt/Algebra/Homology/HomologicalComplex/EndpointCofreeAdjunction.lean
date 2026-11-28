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
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# The adjunction for endpoint cofree complexes

Let C have zero morphisms, a zero object and binary biproducts, and let c be a
complex shape on an arbitrary index type ι. Forgetting the differential is left
adjoint to the cofree functor on GradedObject ι C. Its value on I has terms
Iᵢ ⊞ Eᵢ, where Eᵢ is I(c.next i) along an outgoing edge and zero otherwise.

The adjunction identifies coefficient families Kᵢ → Iᵢ with complex maps
K → D(I). The unit has identity first coefficients and the outgoing source
differentials as second coefficients. The counit consists of first projections.
The forgetful functor is faithful, so the unit is a monomorphism.

If C also has finite limits, forgetting differentials preserves monomorphisms,
and the cofree right adjoint preserves injective objects. The index and both
category universes are independent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w

variable (C : Type u) [Category.{v} C]
  [HasZeroMorphisms C] [HasZeroObject C] [HasBinaryBiproducts C]
  {ι : Type w} (c : ComplexShape ι)

/-- The functor from coefficient families to c-shaped cofree complexes. A family
map aᵢ : Iᵢ → Jᵢ induces the complex map whose first coefficient is aᵢ. -/
def endpointCofreeFunctor : GradedObject ι C ⥤ HomologicalComplex C c where
  obj I := endpointCofree c I
  map a := endpointCofreeMap c a
  map_id I := endpointCofreeMap_id c I
  map_comp a b := (endpointCofreeMap_comp c a b).symm

/-- The adjunction identifying maps of graded families K.X → I with complex
maps K → D(I), by taking or prescribing their first coefficients. -/
def endpointCofreeAdjunction : forget C c ⊣ endpointCofreeFunctor C c :=
  Adjunction.mkOfHomEquiv
    { homEquiv K I := (endpointCofreeHomEquiv K I).symm
      homEquiv_naturality_left_symm := by
        intro K' K I f g
        funext i
        change (f.f i ≫ g.f i) ≫ endpointCofreeProjection c I i =
          f.f i ≫ (g.f i ≫ endpointCofreeProjection c I i)
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

/-- The adjunction correspondence sends a coefficient family aᵢ : Kᵢ → Iᵢ
to the cofree complex map with these first coefficients. -/
theorem endpointCofreeAdjunction_homEquiv (K : HomologicalComplex C c)
    (I : GradedObject ι C) :
    (endpointCofreeAdjunction C c).homEquiv K I = (endpointCofreeHomEquiv K I).symm := by
  unfold endpointCofreeAdjunction
  exact congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) K) I

/-- The image of a coefficient family under the adjunction is the complex map
whose first components are that family. -/
@[simp]
theorem endpointCofreeAdjunction_homEquiv_apply (K : HomologicalComplex C c)
    (I : GradedObject ι C) (a : (forget C c).obj K ⟶ I) :
    (endpointCofreeAdjunction C c).homEquiv K I a = endpointCofreeHom K I a :=
  congrArg
    (fun e : ((forget C c).obj K ⟶ I) ≃ (K ⟶ (endpointCofreeFunctor C c).obj I) => e a)
    (endpointCofreeAdjunction_homEquiv C c K I)

/-- The inverse adjunction correspondence takes the first projection of a
complex morphism in every degree. -/
@[simp]
theorem endpointCofreeAdjunction_homEquiv_symm_apply (K : HomologicalComplex C c)
    (I : GradedObject ι C) (f : K ⟶ (endpointCofreeFunctor C c).obj I) :
    ((endpointCofreeAdjunction C c).homEquiv K I).symm f =
      fun i => f.f i ≫ endpointCofreeProjection c I i :=
  congrArg
    (fun e : ((forget C c).obj K ⟶ I) ≃ (K ⟶ (endpointCofreeFunctor C c).obj I) => e.symm f)
    (endpointCofreeAdjunction_homEquiv C c K I)

/-- The adjunction unit sends K to D(K.X), with identity first coefficients
and K's differentials as outgoing second coefficients. -/
abbrev endpointCofreeUnit :
    𝟭 (HomologicalComplex C c) ⟶ forget C c ⋙ endpointCofreeFunctor C c :=
  (endpointCofreeAdjunction C c).unit

/-- The adjunction counit in degree i is the first projection
D(I)ᵢ = Iᵢ ⊞ Eᵢ → Iᵢ. -/
abbrev endpointCofreeCounit :
    endpointCofreeFunctor C c ⋙ forget C c ⟶ 𝟭 (GradedObject ι C) :=
  (endpointCofreeAdjunction C c).counit

/-- The unit component at K is the cofree map with identity first coefficients. -/
@[simp]
theorem endpointCofreeUnit_app (K : HomologicalComplex C c) :
    (endpointCofreeUnit C c).app K =
      endpointCofreeHom K K.X (fun i => 𝟙 (K.X i)) := by
  have h := (endpointCofreeAdjunction C c).homEquiv_id K
  rw [endpointCofreeAdjunction_homEquiv_apply] at h
  dsimp only [forget, GradedObject.categoryOfGradedObjects, CategoryTheory.pi] at h
  exact h.symm

/-- The first coefficient of the unit is the identity in every degree. -/
@[reassoc (attr := simp)]
theorem endpointCofreeUnit_fst (K : HomologicalComplex C c) (i : ι) :
    ((endpointCofreeUnit C c).app K).f i ≫
        endpointCofreeProjection c K.X i = 𝟙 (K.X i) := by
  rw [endpointCofreeUnit_app]
  exact endpointCofreeHom_fst K K.X (fun i => 𝟙 (K.X i)) i

/-- Along an outgoing edge, the second coefficient of the unit, identified with
the next source term, is the source differential. -/
@[reassoc]
theorem endpointCofreeUnit_snd_of_rel (K : HomologicalComplex C c)
    {i j : ι} (hij : c.Rel i j) :
    (((endpointCofreeUnit C c).app K).f i ≫
        endpointCofreeSecondProjection c K.X i) ≫
        (endpointCofreeNextTermIso K.X hij).hom = K.d i j := by
  rw [endpointCofreeUnit_app]
  exact (endpointCofreeHom_snd_of_rel K K.X (fun i => 𝟙 (K.X i)) hij).trans
    (Category.comp_id _)

/-- At an index without an outgoing edge, the second coefficient of the unit is
the zero morphism to the optional zero term. -/
@[reassoc]
theorem endpointCofreeUnit_snd_of_no_next (K : HomologicalComplex C c) (i : ι)
    (hi : ¬ c.Rel i (c.next i)) :
    ((endpointCofreeUnit C c).app K).f i ≫
        endpointCofreeSecondProjection c K.X i = 0 :=
  (endpointCofreeNextTerm_isZero K.X i hi).eq_of_tgt _ _

/-- The cofree unit is a monomorphism because its forgetful left adjoint is faithful. -/
theorem endpointCofreeUnit_mono (K : HomologicalComplex C c) :
    Mono ((endpointCofreeUnit C c).app K) :=
  Adjunction.unit_mono_of_L_faithful (endpointCofreeAdjunction C c) K

/-- The counit in degree i is the first projection from the cofree term to its
coefficient object Iᵢ. -/
@[simp]
theorem endpointCofreeCounit_app (I : GradedObject ι C) (i : ι) :
    ((endpointCofreeCounit C c).app I) i = endpointCofreeProjection c I i := by
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
        endpointCofreeProjection c J i =
      endpointCofreeProjection c I i ≫ a i :=
  endpointCofreeMap_fst c a i

variable [HasFiniteLimits C]

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
