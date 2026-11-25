/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Data
import MathlibExt.CategoryTheory.MorphismProperty.IndexEquivalence

/-!
# Original free diagrams under an index equivalence

The same supplied base generation data provides the Hom coproducts on both
original diagram categories. The comparison at an actual representative
reindexes these coproducts with the original fully faithful inverse Hom
equivalence. Every insertion, index action, coefficient map, chosen
adjunction unit and counit remains part of the comparison.
-/

set_option autoImplicit false
noncomputable section
universe w uD vD uS vS uM vM
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.FunctorProjective.IndexEquivalence

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- The actual inverse functor gives the complete original representative Hom equivalence. -/
def homIndexEquiv (e : D ≌ S) (s t : S) :
    (e.inverse.obj s ⟶ e.inverse.obj t) ≃ (s ⟶ t) :=
  (e.fullyFaithfulInverse.homEquiv (X := s) (Y := t)).symm

/-- The entire forward Hom function retains both original counit components. -/
theorem homIndexEquiv_forward_function (e : D ≌ S) :
    (fun (s t : S) (f : e.inverse.obj s ⟶ e.inverse.obj t) => homIndexEquiv e s t f) =
      fun (s t : S) (f : e.inverse.obj s ⟶ e.inverse.obj t) =>
        e.counitInv.app s ≫ e.functor.map f ≫ e.counit.app t := rfl

/-- The entire inverse Hom function is the map of the same original inverse functor. -/
theorem homIndexEquiv_inverse_function (e : D ≌ S) :
    (fun (s t : S) (f : s ⟶ t) => (homIndexEquiv e s t).symm f) =
      fun (s t : S) (f : s ⟶ t) => e.inverse.map f := rfl

/-- The actual Hom preimage is sent back to the complete original morphism. -/
theorem homIndexEquiv_map (e : D ≌ S) (s t : S)
    (f : e.inverse.obj s ⟶ e.inverse.obj t) :
    e.inverse.map (homIndexEquiv e s t f) = f :=
  e.fullyFaithfulInverse.map_preimage f

/-- Reindexing retains the genuine identity insertion at every original representative. -/
theorem homIndexEquiv_id (e : D ≌ S) (s : S) :
    homIndexEquiv e s s (𝟙 (e.inverse.obj s)) = 𝟙 s := by
  apply e.inverse.map_injective
  exact (homIndexEquiv_map e s s _).trans (e.inverse.map_id s).symm

/-- The complete Hom reindexing commutes with every actual target-index action. -/
theorem homIndexEquiv_comp (e : D ≌ S) {s t z : S}
    (f : e.inverse.obj s ⟶ e.inverse.obj t) (g : t ⟶ z) :
    homIndexEquiv e s z (f ≫ e.inverse.map g) = homIndexEquiv e s t f ≫ g := by
  apply e.inverse.map_injective
  calc
    e.inverse.map (homIndexEquiv e s z (f ≫ e.inverse.map g)) =
        f ≫ e.inverse.map g := homIndexEquiv_map e s z _
    _ = e.inverse.map (homIndexEquiv e s t f) ≫ e.inverse.map g := by
      rw [homIndexEquiv_map]
    _ = e.inverse.map (homIndexEquiv e s t f ≫ g) :=
      (e.inverse.map_comp _ _).symm

variable [LocallySmall.{w} S]

/-- The original free diagram insertion is labelled by the actual original Hom. -/
def sourceInsertion (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s t : S) (A : M) (f : e.inverse.obj s ⟶ e.inverse.obj t) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    A ⟶ ((freeFunctor (D := D) d (e.inverse.obj s)).obj A).obj (e.inverse.obj t) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  letI : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact Sigma.ι (fun _ : e.inverse.obj s ⟶ e.inverse.obj t => A) f

/-- The target free diagram insertion retains the actual target Hom label. -/
def targetInsertion (d : CofibrantGenerationData M κ) (s t : S) (A : M) (f : s ⟶ t) :
    A ⟶ ((freeFunctor (D := S) d s).obj A).obj t := by
  letI : ∀ x y : S, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact Sigma.ι (fun _ : s ⟶ t => A) f

/-- The full original free component is compared by the existing actual coproduct reindexing. -/
def componentIso (e : D ≌ S) (d : CofibrantGenerationData M κ) (s t : S) (A : M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((freeFunctor (D := D) d (e.inverse.obj s)).obj A).obj (e.inverse.obj t) ≅
      ((freeFunctor (D := S) d s).obj A).obj t := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  letI : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  letI : ∀ x y : S, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact Sigma.reindex (homIndexEquiv e s t) (fun _ : s ⟶ t => A)

/-- Every original insertion survives the forward coproduct comparison. -/
theorem componentIso_insertion_hom (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s t : S) (A : M) (f : e.inverse.obj s ⟶ e.inverse.obj t) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    sourceInsertion e d s t A f ≫ (componentIso e d s t A).hom =
      targetInsertion d s t A (homIndexEquiv e s t f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  let _ : ∀ x y : S, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact Sigma.ι_reindex_hom (homIndexEquiv e s t) (fun _ : s ⟶ t => A) f

/-- Every original insertion also survives the inverse coproduct comparison. -/
theorem componentIso_insertion_inv (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s t : S) (A : M) (f : s ⟶ t) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    targetInsertion d s t A f ≫ (componentIso e d s t A).inv =
      sourceInsertion e d s t A (e.inverse.map f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  have h := componentIso_insertion_hom e d s t A (e.inverse.map f)
  have hIndex : homIndexEquiv e s t (e.inverse.map f) = f :=
    e.fullyFaithfulInverse.preimage_map f
  rw [hIndex] at h
  exact (Iso.comp_inv_eq (componentIso e d s t A)).mpr h.symm

/-- The original source coefficient map acts on every original insertion. -/
theorem sourceInsertion_coefficient (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s t : S) {A B : M} (f : A ⟶ B) (h : e.inverse.obj s ⟶ e.inverse.obj t) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    sourceInsertion e d s t A h ≫
        ((freeFunctor (D := D) d (e.inverse.obj s)).map f).app (e.inverse.obj t) =
      f ≫ sourceInsertion e d s t B h := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  simp only [sourceInsertion, freeFunctor, evaluationLeftAdjoint,
    colimit.ι_desc, Cofan.mk_ι_app]

/-- The target coefficient map acts on every actual target insertion. -/
theorem targetInsertion_coefficient (d : CofibrantGenerationData M κ)
    (s t : S) {A B : M} (f : A ⟶ B) (h : s ⟶ t) :
    targetInsertion d s t A h ≫ ((freeFunctor (D := S) d s).map f).app t =
      f ≫ targetInsertion d s t B h := by
  let _ : ∀ x y : S, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  simp only [targetInsertion, freeFunctor, evaluationLeftAdjoint,
    colimit.ι_desc, Cofan.mk_ι_app]

/-- The source diagram action retains composition of actual original Hom labels. -/
theorem sourceInsertion_index (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s : S) {t z : S} (A : M) (h : e.inverse.obj s ⟶ e.inverse.obj t) (g : t ⟶ z) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    sourceInsertion e d s t A h ≫
        ((freeFunctor (D := D) d (e.inverse.obj s)).obj A).map (e.inverse.map g) =
      sourceInsertion e d s z A (h ≫ e.inverse.map g) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  simp only [sourceInsertion, freeFunctor, evaluationLeftAdjoint,
    colimit.ι_desc, Cofan.mk_ι_app]

/-- The target diagram action retains composition of every actual target Hom label. -/
theorem targetInsertion_index (d : CofibrantGenerationData M κ)
    (s : S) {t z : S} (A : M) (h : s ⟶ t) (g : t ⟶ z) :
    targetInsertion d s t A h ≫ ((freeFunctor (D := S) d s).obj A).map g =
      targetInsertion d s z A (h ≫ g) := by
  let _ : ∀ x y : S, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  simp only [targetInsertion, freeFunctor, evaluationLeftAdjoint,
    colimit.ι_desc, Cofan.mk_ι_app]

/-- The actual component comparison commutes with every original index action. -/
theorem componentIso_index_naturality (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s : S) {t z : S} (A : M) (g : t ⟶ z) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((freeFunctor (D := D) d (e.inverse.obj s)).obj A).map (e.inverse.map g) ≫
        (componentIso e d s z A).hom =
      (componentIso e d s t A).hom ≫ ((freeFunctor (D := S) d s).obj A).map g := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  let _ : ∀ x y : S, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  apply Sigma.hom_ext
  intro h
  change sourceInsertion e d s t A h ≫ _ = sourceInsertion e d s t A h ≫ _
  calc
    sourceInsertion e d s t A h ≫
        (((freeFunctor (D := D) d (e.inverse.obj s)).obj A).map (e.inverse.map g) ≫
          (componentIso e d s z A).hom) =
        (sourceInsertion e d s t A h ≫
          ((freeFunctor (D := D) d (e.inverse.obj s)).obj A).map (e.inverse.map g)) ≫
            (componentIso e d s z A).hom := (Category.assoc _ _ _).symm
    _ = sourceInsertion e d s z A (h ≫ e.inverse.map g) ≫
        (componentIso e d s z A).hom := by rw [sourceInsertion_index]
    _ = targetInsertion d s z A (homIndexEquiv e s z (h ≫ e.inverse.map g)) :=
      componentIso_insertion_hom e d s z A _
    _ = targetInsertion d s z A (homIndexEquiv e s t h ≫ g) := by rw [homIndexEquiv_comp]
    _ = targetInsertion d s t A (homIndexEquiv e s t h) ≫
        ((freeFunctor (D := S) d s).obj A).map g :=
      (targetInsertion_index d s A _ g).symm
    _ = (sourceInsertion e d s t A h ≫ (componentIso e d s t A).hom) ≫
        ((freeFunctor (D := S) d s).obj A).map g := by rw [componentIso_insertion_hom]
    _ = sourceInsertion e d s t A h ≫
        ((componentIso e d s t A).hom ≫ ((freeFunctor (D := S) d s).obj A).map g) :=
      Category.assoc _ _ _

/-- The component comparison retains both actual free coefficient maps. -/
theorem componentIso_coefficient_naturality (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s t : S) {A B : M} (f : A ⟶ B) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((freeFunctor (D := D) d (e.inverse.obj s)).map f).app (e.inverse.obj t) ≫
        (componentIso e d s t B).hom =
      (componentIso e d s t A).hom ≫ ((freeFunctor (D := S) d s).map f).app t := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  let _ : ∀ x y : S, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  apply Sigma.hom_ext
  intro h
  change sourceInsertion e d s t A h ≫ _ = sourceInsertion e d s t A h ≫ _
  calc
    sourceInsertion e d s t A h ≫
        (((freeFunctor (D := D) d (e.inverse.obj s)).map f).app (e.inverse.obj t) ≫
          (componentIso e d s t B).hom) =
        (sourceInsertion e d s t A h ≫
          ((freeFunctor (D := D) d (e.inverse.obj s)).map f).app (e.inverse.obj t)) ≫
            (componentIso e d s t B).hom := (Category.assoc _ _ _).symm
    _ = (f ≫ sourceInsertion e d s t B h) ≫ (componentIso e d s t B).hom := by
      rw [sourceInsertion_coefficient]
    _ = f ≫ targetInsertion d s t B (homIndexEquiv e s t h) := by
      rw [Category.assoc, componentIso_insertion_hom]
    _ = targetInsertion d s t A (homIndexEquiv e s t h) ≫
        ((freeFunctor (D := S) d s).map f).app t :=
      (targetInsertion_coefficient d s t f _).symm
    _ = (sourceInsertion e d s t A h ≫ (componentIso e d s t A).hom) ≫
        ((freeFunctor (D := S) d s).map f).app t := by rw [componentIso_insertion_hom]
    _ = sourceInsertion e d s t A h ≫
        ((componentIso e d s t A).hom ≫ ((freeFunctor (D := S) d s).map f).app t) :=
      Category.assoc _ _ _

/-- The actual Hom-coproduct components give the comparison of entire original free diagrams. -/
def freeObjectIso (e : D ≌ S) (d : CofibrantGenerationData M κ) (s : S) (A : M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    e.inverse ⋙ (freeFunctor (D := D) d (e.inverse.obj s)).obj A ≅
      (freeFunctor (D := S) d s).obj A := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact NatIso.ofComponents (fun t => componentIso e d s t A)
    (fun {_ _} g => componentIso_index_naturality e d s A g)

/-- The same actual components compare the whole original free coefficient functors. -/
def freeIso (e : D ≌ S) (d : CofibrantGenerationData M κ) (s : S) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    freeFunctor (D := D) d (e.inverse.obj s) ⋙ (e.congrLeft (E := M)).functor ≅
      freeFunctor (D := S) d s := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact NatIso.ofComponents (fun A => freeObjectIso e d s A) (fun {_ _} f => by
    ext t
    exact componentIso_coefficient_naturality e d s t f)

/-- The whole forward component function retains the original coproduct comparison. -/
theorem freeIso_hom_component_function (e : D ≌ S) (d : CofibrantGenerationData M κ) (s : S) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (A : M) (t : S) => ((freeIso e d s).hom.app A).app t) =
      fun (A : M) (t : S) => (componentIso e d s t A).hom := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The whole inverse component function retains the same original coproduct inverse. -/
theorem freeIso_inv_component_function (e : D ≌ S) (d : CofibrantGenerationData M κ) (s : S) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (A : M) (t : S) => ((freeIso e d s).inv.app A).app t) =
      fun (A : M) (t : S) => (componentIso e d s t A).inv := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The entire original source unit is the insertion of the original identity Hom. -/
theorem sourceUnit_insertion (e : D ≌ S) (d : CofibrantGenerationData M κ) (s : S) (A : M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).unit.app A =
      sourceInsertion e d s s A (𝟙 (e.inverse.obj s)) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact evaluationAdjunctionRight_unit_app M (e.inverse.obj s) A

/-- The entire target unit is the insertion of the actual target identity Hom. -/
theorem targetUnit_insertion (d : CofibrantGenerationData M κ) (s : S) (A : M) :
    (freeEvaluationAdjunction (D := S) d s).unit.app A =
      targetInsertion d s s A (𝟙 s) := by
  let _ : ∀ x y : S, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact evaluationAdjunctionRight_unit_app M s A

/-- The forward comparison preserves the chosen units with both actual evaluation getters. -/
theorem freeIso_unit (e : D ≌ S) (d : CofibrantGenerationData M κ) (s : S) (A : M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).unit.app A ≫
        ((freeIso e d s).hom.app A).app s =
      (freeEvaluationAdjunction (D := S) d s).unit.app A := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  calc
    (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).unit.app A ≫
        ((freeIso e d s).hom.app A).app s =
        sourceInsertion e d s s A (𝟙 (e.inverse.obj s)) ≫
          (componentIso e d s s A).hom :=
      congrArg₂ (fun f g => f ≫ g) (sourceUnit_insertion e d s A)
        (congrFun (congrFun (freeIso_hom_component_function e d s) A) s)
    _ = targetInsertion d s s A (homIndexEquiv e s s (𝟙 (e.inverse.obj s))) :=
      componentIso_insertion_hom e d s s A _
    _ = targetInsertion d s s A (𝟙 s) :=
      congrArg (targetInsertion d s s A) (homIndexEquiv_id e s)
    _ = (freeEvaluationAdjunction (D := S) d s).unit.app A :=
      (targetUnit_insertion d s A).symm

/-- The inverse comparison recovers the same original chosen source unit. -/
theorem freeIso_unit_inv (e : D ≌ S) (d : CofibrantGenerationData M κ) (s : S) (A : M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeEvaluationAdjunction (D := S) d s).unit.app A ≫
        ((freeIso e d s).inv.app A).app s =
      (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).unit.app A := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  have h : (freeEvaluationAdjunction (D := S) d s).unit.app A =
      (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).unit.app A ≫
        (componentIso e d s s A).hom :=
    (freeIso_unit e d s A).symm.trans
      (congrArg
        (fun f => (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).unit.app A ≫ f)
        (congrFun (congrFun (freeIso_hom_component_function e d s) A) s))
  exact (congrArg
    (fun f => (freeEvaluationAdjunction (D := S) d s).unit.app A ≫ f)
    (congrFun (congrFun (freeIso_inv_component_function e d s) A) s)).trans
      ((Iso.comp_inv_eq (componentIso e d s s A)).mpr h)

/-- The original counit evaluates every actual source Hom insertion. -/
theorem sourceCounit_insertion (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s t : S) (X : D ⥤ M) (h : e.inverse.obj s ⟶ e.inverse.obj t) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    sourceInsertion e d s t (X.obj (e.inverse.obj s)) h ≫
        ((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).counit.app X).app
          (e.inverse.obj t) = X.map h := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  simp only [sourceInsertion, freeEvaluationAdjunction,
    evaluationAdjunctionRight_counit_app_app, Functor.id_obj]
  change Sigma.ι (fun _ : e.inverse.obj s ⟶ e.inverse.obj t => X.obj (e.inverse.obj s)) h ≫
      Sigma.desc (f := fun _ : e.inverse.obj s ⟶ e.inverse.obj t => X.obj (e.inverse.obj s))
        (fun h : e.inverse.obj s ⟶ e.inverse.obj t => X.map h) = X.map h
  exact Sigma.ι_comp_desc
    (f := fun _ : e.inverse.obj s ⟶ e.inverse.obj t => X.obj (e.inverse.obj s))
    (fun h : e.inverse.obj s ⟶ e.inverse.obj t => X.map h) h

/-- The target counit evaluates every original target Hom insertion. -/
theorem targetCounit_insertion (d : CofibrantGenerationData M κ)
    (s t : S) (X : S ⥤ M) (h : s ⟶ t) :
    targetInsertion d s t (X.obj s) h ≫
        ((freeEvaluationAdjunction (D := S) d s).counit.app X).app t = X.map h := by
  let _ : ∀ x y : S, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  simp only [targetInsertion, freeEvaluationAdjunction,
    evaluationAdjunctionRight_counit_app_app, Functor.id_obj]
  change Sigma.ι (fun _ : s ⟶ t => X.obj s) h ≫
      Sigma.desc (f := fun _ : s ⟶ t => X.obj s) (fun h : s ⟶ t => X.map h) = X.map h
  exact Sigma.ι_comp_desc (f := fun _ : s ⟶ t => X.obj s) (fun h : s ⟶ t => X.map h) h

/-- The whole forward comparison retains the same original counits at every diagram. -/
theorem freeIso_counit (e : D ≌ S) (d : CofibrantGenerationData M κ) (s : S) (X : D ⥤ M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeIso e d s).hom.app (X.obj (e.inverse.obj s)) ≫
        (freeEvaluationAdjunction (D := S) d s).counit.app (e.inverse ⋙ X) =
      (e.congrLeft (E := M)).functor.map
        ((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).counit.app X) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  let _ : ∀ x y : S, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  ext t
  apply Sigma.hom_ext
  intro h
  change sourceInsertion e d s t (X.obj (e.inverse.obj s)) h ≫
      (((freeIso e d s).hom.app (X.obj (e.inverse.obj s))).app t ≫
        ((freeEvaluationAdjunction (D := S) d s).counit.app (e.inverse ⋙ X)).app t) =
    sourceInsertion e d s t (X.obj (e.inverse.obj s)) h ≫
      ((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).counit.app X).app
        (e.inverse.obj t)
  rw [← Category.assoc,
    congrFun (congrFun (freeIso_hom_component_function e d s) _) t,
    componentIso_insertion_hom e d s t (X.obj (e.inverse.obj s)) h]
  exact (targetCounit_insertion d s t (e.inverse ⋙ X) (homIndexEquiv e s t h)).trans
    ((congrArg (fun f => X.map f) (homIndexEquiv_map e s t h)).trans
      (sourceCounit_insertion e d s t X h).symm)

/-- The whole inverse comparison retains the same original target counit. -/
theorem freeIso_counit_inv (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s : S) (X : D ⥤ M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeIso e d s).inv.app (X.obj (e.inverse.obj s)) ≫
        (e.congrLeft (E := M)).functor.map
          ((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).counit.app X) =
      (freeEvaluationAdjunction (D := S) d s).counit.app (e.inverse ⋙ X) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rw [← freeIso_counit e d s X]
  exact Iso.inv_hom_id_assoc ((freeIso e d s).app (X.obj (e.inverse.obj s))) _

/-- Every original source Hom has the same scalar adjunct after the actual free comparison. -/
theorem freeIso_homEquiv (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s : S) (A : M) (X : D ⥤ M)
    (f : letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor;
      (freeFunctor (D := D) d (e.inverse.obj s)).obj A ⟶ X) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeEvaluationAdjunction (D := S) d s).homEquiv A (e.inverse ⋙ X)
        ((freeIso e d s).inv.app A ≫ (e.congrLeft (E := M)).functor.map f) =
      (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).homEquiv A X f := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (freeEvaluationAdjunction (D := S) d s).unit.app A ≫
      (((freeIso e d s).inv.app A).app s ≫ f.app (e.inverse.obj s)) =
    (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).unit.app A ≫
      f.app (e.inverse.obj s)
  rw [← Category.assoc, freeIso_unit_inv]

/-- Every original inverse Hom retains the same coefficient map and original counit. -/
theorem freeIso_homEquiv_symm (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s : S) (A : M) (X : D ⥤ M) (f : A ⟶ X.obj (e.inverse.obj s)) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeIso e d s).hom.app A ≫
        ((freeEvaluationAdjunction (D := S) d s).homEquiv A (e.inverse ⋙ X)).symm f =
      (e.congrLeft (E := M)).functor.map
        (((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).homEquiv A X).symm f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  calc
    (freeIso e d s).hom.app A ≫
        ((freeFunctor (D := S) d s).map f ≫
          (freeEvaluationAdjunction (D := S) d s).counit.app (e.inverse ⋙ X)) =
        ((e.congrLeft (E := M)).functor.map
            ((freeFunctor (D := D) d (e.inverse.obj s)).map f) ≫
          (freeIso e d s).hom.app (X.obj (e.inverse.obj s))) ≫
            (freeEvaluationAdjunction (D := S) d s).counit.app (e.inverse ⋙ X) := by
      have hn : (e.congrLeft (E := M)).functor.map
            ((freeFunctor (D := D) d (e.inverse.obj s)).map f) ≫
          (freeIso e d s).hom.app (X.obj (e.inverse.obj s)) =
          (freeIso e d s).hom.app A ≫ (freeFunctor (D := S) d s).map f := by
        simpa only [Functor.comp_map] using (freeIso e d s).hom.naturality f
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun h => h ≫
          (freeEvaluationAdjunction (D := S) d s).counit.app (e.inverse ⋙ X)) hn.symm)
    _ = (e.congrLeft (E := M)).functor.map
          ((freeFunctor (D := D) d (e.inverse.obj s)).map f) ≫
        (e.congrLeft (E := M)).functor.map
          ((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).counit.app X) := by
      rw [Category.assoc, freeIso_counit]
    _ = (e.congrLeft (E := M)).functor.map
        ((freeFunctor (D := D) d (e.inverse.obj s)).map f ≫
          (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).counit.app X) :=
      ((e.congrLeft (E := M)).functor.map_comp _ _).symm

/-- The entire forward unit family keeps every original representative and coefficient. -/
theorem freeIso_unit_function (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (s : S) (A : M) =>
      (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).unit.app A ≫
        ((freeIso e d s).hom.app A).app s) =
      fun (s : S) (A : M) => (freeEvaluationAdjunction (D := S) d s).unit.app A := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  funext s A
  exact freeIso_unit e d s A

/-- The entire inverse unit family retains the same original chosen source units. -/
theorem freeIso_unit_inv_function (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (s : S) (A : M) =>
      (freeEvaluationAdjunction (D := S) d s).unit.app A ≫
        ((freeIso e d s).inv.app A).app s) =
      fun (s : S) (A : M) =>
        (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).unit.app A := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  funext s A
  exact freeIso_unit_inv e d s A

/-- The complete forward counit function retains every original source diagram. -/
theorem freeIso_counit_function (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (s : S) (X : D ⥤ M) =>
      (freeIso e d s).hom.app (X.obj (e.inverse.obj s)) ≫
        (freeEvaluationAdjunction (D := S) d s).counit.app (e.inverse ⋙ X)) =
      fun (s : S) (X : D ⥤ M) =>
        (e.congrLeft (E := M)).functor.map
          ((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).counit.app X) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  funext s X
  exact freeIso_counit e d s X

/-- The complete inverse counit function retains every original target counit. -/
theorem freeIso_counit_inv_function (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (s : S) (X : D ⥤ M) =>
      (freeIso e d s).inv.app (X.obj (e.inverse.obj s)) ≫
        (e.congrLeft (E := M)).functor.map
          ((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).counit.app X)) =
      fun (s : S) (X : D ⥤ M) =>
        (freeEvaluationAdjunction (D := S) d s).counit.app (e.inverse ⋙ X) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  funext s X
  exact freeIso_counit_inv e d s X

/-- The whole forward scalar Hom function is checked before any original arrow is applied. -/
theorem freeIso_homEquiv_function (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (s : S) (A : M) (X : D ⥤ M)
      (f : letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor;
      (freeFunctor (D := D) d (e.inverse.obj s)).obj A ⟶ X) =>
      (freeEvaluationAdjunction (D := S) d s).homEquiv A (e.inverse ⋙ X)
        ((freeIso e d s).inv.app A ≫ (e.congrLeft (E := M)).functor.map f)) =
      fun (s : S) (A : M) (X : D ⥤ M)
        (f : letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor;
      (freeFunctor (D := D) d (e.inverse.obj s)).obj A ⟶ X) =>
        (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).homEquiv A X f := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  funext s A X f
  exact freeIso_homEquiv e d s A X f

/-- The whole inverse scalar Hom function retains every original coefficient domain. -/
theorem freeIso_homEquiv_symm_function (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (s : S) (A : M) (X : D ⥤ M) (f : A ⟶ X.obj (e.inverse.obj s)) =>
      (freeIso e d s).hom.app A ≫
        ((freeEvaluationAdjunction (D := S) d s).homEquiv A (e.inverse ⋙ X)).symm f) =
      fun (s : S) (A : M) (X : D ⥤ M) (f : A ⟶ X.obj (e.inverse.obj s)) =>
        (e.congrLeft (E := M)).functor.map
          (((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).homEquiv A X).symm f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  funext s A X f
  exact freeIso_homEquiv_symm e d s A X f

/-- The actual Arrow functor compares the entire original free-image arrow families. -/
def freeArrowComparison (e : D ≌ S) (d : CofibrantGenerationData M κ) (s : S) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeFunctor (D := D) d (e.inverse.obj s) ⋙
        (e.congrLeft (E := M)).functor).mapArrow ≅
      (freeFunctor (D := S) d s).mapArrow := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact (Functor.mapArrowFunctor M (S ⥤ M)).mapIso (freeIso e d s)

/-- The entire Arrow comparison retains all four original endpoint diagram maps. -/
theorem freeArrowComparison_fields (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s : S) (f : Arrow M) (t : S) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((freeArrowComparison e d s).hom.app f).left.app t =
        (componentIso e d s t f.left).hom ∧
      ((freeArrowComparison e d s).hom.app f).right.app t =
        (componentIso e d s t f.right).hom ∧
      ((freeArrowComparison e d s).inv.app f).left.app t =
        (componentIso e d s t f.left).inv ∧
      ((freeArrowComparison e d s).inv.app f).right.app t =
        (componentIso e d s t f.right).inv := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every original Arrow square retains the forward free-comparison naturality equation. -/
theorem freeArrowComparison_naturality (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s : S) {f g : Arrow M} (a : f ⟶ g) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeFunctor (D := D) d (e.inverse.obj s) ⋙
        (e.congrLeft (E := M)).functor).mapArrow.map a ≫
        (freeArrowComparison e d s).hom.app g =
      (freeArrowComparison e d s).hom.app f ≫
        (freeFunctor (D := S) d s).mapArrow.map a := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact (freeArrowComparison e d s).hom.naturality a

/-- Every original Arrow square retains the inverse free-comparison naturality equation. -/
theorem freeArrowComparison_inv_naturality (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (s : S) {f g : Arrow M} (a : f ⟶ g) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeFunctor (D := S) d s).mapArrow.map a ≫
        (freeArrowComparison e d s).inv.app g =
      (freeArrowComparison e d s).inv.app f ≫
        (freeFunctor (D := D) d (e.inverse.obj s) ⋙
          (e.congrLeft (E := M)).functor).mapArrow.map a := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact (freeArrowComparison e d s).inv.naturality a

end HomotopicalAlgebra.FunctorProjective.IndexEquivalence
