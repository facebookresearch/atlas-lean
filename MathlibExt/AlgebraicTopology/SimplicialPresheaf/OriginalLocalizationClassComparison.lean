/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Full original-family local-class comparison on the unchanged presheaf category.
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalSmithModel
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# Localizing families with the same local fibrant objects

On a working-small, locally small site, two localizing families with the same local fibrant
objects have the same weak-equivalence class on all simplicial-presheaf arrows. When both
families are working-small, their chosen localized models have equal cofibration,
weak-equivalence and global fibration classes, and the identity adjunction is a Quillen
equivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i j
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan
variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} {J : Type j}

/-- Literal all-original-arrow weak classes agree from the proved all-object locality
equivalence. -/
theorem originalLocalEquivalences_eq_of_localFibrant_iff
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (T : J → Arrow (SimplicialPresheaf.{u} D))
    (hLocal : ∀ Z, isOriginalLocalFibrant S Z ↔ isOriginalLocalFibrant T Z) :
    originalLocalEquivalences S = originalLocalEquivalences T := by
  ext A B f
  change (∀ Z, isOriginalLocalFibrant S Z →
    SSet.realizationWeakEquivalences (innerHomPre f Z)) ↔
      ∀ Z, isOriginalLocalFibrant T Z →
        SSet.realizationWeakEquivalences (innerHomPre f Z)
  constructor
  · intro hf Z hZ
    exact hf Z ((hLocal Z).mpr hZ)
  · intro hf Z hZ
    exact hf Z ((hLocal Z).mp hZ)

/-- The SAME internally selected models have equal Cof/W/GLOBAL Fib properties. -/
theorem originalLocalModelClasses_eq_of_localFibrant_iff [Small.{u} I] [Small.{u} J]
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (T : J → Arrow (SimplicialPresheaf.{u} D))
    (hLocal : ∀ Z, isOriginalLocalFibrant S Z ↔ isOriginalLocalFibrant T Z) :
    (originalLocalSmithData S).model.categoryWithCofibrations.cofibrations =
        (originalLocalSmithData T).model.categoryWithCofibrations.cofibrations ∧
    (originalLocalSmithData S).model.categoryWithWeakEquivalences.weakEquivalences =
        (originalLocalSmithData T).model.categoryWithWeakEquivalences.weakEquivalences ∧
    (originalLocalSmithData S).model.categoryWithFibrations.fibrations =
        (originalLocalSmithData T).model.categoryWithFibrations.fibrations := by
  let ms := originalLocalSmithData S
  let mt := originalLocalSmithData T
  have hW : originalLocalEquivalences S = originalLocalEquivalences T :=
    originalLocalEquivalences_eq_of_localFibrant_iff S T hLocal
  refine ⟨ms.cofibrations_eq.trans mt.cofibrations_eq.symm,
    ms.weakEquivalences_eq.trans (hW.trans mt.weakEquivalences_eq.symm), ?_⟩
  calc
    ms.model.categoryWithFibrations.fibrations = (localTrivialMonomorphisms S).rlp :=
      ms.fibrations_eq
    _ = (localTrivialMonomorphisms T).rlp := by
      unfold localTrivialMonomorphisms
      rw [hW]
    _ = mt.model.categoryWithFibrations.fibrations := mt.fibrations_eq.symm

/-- Native identity QE uses TWO explicit original-family models, with no merged local instances. -/
theorem originalLocalIdentity_isQuillenEquivalence_of_localFibrant_iff
    [Small.{u} I] [Small.{u} J]
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (T : J → Arrow (SimplicialPresheaf.{u} D))
    (hLocal : ∀ Z, isOriginalLocalFibrant S Z ↔ isOriginalLocalFibrant T Z) :
    @CategoryTheory.Adjunction.IsQuillenEquivalence
      (SimplicialPresheaf.{u} D) inferInstance
      (SimplicialPresheaf.{u} D) inferInstance
      (originalLocalSmithModel S) (originalLocalSmithModel T)
      (Functor.id (SimplicialPresheaf.{u} D))
      (Functor.id (SimplicialPresheaf.{u} D))
      (Adjunction.id (C := SimplicialPresheaf.{u} D)) := by
  let ms := originalLocalSmithData S
  let mt := originalLocalSmithData T
  change @CategoryTheory.Adjunction.IsQuillenEquivalence
    (SimplicialPresheaf.{u} D) inferInstance
    (SimplicialPresheaf.{u} D) inferInstance
    ms.model mt.model (Functor.id _) (Functor.id _)
    (Adjunction.id (C := SimplicialPresheaf.{u} D))
  have hClasses := originalLocalModelClasses_eq_of_localFibrant_iff S T hLocal
  have hCof : ms.model.categoryWithCofibrations.cofibrations =
      mt.model.categoryWithCofibrations.cofibrations := hClasses.1
  have hW : ms.model.categoryWithWeakEquivalences.weakEquivalences =
      mt.model.categoryWithWeakEquivalences.weakEquivalences := hClasses.2.1
  refine @CategoryTheory.Adjunction.IsQuillenEquivalence.mk
    (SimplicialPresheaf.{u} D) inferInstance
    (SimplicialPresheaf.{u} D) inferInstance
    ms.model mt.model (Functor.id _) (Functor.id _)
    (Adjunction.id (C := SimplicialPresheaf.{u} D)) ?_ ?_
  · refine @CategoryTheory.Adjunction.IsQuillenAdjunction.mk
      (SimplicialPresheaf.{u} D) inferInstance
      (SimplicialPresheaf.{u} D) inferInstance
      ms.model mt.model (Functor.id _) (Functor.id _)
      (Adjunction.id (C := SimplicialPresheaf.{u} D)) ?_ ?_
    · intro A B f hf
      change ms.model.categoryWithCofibrations.cofibrations f at hf
      change mt.model.categoryWithCofibrations.cofibrations f
      rw [← hCof]
      exact hf
    · intro A B f hf
      change ms.model.categoryWithCofibrations.cofibrations f ∧
        ms.model.categoryWithWeakEquivalences.weakEquivalences f at hf
      change mt.model.categoryWithCofibrations.cofibrations f ∧
        mt.model.categoryWithWeakEquivalences.weakEquivalences f
      rw [← hCof, ← hW]
      exact hf
  · intro X Y _ _ f
    change mt.model.categoryWithWeakEquivalences.weakEquivalences f ↔
      ms.model.categoryWithWeakEquivalences.weakEquivalences
        ((Adjunction.id (C := SimplicialPresheaf.{u} D)).homEquiv X Y f)
    have hid : (Adjunction.id (C := SimplicialPresheaf.{u} D)).homEquiv X Y f = f := by
      simp [CategoryTheory.Adjunction.homEquiv]
    rw [hid, hW]

end SimplicialPresheaf.InjectiveKan
