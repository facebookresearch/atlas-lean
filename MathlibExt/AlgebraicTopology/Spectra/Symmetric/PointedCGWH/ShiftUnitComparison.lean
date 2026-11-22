/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.LabelTransformation

/-!
# The unit-index symmetric shift

The symmetric shift by the finite-set tensor unit is naturally isomorphic
to the identity functor. Its components are the actions of the index right
unitor and its inverse through the underlying ordinary functors. Compatibility
with every labelled coefficient action gives enriched transformations that
are natural in spectrum morphisms and inverse in both directions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace NativeOmegaRecovery.NativeSymmetricShiftUnit

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} J.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

open PointedCGWH.SymmetricModulePresentation

/-- The actual native shift by the original index tensor unit. -/
def unitShift : (EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) ⥤ (EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ Operad.SmallFinBijGroupoid)

/-- The whole unit shift carries each transformation by its actual shifted component. -/
theorem unitShift_map_component {E E' : (EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})} (t : E ⟶ E') (n : Operad.SmallFinBijGroupoid) :
    component ((unitShift.{u, v}).map t) (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      component t (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ (𝟙_ Operad.SmallFinBijGroupoid))) :=
  PointedCGWH.SymmetricShift.functor_map_component (𝟙_ Operad.SmallFinBijGroupoid) n t

private theorem index_surjective (x : J.{u, v}) :
    ∃ n : I, PointedCGWH.symmetricOperatorObj.{u, v} n = x := by
  rcases x with ⟨n⟩
  exact ⟨(show I from n), rfl⟩

/-- The original right-unitor action has the complete native source and target. -/
def unitorHom (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) (x : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    ((unitShift.{u, v}).obj E).toEnrichedFunctor.obj x ⟶
      E.toEnrichedFunctor.obj x :=
  ordinaryMap E (ρ_ (show Operad.SmallFinBijGroupoid from x.asIndex)).hom

/-- Its inverse is the same original index right-unitor inverse. -/
def unitorInv (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) (x : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    E.toEnrichedFunctor.obj x ⟶
      ((unitShift.{u, v}).obj E).toEnrichedFunctor.obj x :=
  ordinaryMap E (ρ_ (show Operad.SmallFinBijGroupoid from x.asIndex)).inv

/-- The original whole native transformation retains naturality of every actual index arrow. -/
theorem ordinaryMap_naturality {E E' : (EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})} (t : E ⟶ E')
    {n k : Operad.SmallFinBijGroupoid} (f : n ⟶ k) :
    component t (PointedCGWH.symmetricOperatorObj.{u, v} n) ≫ ordinaryMap E' f =
      ordinaryMap E f ≫ component t (PointedCGWH.symmetricOperatorObj.{u, v} k) := by
  let F : Operad.SmallFinBijGroupoid ⥤ V.{u, v} :=
    ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor
  let G : Operad.SmallFinBijGroupoid ⥤ V.{u, v} :=
    ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E').functor
  let τ : F ⟶ G := ((PointedCGWH.symmetricSequenceRestriction.{u, v}).map t).natTrans
  have h := NatTrans.naturality (F := F) (G := G) (X := n) (Y := k) τ f
  have hn : τ.app n = component t (PointedCGWH.symmetricOperatorObj.{u, v} n) :=
    PointedCGWH.symmetricSequenceRestriction_component t n
  have hk : τ.app k = component t (PointedCGWH.symmetricOperatorObj.{u, v} k) :=
    PointedCGWH.symmetricSequenceRestriction_component t k
  change ordinaryMap E f ≫ τ.app k = τ.app n ≫ ordinaryMap E' f at h
  rw [hn, hk] at h
  exact h.symm

/-- Every actual forward component retains the chosen original right unitor. -/
theorem unitorHom_original (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    unitorHom E (PointedCGWH.symmetricOperatorObj.{u, v} n) = ordinaryMap E (ρ_ n).hom := rfl

/-- Every actual inverse component retains its original inverse arrow. -/
theorem unitorInv_original (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    unitorInv E (PointedCGWH.symmetricOperatorObj.{u, v} n) = ordinaryMap E (ρ_ n).inv := rfl

private theorem inverse_square {C : Type*} [Category C] [MonoidalCategory C]
    (A : C) {X Y T U : C} (eN : X ≅ Y) (eK : T ≅ U)
    (f : A ⊗ X ⟶ T) (g : A ⊗ Y ⟶ U)
    (h : f ≫ eK.hom = (A ◁ eN.hom) ≫ g) :
    g ≫ eK.inv = (A ◁ eN.inv) ≫ f := by
  apply (cancel_epi (A ◁ eN.hom)).1
  have ht := congrArg (fun z => z ≫ eK.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← whiskerLeft_comp_assoc, whiskerLeft_id, Category.id_comp] using ht.symm

/-- The complete original inverse unitor action satisfies every labelled coefficient square. -/
theorem arrow_rightUnitor_inv (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})
    (a n k : Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k) :
    reconstructedArrowAction E a n k f ≫ ordinaryMap E (ρ_ k).inv =
      (PointedCGWH.sphereSequence.{u, v}.functor.obj a ◁ ordinaryMap E (ρ_ n).inv) ≫
        shiftedArrow E (𝟙_ Operad.SmallFinBijGroupoid) a n k f := by
  let F := ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor
  exact inverse_square (S.{u, v}.functor.obj a) (F.mapIso (ρ_ n)) (F.mapIso (ρ_ k))
    (shiftedArrow E (𝟙_ Operad.SmallFinBijGroupoid) a n k f) (reconstructedArrowAction E a n k f)
    (arrow_rightUnitor E a n k f)

/-- All original label squares construct the full enriched unit-shift map. -/
def hom (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    (unitShift.{u, v}).obj E ⟶ E :=
  NativeSymmetricLabelTransformation.transformation _ E (unitorHom E) (by
    intro a n k f
    rw [unitorHom_original, unitorHom_original]
    exact arrow_rightUnitor E a n k f)

/-- All original inverse squares construct the complete inverse enriched map. -/
def inv (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    E ⟶ (unitShift.{u, v}).obj E :=
  NativeSymmetricLabelTransformation.transformation E _ (unitorInv E) (by
    intro a n k f
    rw [unitorInv_original, unitorInv_original]
    exact arrow_rightUnitor_inv E a n k f)

/-- The full enriched map retains the actual original right-unitor component. -/
theorem hom_component (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    component (hom E) (PointedCGWH.symmetricOperatorObj.{u, v} n) = ordinaryMap E (ρ_ n).hom := by
  unfold hom
  rw [NativeSymmetricLabelTransformation.transformation_component, unitorHom_original]

/-- The full inverse retains the actual original inverse component. -/
theorem inv_component (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    component (inv E) (PointedCGWH.symmetricOperatorObj.{u, v} n) = ordinaryMap E (ρ_ n).inv := by
  unfold inv
  rw [NativeSymmetricLabelTransformation.transformation_component, unitorInv_original]

/-- The two chosen maps compose to the identity on the complete shifted spectrum. -/
theorem hom_inv (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    hom E ≫ inv E = 𝟙 ((unitShift.{u, v}).obj E) := by
  apply hom_ext
  intro x
  obtain ⟨n, rfl⟩ := index_surjective x
  rw [component_comp, hom_component, inv_component, component_id]
  exact (((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor.mapIso (ρ_ n)).hom_inv_id

/-- The reverse composition is the identity on the entire original spectrum. -/
theorem inv_hom (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) : inv E ≫ hom E = 𝟙 E := by
  apply hom_ext
  intro x
  obtain ⟨n, rfl⟩ := index_surjective x
  rw [component_comp, inv_component, hom_component, component_id]
  exact (((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor.mapIso (ρ_ n)).inv_hom_id

/-- The chosen forward map is natural in every whole native spectrum transformation. -/
theorem naturality {E E' : (EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})} (t : E ⟶ E') :
    (unitShift.{u, v}).map t ≫ hom E' = hom E ≫ t :=
  EnrichedFunctorCat.hom_ext
    (a := (unitShift.{u, v}).map t ≫ hom E') (b := hom E ≫ t) (by
      intro x
      obtain ⟨n, rfl⟩ := index_surjective x
      rw [component_comp, component_comp, hom_component, hom_component,
        unitShift_map_component]
      exact ordinaryMap_naturality t (ρ_ n).hom)

/-- The same chosen inverse retains every source and target naturality. -/
theorem inv_naturality {E E' : (EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})} (t : E ⟶ E') :
    t ≫ inv E' = inv E ≫ (unitShift.{u, v}).map t :=
  EnrichedFunctorCat.hom_ext
    (a := t ≫ inv E') (b := inv E ≫ (unitShift.{u, v}).map t) (by
      intro x
      obtain ⟨n, rfl⟩ := index_surjective x
      rw [component_comp, component_comp, inv_component, inv_component,
        unitShift_map_component]
      exact ordinaryMap_naturality t (ρ_ n).inv)

/-- The actual original forward maps form a full natural transformation. -/
def homNat : unitShift.{u, v} ⟶ 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) where
  app := hom
  naturality := fun _ _ t => naturality t

/-- The unchanged inverse maps form its full inverse natural transformation. -/
def invNat : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) ⟶ unitShift.{u, v} where
  app := inv
  naturality := fun _ _ t => inv_naturality t

/-- The genuine full enriched unit shift is naturally the identity functor. -/
def comparison : unitShift.{u, v} ≅ 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) where
  hom := homNat
  inv := invNat
  hom_inv_id := by
    apply NatTrans.ext
    funext E
    exact hom_inv E
  inv_hom_id := by
    apply NatTrans.ext
    funext E
    exact inv_hom E

/-- The full functor comparison uses exactly the chosen original right-unitor action. -/
theorem comparison_hom_component (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    component (comparison.hom.app E) (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      ordinaryMap E (ρ_ n).hom := hom_component E n

/-- Its inverse uses exactly the same chosen inverse action. -/
theorem comparison_inv_component (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    component (comparison.inv.app E) (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      ordinaryMap E (ρ_ n).inv := inv_component E n

end NativeOmegaRecovery.NativeSymmetricShiftUnit
