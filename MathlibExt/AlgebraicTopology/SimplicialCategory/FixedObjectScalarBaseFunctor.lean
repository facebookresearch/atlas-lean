/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectScalarNerveNaturality

/-!
# The SAME full original labelled scalar base functor

All original fixed-label enrichments and full Hom maps give the genuine
native scalar nerve diagonal functor. Characteristic identity and
composition formulas retain every original coefficient, and the actual
canonical label comparison preserves weakness of the original base map.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.SimplicialEnrichment.FixedObjects
variable {O : Type u}

/-- The entire native original label-base map retains the SAME full identity functor. -/
lemma scalarLabelBaseMap_id (C : FixedObjects O) : scalarLabelBaseMap (𝟙 C) = 𝟙 (scalarLabelBase C) := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro w
  have hi : (scalarCatMap (𝟙 C) q).toFunctor = 𝟭 (scalarCat C q) := by
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro x y a
    exact heq_of_eq (congrArg (fun f => f.app q a) (homMap_id C x y))
  exact (congrArg (fun F => w ⋙ F) hi).trans (Functor.comp_id w)

/-- The entire native original label-base map retains SAME full enriched composition. -/
lemma scalarLabelBaseMap_comp {C D E : FixedObjects O} (F : C ⟶ D) (G : D ⟶ E) :
    scalarLabelBaseMap (F ≫ G) = scalarLabelBaseMap F ≫ scalarLabelBaseMap G := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro w
  have hc : (scalarCatMap (F ≫ G) q).toFunctor = (scalarCatMap F q).toFunctor ⋙ (scalarCatMap G q).toFunctor := by
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro x y a
    exact heq_of_eq (congrArg (fun f => f.app q a) (homMap_comp F G x y))
  exact (congrArg (fun H => w ⋙ H) hc).trans (Functor.assoc _ _ _).symm

/-- The SAME complete original fixed-label scalar base nerve diagonal functor. -/
def scalarLabelBaseFunctor : FixedObjects O ⥤ SSet.{u} where
  obj := scalarLabelBase
  map := scalarLabelBaseMap
  map_id := scalarLabelBaseMap_id
  map_comp := scalarLabelBaseMap_comp

/-- Canonical original label coordinates preserve and reflect weakness of the SAME full original base map. -/
theorem scalarLabelBaseMap_weak_iff {C D : FixedObjects O} (F : C ⟶ D) :
    SSet.realizationWeakEquivalences (scalarLabelBaseMap F) ↔
      SSet.realizationWeakEquivalences (SSet.ScalarUnderCategory.baseMap F.val) := by
  have hC := labelBaseToCanonical_weak C
  have hD := labelBaseToCanonical_weak D
  constructor
  · intro h
    have hp := SSet.realizationWeakEquivalences.comp_mem _ _ h hD
    rw [scalarLabelBaseMap_natural] at hp
    exact SSet.realizationWeakEquivalences.of_precomp _ _ hC hp
  · intro h
    have hp := SSet.realizationWeakEquivalences.comp_mem _ _ hC h
    rw [← scalarLabelBaseMap_natural] at hp
    exact SSet.realizationWeakEquivalences.of_postcomp _ _ hD hp

end CategoryTheory.SimplicialEnrichment.FixedObjects
