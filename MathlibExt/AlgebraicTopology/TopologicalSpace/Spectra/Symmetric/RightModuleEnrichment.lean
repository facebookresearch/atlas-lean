/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.HomCongr
public import MathlibExt.CategoryTheory.Enriched.RightActionMappingCategory
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.RightModuleMapping

/-!
# Enrichment of symmetric right sphere modules

Products and equalizers construct the mapping objects of symmetric right sphere modules,
with projections to their levelwise internal Hom objects. These mapping objects give an
enrichment whose ordinary morphisms, identities and composition are the module ones;
maps from every parameter object are characterized by compatible component families.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.hashCommand false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalOpposite
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.SymmetricRightModuleEnrichment

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction

/-- The symmetric right sphere modules carrying the mapping object enrichment. -/
abbrev Carrier := SymmetricRightModuleMapping.Carrier.{u, v}

/-- The actual original standard right modules, diagrams and complete right sphere actions. -/
abbrev actualData : Enriched.RightActionMappingCategory.Data
    (V := PointedCGWH.{u, v}) (I := Operad.SmallFinBijGroupoid) Carrier.{u, v} where
  diagram M := M.X.functor
  coefficient := sphereSequence.{u, v}.functor.obj
  right := SymmetricRightModulePresentation.pairAction

instance nativeObjectProducts : ∀ M N : Carrier.{u, v}, HasProduct
    (Enriched.RightActionMapping.objects
      (Enriched.RightActionMappingCategory.mappingData actualData M N)) :=
  fun M N => SymmetricRightModuleMapping.mappingObjectProduct M N

instance nativeRelationProducts : ∀ M N : Carrier.{u, v}, HasProduct
    (Enriched.RightActionMapping.relations
      (Enriched.RightActionMappingCategory.mappingData actualData M N)) :=
  fun M N => SymmetricRightModuleMapping.mappingRelationProduct M N

instance nativeEqualizers : ∀ M N : Carrier.{u, v}, HasEqualizer
    (Enriched.RightActionMapping.leftMap
      (Enriched.RightActionMappingCategory.mappingData actualData M N))
    (Enriched.RightActionMapping.rightMap
      (Enriched.RightActionMappingCategory.mappingData actualData M N)) :=
  fun M N => SymmetricRightModuleMapping.mappingEqualizer M N

/-- The complete generic mapping object is exactly the actual original module equalizer. -/
theorem mappingHom_eq (M N : Carrier.{u, v}) :
    Enriched.RightActionMappingCategory.Hom actualData M N =
      SymmetricRightModuleMapping.Hom M N := by
  exact (Enriched.RightActionMappingCategory.Hom_eq actualData M N).trans
    ((Enriched.RightActionMapping.Hom_eq
      (Enriched.RightActionMappingCategory.mappingData actualData M N)).trans
        (SymmetricRightModuleMapping.Hom_eq M N).symm)

/-- The original object equality is realized through its exact identity-value isomorphisms. -/
@[no_expose]
def mappingHomIso (M N : Carrier.{u, v}) : SymmetricRightModuleMapping.Hom M N ≅
    Enriched.RightActionMappingCategory.Hom actualData M N :=
  SymmetricRightModuleMapping.genericHomIso M N ≪≫
    (Enriched.RightActionMappingCategory.genericHomIso actualData M N).symm

/-- Every full forward mapping-value component is the original module projection. -/
@[reassoc]
theorem mappingHomIso_hom_π (M N : Carrier.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (mappingHomIso M N).hom ≫ Enriched.RightActionMappingCategory.π actualData M N n =
      SymmetricRightModuleMapping.π M N n := by
  change ((SymmetricRightModuleMapping.genericHomIso M N).hom ≫
    (Enriched.RightActionMappingCategory.genericHomIso actualData M N).inv) ≫
      Enriched.RightActionMappingCategory.π actualData M N n = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (SymmetricRightModuleMapping.genericHomIso M N).hom ≫ z)
      (Enriched.RightActionMappingCategory.genericHomIso_inv_π actualData M N n)).trans
        (SymmetricRightModuleMapping.genericHomIso_hom_π M N n))

/-- Every full inverse mapping-value component is the original module projection. -/
@[reassoc]
theorem mappingHomIso_inv_π (M N : Carrier.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (mappingHomIso M N).inv ≫ SymmetricRightModuleMapping.π M N n =
      Enriched.RightActionMappingCategory.π actualData M N n := by
  change ((Enriched.RightActionMappingCategory.genericHomIso actualData M N).hom ≫
    (SymmetricRightModuleMapping.genericHomIso M N).inv) ≫
      SymmetricRightModuleMapping.π M N n = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (Enriched.RightActionMappingCategory.genericHomIso actualData M N).hom ≫ z)
      (SymmetricRightModuleMapping.genericHomIso_inv_π M N n)).trans
        (Enriched.RightActionMappingCategory.genericHomIso_hom_π actualData M N n))

/-- The actual whole original module Hom correspondence at the exact selected mapping value. -/
@[no_expose]
def homEquiv (M N : Carrier.{u, v}) : (M ⟶ N) ≃
    (𝟙_ PointedCGWH.{u, v} ⟶ Enriched.RightActionMappingCategory.Hom actualData M N) where
  toFun f := SymmetricRightModuleMapping.homEquiv M N f ≫ (mappingHomIso M N).hom
  invFun f := (SymmetricRightModuleMapping.homEquiv M N).symm (f ≫ (mappingHomIso M N).inv)
  left_inv f := by
    dsimp only
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (SymmetricRightModuleMapping.homEquiv M N).symm_apply_apply f
  right_inv f := by
    dsimp only
    rw [Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every component is the original whole module mapping-space projection. -/
theorem homEquiv_π {M N : Carrier.{u, v}} (f : M ⟶ N) (n : Operad.SmallFinBijGroupoid) :
    homEquiv M N f ≫ Enriched.RightActionMappingCategory.π actualData M N n =
      eHomEquiv PointedCGWH.{u, v} (f.hom.natTrans.app n) := by
  change (SymmetricRightModuleMapping.homEquiv M N f ≫ (mappingHomIso M N).hom) ≫
    Enriched.RightActionMappingCategory.π actualData M N n = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => SymmetricRightModuleMapping.homEquiv M N f ≫ z)
      (mappingHomIso_hom_π M N n)).trans (SymmetricRightModuleMapping.homEquiv_π f n))

/-- The independent original product equalizers genuinely enrich the actual standard modules. -/
@[instance_reducible]
def enrichedOrdinaryCategory : EnrichedOrdinaryCategory PointedCGWH.{u, v} Carrier.{u, v} where
  toEnrichedCategory := Enriched.RightActionMappingCategory.enrichedCategory actualData
  homEquiv := homEquiv _ _
  homEquiv_id M := by
    change homEquiv M M (𝟙 M) = Enriched.RightActionMappingCategory.identity actualData M
    apply Enriched.RightActionMappingCategory.hom_ext actualData
    intro n
    exact (homEquiv_π (𝟙 M) n).trans
      ((eHomEquiv_id PointedCGWH.{u, v} (M.X.functor.obj n)).trans
        (Enriched.RightActionMappingCategory.identity_π actualData M n).symm)
  homEquiv_comp {M N P} f g := by
    change homEquiv M P (f ≫ g) = (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
      (homEquiv M N f ⊗ₘ homEquiv N P g) ≫
        Enriched.RightActionMappingCategory.composition actualData M N P
    apply Enriched.RightActionMappingCategory.hom_ext actualData
    intro n
    simp only [Category.assoc, Enriched.RightActionMappingCategory.composition_π,
      tensorHom_comp_tensorHom_assoc, homEquiv_π]
    exact eHomEquiv_comp PointedCGWH.{u, v}
      (f.hom.natTrans.app n) (g.hom.natTrans.app n)

attribute [local instance] enrichedOrdinaryCategory

/-- The native enriched Hom is exactly the actual original module mapping space. -/
theorem Hom_eq (M N : Carrier.{u, v}) : (M ⟶[PointedCGWH.{u, v}] N) =
    SymmetricRightModuleMapping.Hom M N := by
  change Enriched.RightActionMappingCategory.Hom actualData M N = _
  exact mappingHom_eq M N

/-- The selected enrichment uses every complete original mapping-space projection. -/
@[no_expose]
def π (M N : Carrier.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (M ⟶[PointedCGWH.{u, v}] N) ⟶ (ihom (M.X.functor.obj n)).obj (N.X.functor.obj n) :=
  Enriched.RightActionMappingCategory.π actualData M N n

/-- Every whole projection is retained by the actual original mapping-value comparison. -/
theorem π_comparison (M N : Carrier.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (mappingHomIso M N).hom ≫ π M N n = SymmetricRightModuleMapping.π M N n :=
  mappingHomIso_hom_π M N n

/-- Actual enriched identity preserves every entire original level. -/
theorem identity_π (M : Carrier.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    eId PointedCGWH.{u, v} M ≫ π M M n = eId PointedCGWH.{u, v} (M.X.functor.obj n) :=
  Enriched.RightActionMappingCategory.identity_π actualData M n

/-- The actual enriched composition retains both complete original internal-Hom factors. -/
theorem composition_π (M N P : Carrier.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    eComp PointedCGWH.{u, v} M N P ≫ π M P n = (π M N n ⊗ₘ π N P n) ≫
      eComp PointedCGWH.{u, v} (M.X.functor.obj n) (N.X.functor.obj n) (P.X.functor.obj n) :=
  Enriched.RightActionMappingCategory.composition_π actualData M N P n

/-- The selected enrichment retains the whole original module Hom
through its actual object comparison. -/
theorem eHomEquiv_apply {M N : Carrier.{u, v}} (f : M ⟶ N) :
    eHomEquiv PointedCGWH.{u, v} f =
      SymmetricRightModuleMapping.homEquiv M N f ≫ (mappingHomIso M N).hom := by rfl

/-- Every complete original parameter family is represented
by the actual selected module Hom. -/
@[no_expose]
def parameterEquiv (M N : Carrier.{u, v}) (P : PointedCGWH.{u, v}) :
    (P ⟶ (M ⟶[PointedCGWH.{u, v}] N)) ≃
      Enriched.RightActionMapping.CompatibleFamily
        (SymmetricRightModuleMapping.mappingData M N) P :=
  (Iso.homCongr (Iso.refl P)
    (Enriched.RightActionMappingCategory.genericHomIso actualData M N)).trans
      (Enriched.RightActionMapping.representationEquiv
        (Enriched.RightActionMappingCategory.mappingData actualData M N) P)

/-- Every whole forward parameter component is exactly the original projection. -/
theorem parameterEquiv_app (M N : Carrier.{u, v}) (P : PointedCGWH.{u, v})
    (f : P ⟶ (M ⟶[PointedCGWH.{u, v}] N)) (n : Operad.SmallFinBijGroupoid) :
    (parameterEquiv M N P f).app n = f ≫ π M N n := by
  change (𝟙 P ≫ f ≫ (Enriched.RightActionMappingCategory.genericHomIso actualData M N).hom) ≫
    Enriched.RightActionMapping.π
      (Enriched.RightActionMappingCategory.mappingData actualData M N) n = _
  rw [Category.id_comp, Category.assoc,
    Enriched.RightActionMappingCategory.genericHomIso_hom_π]
  rfl

/-- Every whole inverse parameter component is exactly the given original family map. -/
theorem parameterEquiv_symm_π (M N : Carrier.{u, v}) (P : PointedCGWH.{u, v})
    (q : Enriched.RightActionMapping.CompatibleFamily
      (SymmetricRightModuleMapping.mappingData M N) P)
    (n : Operad.SmallFinBijGroupoid) :
    (parameterEquiv M N P).symm q ≫ π M N n = q.app n := by
  change (𝟙 P ≫ Enriched.RightActionMapping.lift
    (Enriched.RightActionMappingCategory.mappingData actualData M N) q ≫
      (Enriched.RightActionMappingCategory.genericHomIso actualData M N).inv) ≫
        Enriched.RightActionMappingCategory.π actualData M N n = _
  rw [Category.id_comp, Category.assoc,
    Enriched.RightActionMappingCategory.genericHomIso_inv_π, Enriched.RightActionMapping.lift_π]

/-- All complete original projections determine every map into the actual module mapping object. -/
theorem hom_ext {M N : Carrier.{u, v}} {P : PointedCGWH.{u, v}}
    {f g : P ⟶ (M ⟶[PointedCGWH.{u, v}] N)}
    (h : ∀ n, f ≫ π M N n = g ≫ π M N n) : f = g :=
  Enriched.RightActionMappingCategory.hom_ext actualData h

end PointedCGWH.SymmetricRightModuleEnrichment
