/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.DRightCategory
public import Mathlib.CategoryTheory.InducedCategory

public import MathlibExt.CategoryTheory.Enriched.InducedOrdinary
public import MathlibExt.CategoryTheory.Enriched.IndexedPointHomMap

/-!
# Ordinary morphisms of the symmetric right-source index

Identifies ordinary morphisms in the induced opposite right-source index with reversed morphisms between free sphere modules. The formulas transport their enriched points through the original Hom-object equality and its equality isomorphism.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory Opposite
open scoped MonoidalClosed CategoryTheory.MonObj



namespace PointedCGWH.SymmetricDRightOrdinary

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
  SymmetricModuleMappingComparison.literalEnrichedOrdinaryCategory

/-- The original standard RIGHT carrier underlying every source arrow. -/
abbrev Carrier := SymmetricDRight.Carrier.{u, v}

/-- Original source arrows are the actual opposite full free-module morphisms. -/
@[instance_reducible]
instance ordinaryCategory : Category SymmetricDRight.Index :=
  inferInstanceAs (Category (InducedCategory Carrier.{u, v}ᵒᵖ SymmetricDRight.freeLabel))

/-- The ordinary source and its literal mapping-space enrichment retain actual unit points. -/
@[instance_reducible]
instance enrichedOrdinaryCategory : EnrichedOrdinaryCategory PointedCGWH.{u, v}
    SymmetricDRight.Index :=
  { InducedCategory.enrichedOrdinaryCategory PointedCGWH.{u, v} SymmetricDRight.freeLabel with
    toEnrichedCategory := SymmetricDRight.enrichedCategory.{u, v} }

/-- The native ordinary structure is the same whole original induced data. -/
theorem original_enrichedOrdinaryCategory_eq : enrichedOrdinaryCategory.{u, v} =
    InducedCategory.enrichedOrdinaryCategory PointedCGWH.{u, v} SymmetricDRight.freeLabel := by
  rfl

/-- The actual induced ordinary source uses the previously proved whole D_R enrichment. -/
theorem enrichment_eq : enrichedOrdinaryCategory.{u, v}.toEnrichedCategory =
    SymmetricDRight.enrichedCategory.{u, v} := by rfl

/-- Every actual original source arrow is the complete standard RIGHT free-module map. -/
@[no_expose]
def homEquiv (d e : Operad.SmallFinBijGroupoid) :
    (SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) ≃
      (SymmetricDRight.freeObject e ⟶ SymmetricDRight.freeObject d) :=
  InducedCategory.homEquiv.trans Quiver.Hom.opEquiv.symm

/-- The whole source arrow map retains the actual original module morphism. -/
theorem homEquiv_apply (d e : Operad.SmallFinBijGroupoid)
    (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    homEquiv d e f = f.hom.unop := by rfl

/-- Every source unit parameter is the actual full original module mapping-space point. -/
theorem unitPoint (d e : Operad.SmallFinBijGroupoid)
    (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    HEq (eHomEquiv PointedCGWH.{u, v} f)
      (SymmetricRightModuleMapping.homEquiv (SymmetricDRight.freeObject e)
        (SymmetricDRight.freeObject d) (homEquiv d e f)) := by rfl

/-- The whole point function retains every original reversed free-module arrow. -/
theorem point_function (d e : SymmetricDRight.Index) :
    HEq (fun f : d ⟶ e => eHomEquiv PointedCGWH.{u, v} f)
      (fun f : d ⟶ e => eHomEquiv PointedCGWH.{u, v} (C := Carrier.{u, v}) f.hom.unop) := by
  rfl

/-- Every original ordinary source point is the same full original module point. -/
theorem actual_module_point (d e : Operad.SmallFinBijGroupoid)
    (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    HEq (eHomEquiv PointedCGWH.{u, v} f)
      (eHomEquiv PointedCGWH.{u, v} (C := Carrier.{u, v}) (homEquiv d e f)) := by
  rfl

/-- The original Hom-object equality transports each whole actual source point. -/
theorem actual_module_point_transport (d e : Operad.SmallFinBijGroupoid)
    (h : (SymmetricDRight.obj d ⟶[PointedCGWH.{u, v}] SymmetricDRight.obj e) =
      (SymmetricDRight.freeObject e ⟶[PointedCGWH.{u, v}] SymmetricDRight.freeObject d))
    (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    eHomEquiv PointedCGWH.{u, v} f ≫ eqToHom h =
      eHomEquiv PointedCGWH.{u, v} (C := Carrier.{u, v}) (homEquiv d e f) := by
  apply eq_of_heq
  exact (comp_eqToHom_heq (eHomEquiv PointedCGWH.{u, v} f) h).trans
    (actual_module_point d e f)

/-- The independent original enrichment and ordinary points use the same complete Hom transport. -/
theorem original_enrichment_point_transport (d e : Operad.SmallFinBijGroupoid)
    (h : (@EnrichedCategory.Hom PointedCGWH.{u, v} _ _ SymmetricDRight.Index
      SymmetricDRight.enrichedCategory.{u, v} (SymmetricDRight.obj d) (SymmetricDRight.obj e)) =
        (SymmetricDRight.freeObject e ⟶[PointedCGWH.{u, v}] SymmetricDRight.freeObject d))
    (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    eHomEquiv PointedCGWH.{u, v} f ≫ eqToHom h =
      eHomEquiv PointedCGWH.{u, v} (C := Carrier.{u, v}) (homEquiv d e f) := by
  apply eq_of_heq
  exact (comp_eqToHom_heq (eHomEquiv PointedCGWH.{u, v} f) h).trans
    (actual_module_point d e f)

/-- The complete original source identity isomorphism transports the original ordinary point. -/
theorem original_enrichment_iso_point (d e : Operad.SmallFinBijGroupoid)
    (h : (@EnrichedCategory.Hom PointedCGWH.{u, v} _ _ SymmetricDRight.Index
      SymmetricDRight.enrichedCategory.{u, v} (SymmetricDRight.obj d) (SymmetricDRight.obj e)) =
        (SymmetricDRight.freeObject e ⟶[PointedCGWH.{u, v}] SymmetricDRight.freeObject d))
    (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    eHomEquiv PointedCGWH.{u, v} f ≫ (eqToIso h).hom =
      eHomEquiv PointedCGWH.{u, v} (C := Carrier.{u, v}) (homEquiv d e f) :=
  original_enrichment_point_transport d e h f

/-- Every whole isomorphism proved equal to the original initializer retains its full point map. -/
theorem original_enrichment_chosen_iso_point (d e : Operad.SmallFinBijGroupoid)
    (h : (@EnrichedCategory.Hom PointedCGWH.{u, v} _ _ SymmetricDRight.Index
      SymmetricDRight.enrichedCategory.{u, v} (SymmetricDRight.obj d) (SymmetricDRight.obj e)) =
        (SymmetricDRight.freeObject e ⟶[PointedCGWH.{u, v}] SymmetricDRight.freeObject d))
    (i : (SymmetricDRight.obj d ⟶[PointedCGWH.{u, v}] SymmetricDRight.obj e) ≅
      (SymmetricDRight.freeObject e ⟶[PointedCGWH.{u, v}] SymmetricDRight.freeObject d))
    (hi : i = eqToIso h) (f : SymmetricDRight.obj d ⟶ SymmetricDRight.obj e) :
    eHomEquiv PointedCGWH.{u, v} f ≫ i.hom =
      eHomEquiv PointedCGWH.{u, v} (C := Carrier.{u, v}) (homEquiv d e f) := by
  rw [hi]
  exact original_enrichment_iso_point d e h f

end PointedCGWH.SymmetricDRightOrdinary
