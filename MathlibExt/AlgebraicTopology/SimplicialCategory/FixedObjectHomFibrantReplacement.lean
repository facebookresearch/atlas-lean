/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHornAcyclicity
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectCodiscreteTerminal
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanClasses

/-!
# Actual original fixed-label Hom fibrant replacement

The genuine stored free-horn factorization of the whole map to the
literal unit-Hom terminal enrichment retains every original object
label. Its full original left Hom maps are anodyne and weak; the
actual right Hom fibrations make every full resulting Hom Kan.
Groupoid components are transported through the SAME actual weak map,
rather than assumed for the resulting enrichment.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjectHomFibrantReplacement
open FixedObjects

variable (C : Type u) [EnrichedCategory SSet.{u} C]

/-- The SAME original enrichment on its literal original object labels. -/
abbrev source : FixedObjects C := FixedObjects.of C

/-- The complete original map to the actual unit-Hom terminal enrichment. -/
abbrev input : source C ⟶ CodiscreteTerminal.object C := CodiscreteTerminal.toTerminal (source C)

/-- The genuine stored original free-horn small-object factorization. -/
abbrev factorization := FreeFactorization.horn (input C)

/-- Its actual fixed-label intermediate object. -/
abbrev fixedObject : FixedObjects C := (factorization C).Z

/-- Its SAME whole original varying-object carrier. -/
abbrev object : Carrier.{u} := (fixedObject C).val

/-- The SAME full original left replacement map, on the original source enrichment. -/
abbrev map : EnrichedFunctor SSet.{u} C (object C) := (factorization C).i.val

/-- The actual full original terminal projection after replacement. -/
abbrev right := (factorization C).p

/-- Both whole original factorization maps recover the SAME original terminal input. -/
theorem fac : (factorization C).i ≫ right C = input C := (factorization C).fac

/-- Every original object retains exactly its supplied original label. -/
theorem map_object (x : C) : (map C).obj x = vertex (fixedObject C) x := map_vertex _ _

/-- Every SAME full original left Hom map is genuinely anodyne. -/
theorem map_hom_anodyne (x y : C) : SSet.anodyneExtensions ((map C).map x y) :=
  FixedObjectModel.horn_i_original_anodyne (input C) x y

/-- Every SAME original full Hom map is weak, without a source Kan hypothesis. -/
theorem map_hom_weak (x y : C) : SSet.realizationWeakEquivalences ((map C).map x y) :=
  (FixedObjectModel.weakEquivalences_original_iff (factorization C).i).mp
    (FixedObjectModel.trivialCofibrations_le_weakEquivalences _ (factorization C).hi) x y

/-- The entire original replacement map is DK weak on its actual labels and Homs. -/
theorem map_weak : EnrichedDwyerKan.weakEquivalences (factorization C).i.val :=
  (EnrichedDwyerKan.fixedWeak_iff (factorization C).i).mpr
    (FixedObjectModel.trivialCofibrations_le_weakEquivalences _ (factorization C).hi)

/-- Every actual complete replaced Hom maps by a genuine original Kan fibration to the original unit Hom. -/
theorem right_hom_fibration (x y : object C) : Fibration ((right C).val.map x y) :=
  FreeFactorization.horn_p_original (input C) x y

/-- The SAME entire replaced Hom is Kan, from its actual original terminal fibration. -/
theorem homKan (x y : object C) : SSet.KanComplex (x ⟶[SSet.{u}] y) := by
  let _ : Fibration ((right C).val.map x y) := right_hom_fibration C x y
  let _ : SSet.KanComplex ((right C).val.obj x ⟶[SSet.{u}] (right C).val.obj y) := by
    change SSet.KanComplex (𝟙_ SSet.{u})
    exact (isFibrant_iff_of_isTerminal (𝟙 (𝟙_ SSet.{u}))
      (CartesianMonoidalCategory.isTerminalTensorUnit : IsTerminal (𝟙_ SSet.{u}))).mpr
      (by infer_instance)
  exact isFibrant_of_fibration ((right C).val.map x y)

/-- The replacement's actual component functor is a genuine ordinary equivalence. -/
theorem component_isEquivalence : (ComponentCategory.mapFunctor (map C)).IsEquivalence :=
  EnrichedDwyerKan.componentIsEquivalence (factorization C).i.val (map_weak C)

/-- Groupoid components of the original enrichment imply groupoid
components of the SAME actual replacement, via its actual inverse component functor. -/
theorem component_isGroupoid [IsGroupoid (ComponentCategory.objects.{u} C)] :
    IsGroupoid (ComponentCategory.objects.{u} (object C)) := by
  let V := ComponentCategory.mapFunctor (map C)
  let _ : V.IsEquivalence := component_isEquivalence C
  exact isGroupoid_of_reflects_iso V.asEquivalence.inverse

end CategoryTheory.SimplicialEnrichment.FixedObjectHomFibrantReplacement
