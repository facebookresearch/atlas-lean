/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomSourceUnit
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomColimitUniverse
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredRootEssentialSurjectivity
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerCofibrationObjectMonicity
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OriginalRealizationWeakFilteredUniverses
import Mathlib.CategoryTheory.Limits.Connected

/-!
# The SAME complete original root functor is weak at genuine filtered colimits

The original Hom functor retains its literal full mapped cocone. Its
actual root maps give the full natural comparison, and the proved
original scalar filtered weak theorem preserves the SAME terminal Hom
map. Genuine original component representatives give full DK weakness.
The diagram object and Hom universes remain independent and explicitly small.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalFilteredRoot
attribute [local instance] IsFiltered.isConnected

variable {C : Carrier.{u}} {J : Type v} [Category.{w} J] [IsFiltered J]
  [UnivLE.{v, u}] [UnivLE.{w, u}] (U : J ⥤ Under C)

/-- Every SAME original terminal root Hom map is weak at its genuine full filtered colimit. -/
theorem hom_weak (s : Cocone U) (hs : IsColimit s)
    (hObj : ∀ {i j : J} (f : i ⟶ j), Function.Injective (U.map f).right.obj)
    (hU : ∀ i, EnrichedDwyerKan.localWeak (U.obj i).hom) (x y : C) :
    SSet.realizationWeakEquivalences (s.pt.hom.map x y) := by
  let A := x ⟶[SSet.{u}] y
  let c := (OriginalUnderHom.functor C x y).mapCocone s
  have hc : IsColimit c := OriginalUnderHomColimit.originalIsColimitUnivLE U s hs x y hObj
  exact SSet.realizationWeakEquivalences.of_isColimit_filtered_univLE.{u, v, w}
    (OriginalUnderHom.sourceUnit U x y) (isColimitConstCocone J A) hc
      (s.pt.hom.map x y)
        (fun i => (Category.id_comp _).trans (OriginalUnderHom.sourceUnit_cocone U x y s i).symm)
          (fun i => hU i x y)

/-- The SAME original terminal root functor is genuinely DK weak from its actual weak stage maps. -/
theorem weak (s : Cocone U) (hs : IsColimit s)
    (hObj : ∀ {i j : J} (f : i ⟶ j), Function.Injective (U.map f).right.obj)
    (hU : ∀ i, EnrichedDwyerKan.weakEquivalences (U.obj i).hom) :
    EnrichedDwyerKan.weakEquivalences s.pt.hom :=
  ⟨fun x y => hom_weak U s hs hObj (fun i => (hU i).1) x y,
    component_essSurj U s hs (fun i => (hU i).2)⟩

/-- Genuine original C0 transitions give weakness of the SAME full original filtered root colimit map. -/
theorem weak_of_cofibrations (s : Cocone U) (hs : IsColimit s)
    (hC : ∀ {i j : J} (f : i ⟶ j), Bergner.cofibrations (U.map f).right)
    (hU : ∀ i, EnrichedDwyerKan.weakEquivalences (U.obj i).hom) :
    EnrichedDwyerKan.weakEquivalences s.pt.hom :=
  weak U s hs (fun f => Bergner.cofibration_objects_injective _ (hC f)) hU

end CategoryTheory.SimplicialEnrichment.OriginalFilteredRoot
