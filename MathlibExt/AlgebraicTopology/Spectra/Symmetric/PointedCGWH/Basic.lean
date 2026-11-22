/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.Basic
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.CanonicalProjectiveModels
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.RightModule
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SelectedDayInstances

/-!
# Symmetric spectra in pointed compactly generated spaces

The public carrier is the genuine enriched functor category on the full sphere
operator index. Its symmetric sequence and sphere-module formulas are derived
from the complete module/operator equivalence. In particular, restriction keeps
every original permutation and every level of an enriched transformation.
-/

set_option autoImplicit false
noncomputable section

universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH

/-- Symmetric spectra are the canonical native enriched operator functors. -/
abbrev SymmetricSpectrum := Spectra.Symmetric.Spectrum.{u, v}

namespace SymmetricSpectrum

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

/-- The complete source left sphere-module presentation of a native spectrum. -/
def toModule : SymmetricSpectrum.{u, v} ⥤
    CategoryTheory.Mod SymmetricSequence.{u, v} sphereSequence.{u, v} :=
  SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse

/-- The original source module acts on each entire native operator Hom. -/
def ofModule : CategoryTheory.Mod SymmetricSequence.{u, v} sphereSequence.{u, v} ⥤
    SymmetricSpectrum.{u, v} :=
  SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor

/-- A native spectrum's symmetric sequence is restriction along the index unit. -/
abbrev X (F : SymmetricSpectrum.{u, v}) : SymmetricSequence.{u, v} :=
  symmetricSequenceRestriction.{u, v}.obj F

/-- A native spectrum map's underlying sequence transformation. -/
def hom {F G : SymmetricSpectrum.{u, v}} (f : F ⟶ G) : F.X ⟶ G.X :=
  symmetricSequenceRestriction.{u, v}.map f

/-- The source module presentation has the same full symmetric sequence. -/
theorem toModule_X (F : SymmetricSpectrum.{u, v}) :
    (toModule.obj F).X = F.X := rfl

/-- The source presentation of a map retains its complete sequence transformation. -/
theorem toModule_hom {F G : SymmetricSpectrum.{u, v}} (f : F ⟶ G) :
    (toModule.map f).hom = hom f := rfl

/-- Restriction evaluates at the identical original finite index. -/
@[simp]
theorem X_obj (F : SymmetricSpectrum.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    F.X.functor.obj n = F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n) :=
  symmetricSequenceRestriction_obj F n

/-- The derived sequence map is the actual enriched transformation component. -/
@[simp]
theorem hom_app {F G : SymmetricSpectrum.{u, v}} (f : F ⟶ G)
    (n : Operad.SmallFinBijGroupoid) :
    (hom f).natTrans.app n =
      EnrichedFunctorCat.component f (symmetricOperatorObj.{u, v} n) :=
  symmetricSequenceRestriction_component f n

/-- The underlying sequence functor retains identity maps. -/
@[simp]
theorem hom_id (F : SymmetricSpectrum.{u, v}) : hom (𝟙 F) = 𝟙 F.X :=
  symmetricSequenceRestriction.map_id F

/-- The underlying sequence functor retains the order of every composite. -/
@[simp]
theorem hom_comp {F G H : SymmetricSpectrum.{u, v}} (f : F ⟶ G) (g : G ⟶ H) :
    hom (f ≫ g) = hom f ≫ hom g := symmetricSequenceRestriction.map_comp f g

/-- Equality of all original level maps detects the whole enriched spectrum map. -/
@[ext]
theorem hom_ext {F G : SymmetricSpectrum.{u, v}} {f g : F ⟶ G}
    (h : ∀ n : Operad.SmallFinBijGroupoid, (hom f).natTrans.app n = (hom g).natTrans.app n) :
    f = g := by
  apply SymmetricModulePresentation.moduleOperatorEquivalence.fullyFaithfulInverse.map_injective
  apply CategoryTheory.Mod.hom_ext
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext n
  exact h n

end SymmetricSpectrum
end PointedCGWH
