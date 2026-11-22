/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.Functor
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.Topology.Category.PointedCGWH.SphereOne
public import Mathlib.CategoryTheory.Limits.Comma

/-!
# Canonical sequential spectra of pointed CGWH spaces

The carrier is the genuine enriched functor category on the one-sphere index.
Levels, morphism components and successor maps come from its enriched action.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

namespace PointedCGWH.Spectra.Sequential

/-- The actual one-sphere enriched indexing category. -/
abbrev Index := CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne.{u, v}

/-- The canonical genuine functor carrier for pointed sequential spectra. -/
abbrev Spectrum :=
  CategoryTheory.Spectra.Sequential.Spectrum PointedCGWH.sphereOne.{u, v}

end PointedCGWH.Spectra.Sequential

namespace PointedCGWH

/-- Sequential spectra of pointed CGWH spaces are genuine enriched functors
on the native one-sphere index. -/
abbrev SequentialSpectrum : Type (v + 1) := Spectra.Sequential.Spectrum.{u, v}

namespace SequentialSpectrum

/-- The object of the genuine spectrum in degree `n`. -/
abbrev level (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    PointedCGWH.{u, v} :=
  CategoryTheory.Spectra.Sequential.level X n

/-- The actual ordinary component of a spectrum morphism. -/
abbrev levelMap {X Y : PointedCGWH.SequentialSpectrum.{u, v}}
    (f : X ⟶ Y) (n : ℕ) : level X n ⟶ level Y n :=
  CategoryTheory.Spectra.Sequential.levelMap f n

/-- The complete uncurried action of the enriched index Hom object. -/
abbrev action (X : PointedCGWH.SequentialSpectrum.{u, v})
    (a b : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    X.toEnrichedFunctor.obj a ⊗ (a ⟶[PointedCGWH.{u, v}] b) ⟶
      X.toEnrichedFunctor.obj b :=
  CategoryTheory.Spectra.Sequential.action X a b

/-- The left successor map from the actual degree-one Hom and inverse braid. -/
abbrev structureMap (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    PointedCGWH.sphereOne.{u, v} ⊗ level X n ⟶ level X (n + 1) :=
  CategoryTheory.Spectra.Sequential.structureMap X n

/-- Level evaluation is the actual enriched evaluation functor. -/
abbrev evaluation (n : ℕ) :
    PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.{u, v} :=
  CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne.{u, v} n

/-- Identity maps have the actual identity components. -/
theorem levelMap_id (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    levelMap (𝟙 X) n = 𝟙 (level X n) :=
  CategoryTheory.Spectra.Sequential.levelMap_id X n

/-- Composition has the source-first composition of actual components. -/
theorem levelMap_comp {X Y Z : PointedCGWH.SequentialSpectrum.{u, v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    levelMap (f ≫ g) n = levelMap f n ≫ levelMap g n :=
  CategoryTheory.Spectra.Sequential.levelMap_comp f g n

/-- Equality of every actual level component determines a spectrum morphism. -/
theorem hom_ext {X Y : PointedCGWH.SequentialSpectrum.{u, v}} {f g : X ⟶ Y}
    (h : ∀ n : ℕ, levelMap f n = levelMap g n) : f = g :=
  CategoryTheory.Spectra.Sequential.hom_ext h

/-- Spectrum morphisms commute with the complete enriched Hom action. -/
theorem action_naturality {X Y : PointedCGWH.SequentialSpectrum.{u, v}}
    (f : X ⟶ Y) (a b : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    action X a b ≫ EnrichedFunctorCat.component f b =
      (EnrichedFunctorCat.component f a ⊗ₘ 𝟙 (a ⟶[PointedCGWH.{u, v}] b)) ≫
        action Y a b :=
  CategoryTheory.Spectra.Sequential.action_naturality f a b

/-- The same morphisms commute with the derived left successor maps. -/
theorem structureMap_naturality {X Y : PointedCGWH.SequentialSpectrum.{u, v}}
    (f : X ⟶ Y) (n : ℕ) :
    (PointedCGWH.sphereOne.{u, v} ◁ levelMap f n) ≫ structureMap Y n =
      structureMap X n ≫ levelMap f (n + 1) :=
  CategoryTheory.Spectra.Sequential.structureMap_naturality f n

/-- Evaluation retains the actual object in degree `n`. -/
theorem evaluation_obj (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (evaluation n).obj X = level X n := rfl

/-- Evaluation retains the actual ordinary morphism component. -/
theorem evaluation_map {X Y : PointedCGWH.SequentialSpectrum.{u, v}}
    (f : X ⟶ Y) (n : ℕ) : (evaluation n).map f = levelMap f n := rfl

end SequentialSpectrum
end PointedCGWH
