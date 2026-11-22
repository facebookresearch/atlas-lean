/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.FunctorClosed
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Basic
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClasses

/-!
# Omega conditions for sequential pointed spectra

Defines the successor adjoints of the structure maps of pointed CGWH sequential spectra
and proves their naturality. The Omega condition requires each adjoint to be a weak
homotopy equivalence after forgetting its base point.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory MorphismProperty
open scoped MonoidalClosed

namespace PointedCGWH.SequentialSpectrum

/-- The actual successor transpose at the original one-sphere coordinate. -/
abbrev adjointStructureMap (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    X.level n ⟶ (ihom PointedCGWH.sphereOne.{u, v}).obj (X.level (n + 1)) :=
  CategoryTheory.Spectra.Sequential.adjointStructureMap X n

/-- The transpose retains the original complete native structure map. -/
theorem adjointStructureMap_uncurry (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    MonoidalClosed.uncurry (adjointStructureMap X n) = X.structureMap n :=
  CategoryTheory.Spectra.Sequential.adjointStructureMap_uncurry X n

/-- The actual native successor transposes commute with every spectrum map. -/
theorem adjointStructureMap_naturality
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    levelMap f n ≫ adjointStructureMap Y n =
      adjointStructureMap X n ≫
        (ihom PointedCGWH.sphereOne.{u, v}).map (levelMap f (n + 1)) :=
  CategoryTheory.Spectra.Sequential.adjointStructureMap_naturality f n

/-- Every actual native successor transpose is a weak equivalence after forgetting its point. -/
abbrev IsOmega (X : PointedCGWH.SequentialSpectrum.{u, v}) : Prop :=
  CategoryTheory.Spectra.Sequential.IsOmega
    (CGWH.weakHomotopyEquivalences.{u, v}.inverseImage PointedCGWH.pointedToCGWH) X

/-- The native Omega condition is the right-map condition at every actual level. -/
theorem isOmega_iff (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    X.IsOmega ↔ ∀ n : ℕ,
      CGWH.weakHomotopyEquivalences (adjointStructureMap X n).right := Iff.rfl

end PointedCGWH.SequentialSpectrum
