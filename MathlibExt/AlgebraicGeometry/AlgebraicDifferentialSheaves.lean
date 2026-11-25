/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/Topology/Sheaves/Modules/Differentials.lean`
(AxiomMath/Stacks, https://github.com/AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SectionwiseAlgebras.lean`
(AxiomMath/Stacks, https://github.com/AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source files carry no per-file copyright notice or author list.
Modified: the scalar morphisms use the affine-base structure map, and the sectionwise
Kähler and exterior-power presheaves are sheafified directly.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import MathlibExt.Algebra.Category.ModuleCat.PresheafExteriorPowers

/-! # Actual algebraic differential-form sheaves over an affine base

The constant scalar presheaf maps to the structure presheaf by the actual
scheme morphism. Kähler differentials and sectionwise exterior powers
are constructed by their native universal constructions and sheafified
over the scheme's structure sheaf.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves

open CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R]
  (X : Over (Spec (CommRingCat.of.{0} R)))

abbrev constants : X.left.Opensᵒᵖ ⥤ CommRingCat :=
  (Functor.const _).obj (CommRingCat.of R)

def scalarMap : constants R X ⟶ X.left.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    X.hom.appTop ≫ X.left.presheaf.map (homOfLE le_top).op
  naturality {U V} f := by
    dsimp
    rw [Category.id_comp, Category.assoc, Category.assoc,
      ← X.left.presheaf.map_comp]
    rfl

abbrev differentials :
    PresheafOfModulesOfCommRing X.left.presheaf :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (scalarMap R X)

abbrev formsPresheaf (i : ℕ) :
    PresheafOfModulesOfCommRing X.left.presheaf :=
  PresheafOfModules.extPow i (differentials R X)

/-- The actual sheaf Ω^i of relative algebraic differential forms. -/
def forms (i : ℕ) : X.left.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.left.ringCatSheaf.obj)).obj
    (formsPresheaf R X i)

end MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
