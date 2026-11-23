/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DeRhamSectionwise.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
`StacksFrontier/Topology/Sheaves/Modules/DeRhamExistence.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b), the sectionwise differential criterion:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: retain the affine-base scalar map, use ordinary base-ring linearity rather than
prime-field Frobenius linearity, and derive the fixed module-sheaf sections source.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Module.ULift
public import MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves

/-!
# Actual relative de Rham complexes over arbitrary affine ring bases

Each form term is the native sectionwise Kahler/exterior-power
construction. Differential data satisfy the de Rham rule on every exact
wedge generator. This is a characterized ordinary source input, whose
existence is already implemented in the public source; no independent
replacement complex is supplied.

The complex is sheafified as base-ring modules, and hypercohomology is
the genuine right-derived functor of its actual global sections.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeDeRhamModels

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open AlgebraicDifferentialSheaves

attribute [local instance] HasDerivedCategory.standard

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

abbrev constantRing : X.left.Opensᵒᵖ ⥤ RingCat :=
  constants R X ⋙ forget₂ CommRingCat RingCat

abbrev baseScalars : constantRing R X ⟶ X.left.ringCatSheaf.obj :=
  Functor.whiskerRight (scalarMap R X) (forget₂ CommRingCat RingCat)

/-- Read a constant-ring module presheaf in the ordinary module category. -/
def constantModulePresheaf (M : PresheafOfModules (constantRing R X)) :
    X.left.Opensᵒᵖ ⥤ ModuleCat R where
  obj U := M.obj U
  map {U V} f := M.map f ≫
    (ModuleCat.restrictScalarsId' ((constantRing R X).map f).hom
      (by rfl)).hom.app (M.obj V)
  map_id U := by
    ext a
    change M.map (𝟙 U) a = a
    rw [M.map_id]
    rfl
  map_comp f g := by
    ext a
    exact M.map_comp_apply f g a

/-- The actual relative form terms, with ordinary base-ring scalars. -/
def formPresheaf (i : ℕ) : X.left.Opensᵒᵖ ⥤ ModuleCat R :=
  constantModulePresheaf R X
    ((PresheafOfModules.restrictScalars (baseScalars R X)).obj
      (formsPresheaf R X i))

/-- An exact-wedge generator in its original O-module before restriction. -/
def generator (i : ℕ) (U : X.left.Opensᵒᵖ)
    (a : X.left.presheaf.obj U) (b : Fin i → X.left.presheaf.obj U) :
    (formPresheaf R X i).obj U :=
  (a • exteriorPower.ιMulti (X.left.presheaf.obj U) i
    (fun j ↦ CommRingCat.KaehlerDifferential.d
      (f := (scalarMap R X).app U) (b j)) :
        (formsPresheaf R X i).obj U)

/-- The ordinary de Rham differential, fully fixed on local generators. -/
structure Differential where
  d : ∀ i : ℕ, formPresheaf R X i ⟶ formPresheaf R X (i + 1)
  square : ∀ i, d i ≫ d (i + 1) = 0
  generator : ∀ (i : ℕ) (U : X.left.Opensᵒᵖ)
    (a : X.left.presheaf.obj U) (b : Fin i → X.left.presheaf.obj U),
    (d i).app U (RelativeDeRhamModels.generator R X i U a b) =
      RelativeDeRhamModels.generator R X (i + 1) U 1 (Fin.cons a b)

/-- The actual module lift used only to match the cohomology universe. -/
def liftModules : ModuleCat.{0} R ⥤ ModuleCat.{1} R where
  obj M := ModuleCat.of R (ULift.{1} M)
  map f := ModuleCat.ofHom
    { toFun a := ULift.up (f.hom a.down)
      map_add' _ _ := ULift.ext (map_add _ _ _)
      map_smul' _ _ := ULift.ext (f.hom.map_smul _ _) }
  map_id _ := by ext a; rfl
  map_comp _ _ := by ext a; rfl

instance liftModules_additive : (liftModules R).Additive where
  map_add := by intros; ext a; rfl

abbrev topology := _root_.Opens.grothendieckTopology X.left
abbrev Sheaves := Sheaf (topology R X) (ModuleCat.{0} R)

/-- The actual module forgetful functor preserves the filtered colimits
used by sheaf inverse image. -/
instance moduleForgetFiltered :
    PreservesFilteredColimits (forget (ModuleCat.{0} R)) := by
  let : PreservesColimitsOfSize.{0, 0}
      (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{0, 0, 0, 0} R
  exact comp_preservesFilteredColimits.{0, 0}
    (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})
    (forget AddCommGrpCat.{0})

instance moduleSheafify : HasSheafify (topology R X) (ModuleCat.{0} R) := by
  let : HasLimits (ModuleCat.{0} R) :=
    ModuleCat.hasLimitsOfSize.{0, 0, 0, 0}
  infer_instance

/-- The actual sheafified, integer-indexed relative de Rham complex. -/
def Differential.natComplex (D : Differential R X) :
    CochainComplex (Sheaves R X) ℕ :=
  let K := CochainComplex.of (formPresheaf R X) D.d D.square
  ((presheafToSheaf (topology R X) (ModuleCat.{0} R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K

/-- Extend the actual form complex by zero in negative degrees. -/
def Differential.complex (D : Differential R X) :
    CochainComplex (Sheaves R X) ℤ :=
  D.natComplex.extend ComplexShape.embeddingUpNat

/-- The canonical exact-wedge section in a sheafified form term. -/
def Differential.sheafGenerator (D : Differential R X) (i : ℕ)
    (U : X.left.Opensᵒᵖ) (a : X.left.presheaf.obj U)
    (b : Fin i → X.left.presheaf.obj U) :
    ((D.natComplex.X i).obj.obj U) :=
  (toSheafify (topology R X) (formPresheaf R X i)).app U
    (RelativeDeRhamModels.generator R X i U a b)

instance coefficientsSiteLimits : HasLimitsOfShape X.left.Opensᵒᵖ
    (ModuleCat.{0} R) := by
  let : HasLimitsOfSize.{0, 0} (ModuleCat.{0} R) :=
    ModuleCat.hasLimitsOfSize.{0, 0, 0, 0}
  infer_instance

/-- The fixed ordinary sections functor. -/
def sections : Sheaves R X ⥤ ModuleCat.{0} R :=
  (sheafSections (topology R X) (ModuleCat.{0} R)).obj
    (op (⊤ : X.left.Opens))

instance sections_additive : (sections R X).Additive where
  map_add {F G} f g := by
    rfl

def sectionsSource : CochainComplex (Sheaves R X) ℤ ⥤
    DerivedCategory (ModuleCat.{1} R) :=
  (sections R X ⋙ liftModules R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

abbrev quasiIso :=
  HomologicalComplex.quasiIso (Sheaves R X) (ComplexShape.up ℤ)

/-- Generic right-derived existence for the actual ordinary sections. -/
class HasDerivedSections : Prop where
  exists_derived : (sectionsSource R X).HasRightDerivedFunctor (quasiIso R X)

attribute [instance] HasDerivedSections.exists_derived

/-- Actual de Rham hypercohomology, with the form complex fixed. -/
def Differential.hypercohomology [HasDerivedSections R X]
    (D : Differential R X) : DerivedCategory (ModuleCat.{1} R) :=
  ((sectionsSource R X).totalRightDerived DerivedCategory.Q
    (quasiIso R X)).obj (DerivedCategory.Q.obj D.complex)

end MathlibExt.AlgebraicGeometry.RelativeDeRhamModels
