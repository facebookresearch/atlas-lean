/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Finite-projective module crystals on the original PD test site

Every coefficient ring is the original nilpotent PD thickening ring.
Restriction is the actual presheaf-module map. Its linearization is the
native tensor-extension adjunction applied to that very map. Thus the
crystal condition tests every original PD arrow, with no independent
base-change isomorphism or comparison functor. The site remains the
general crystalline site, including every nilpotent coefficient test.

This defines module crystals; identifying the covariant Dieudonne
crystal with the original geometric internal Ext remains separate work.

Source: Berthelot--Ogus, Notes on crystalline cohomology, Chapter III;
Scholze--Weinstein, arXiv:1211.6357v2, Sections 3.2 and 4.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricPDModuleCrystals

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open GeometricPDCrystallineTests GeometricPDCrystallineSheaves

variable (p : ℕ) [Fact p.Prime] (A : PDBase) (S : Over A.reduction)

/-- Modules over the literal original PD ring presheaf. -/
abbrev Modules := PresheafOfModules.{1}
  (structureRingPresheaf p A S ⋙ forget₂ CommRingCat.{1} RingCat.{1})

variable (M : Modules p A S)

/-- The original semilinear restriction gives this exact tensor-linearized map. -/
def linearization {P Q : Obj p A S} (f : P ⟶ Q) :
    (ModuleCat.extendScalars.{1, 1, 1} ((structureRingPresheaf p A S).map f.op).hom).obj
      (M.obj (op Q)) ⟶
      M.obj (op P) :=
  ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1}
      ((structureRingPresheaf p A S).map f.op).hom).homEquiv
    (M.obj (op Q)) (M.obj (op P))).symm (M.map f.op)

/-- The crystal condition uses every actual PD arrow, including nilpotent refinements. -/
def IsCartesian : Prop := ∀ {P Q : Obj p A S} (f : P ⟶ Q),
  IsIso (linearization p A S M f)

/-- A finite-projective crystal of modules on the actual big affine PD basis. -/
structure Crystal where
  module : Modules p A S
  [finite : ∀ P : Obj p A S,
    Module.Finite ((structureRingPresheaf p A S).obj (op P)) (module.obj (op P))]
  [projective : ∀ P : Obj p A S,
    Module.Projective ((structureRingPresheaf p A S).obj (op P)) (module.obj (op P))]
  sheaf : Presheaf.IsSheaf (topology p A S) module.presheaf
  cartesian : IsCartesian p A S module

attribute [instance] Crystal.finite Crystal.projective

/-- The underlying sheaf retains the original abelian module values and all restriction maps. -/
def Crystal.underlying (C : Crystal p A S) : CoefficientSheaves p A S :=
  ⟨C.module.presheaf, C.sheaf⟩

end MathlibExt.AlgebraicGeometry.GeometricPDModuleCrystals
