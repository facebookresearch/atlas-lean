/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import MathlibExt.AlgebraicGeometry.GeometricPDCrystallineTests
public import MathlibExt.AlgebraicGeometry.PDivisiblePointFunctors
public import MathlibExt.CategoryTheory.SheafInternalExtModels
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# Actual crystalline structure and p-divisible coefficient sheaves

The structure sheaf is the actual sheafification of the rings of the
PD thickenings. The group coefficient sheaf is the sheafification of
the original finite group-scheme tower evaluated on every nilpotent
reduction. Thus `mu_p`, formal directions and all ring maps are retained.
The internal Ext sheaf is then computed from these fixed geometric
coefficient sheaves by native injective resolutions.

For the covariant Dieudonné convention, pass the actual Cartier dual
tower as the group argument. The dual construction, crystal base change,
F/V and completed A_cris evaluation are separate source-normalized maps.

References: Berthelot--Breen--Messing, *Théorie de Dieudonné cristalline II*;
Scholze--Weinstein, arXiv:1211.6357v2, Sections 3.2 and 4.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open GeometricPDCrystallineTests PDivisibleGroupSchemes PDivisiblePointFunctors
open MathlibExt.CategoryTheory.SheafInternalExtModels

variable (p : ℕ) [Fact p.Prime] (A : PDBase) (S : Over A.reduction)

/-- The integral abelian coefficient category on the actual PD site. -/
abbrev CoefficientSheaves := AbelianSheaves (topology p A S)

/-- Mathlib's sheafification instance on a small site, restated at universe `1` for this file
only: synthesising it on the small model inside `Sheaf.isGrothendieckAbelian_of_essentiallySmall`
otherwise leaves the small model's universe as a stuck metavariable. -/
local instance abelianSheafifySmall {C : Type 1} [SmallCategory C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{1} := by
  infer_instance

instance coefficientSheavesGrothendieck :
    IsGrothendieckAbelian.{1} (CoefficientSheaves p A S) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{1, 1, 0, 2, 1}
    (topology p A S) AddCommGrpCat.{1}

/-- The original thickening rings, with only the necessary universe lift. -/
def structureRingPresheaf : (Obj p A S)ᵒᵖ ⥤ CommRingCat.{1} where
  obj U := CommRingCat.of (ULift.{1} U.unop.ring)
  map f := CommRingCat.ofHom f.unop.algebra.toRingHom.ulift
  map_id U := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The actual crystalline structure ring sheaf. -/
def structureRingSheaf : Sheaf (topology p A S) CommRingCat.{1} :=
  (presheafToSheaf (topology p A S) CommRingCat.{1}).obj
    (structureRingPresheaf p A S)

/-- Its fixed underlying abelian coefficient sheaf. -/
def structureSheaf : CoefficientSheaves p A S :=
  (sheafCompose (topology p A S)
    (forget₂ CommRingCat.{1} RingCat.{1} ⋙
      forget₂ RingCat.{1} AddCommGrpCat.{1})).obj
    (structureRingSheaf p A S)

/-- Universe lift of actual group points; no group or inverse limit is supplied. -/
def liftAbelianGroups : AddCommGrpCat.{0} ⥤ AddCommGrpCat.{1} where
  obj G := AddCommGrpCat.of (ULift.{1} G)
  map f := AddCommGrpCat.ofHom
    { toFun x := ULift.up (f.hom x.down)
      map_zero' := ULift.ext (map_zero f.hom)
      map_add' x y := ULift.ext (map_add f.hom x.down y.down) }
  map_id G := by ext x; rfl
  map_comp f g := by ext x; rfl

variable (G : PDivisibleGroup S.left p)

/-- Original scheme-valued tower points on the reductions of the PD tests. -/
def groupPresheaf : (Obj p A S)ᵒᵖ ⥤ AddCommGrpCat.{1} :=
  (reductions p A S).op ⋙ pointwisePoints (p := p) (S := S.left) G ⋙
    CommGrpCat.toAddCommGrp ⋙ liftAbelianGroups

/-- Sheafify precisely that geometric group diagram. -/
def groupSheaf : CoefficientSheaves p A S :=
  (presheafToSheaf (topology p A S) AddCommGrpCat.{1}).obj
    (groupPresheaf p A S G)

/-- Contravariant crystalline Ext; use the actual dual tower for covariance. -/
def crystallineExt : CoefficientSheaves p A S :=
  internalExt (topology p A S) (groupSheaf p A S G) (structureSheaf p A S) 1

/-- The literal Hom-resolution cochains computing that Ext sheaf. -/
def crystallineExtCochains : CochainComplex (CoefficientSheaves p A S) ℕ :=
  extCochains (topology p A S) (groupSheaf p A S G) (structureSheaf p A S)

/-- This Ext is normalized to homology of the actual internal-Hom cochains. -/
def crystallineExtResolutionIso : crystallineExt p A S G ≅
    (crystallineExtCochains p A S G).homology 1 :=
  internalExtResolutionIso (topology p A S) (groupSheaf p A S G)
    (structureSheaf p A S) 1

end MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves
