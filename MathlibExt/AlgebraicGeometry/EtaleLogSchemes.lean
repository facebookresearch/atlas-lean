/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogStructures
public import MathlibExt.AlgebraicGeometry.SmallEtaleGeometry
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Ring.ULift

/-!
# Fine and saturated log schemes on the actual small etale ringed site

The structure ring is the native sheafification of the actual global
regular-function rings of small-etale schemes, with a universe lift only.
Scheme pullback uses the actual etale base-change projection and the native
sheafification adjunction. Thus the log objects are sheaves M→O with the
actual unit/log condition, not a Zariski or split-normal-crossings substitute.
Fine and fs are the existing chart-cover/groupification contracts.

References: Kato, Logarithmic structures of Fontaine--Illusie, §1;
Borne--Vistoli, arXiv:1001.0466v2, Definition3.4/Proposition3.9;
Gross--Siebert, arXiv:1102.4322v2, Remark1.2(1), which permits etale
curve ghost sheaves even when target/base logs are Zariski-defined.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.EtaleLogSchemes
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleGeometry
open MathlibExt.AlgebraicGeometry.LogStructures
universe u

/-- Only universe size changes; all ring elements and ring maps are retained. -/
def liftRings : CommRingCat.{u} ⥤ CommRingCat.{u+1} where
  obj R := .of (ULift.{u+1} R)
  map f := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp (f.hom.comp ULift.ringEquiv.toRingHom))
  map_id R := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- Actual regular functions of the native small-etale schemes. -/
def rawRing (X : Scheme.{u}) : X.Etaleᵒᵖ ⥤ CommRingCat.{u+1} :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ ⋙ liftRings

/-- The native sheafification of those regular functions. Its maps remain
fixed even before the existing etale descent comparison is integrated. -/
def structureRing (X : Scheme.{u}) : RingSheaf X.smallEtaleTopology :=
  (presheafToSheaf X.smallEtaleTopology CommRingCat.{u+1}).obj (rawRing X)

/-- Actual regular-function pullback on a base-changed etale chart. -/
def rawPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    rawRing Y ⟶ (etaleBaseChange f).op ⋙ rawRing X where
  app U := liftRings.map ((projection f U.unop).appTop)
  naturality {U V} a := by
    change liftRings.map (Scheme.Γ.map a.unop.left.op) ≫
      liftRings.map (Scheme.Γ.map (projection f V.unop).op) =
      liftRings.map (Scheme.Γ.map (projection f U.unop).op) ≫
        liftRings.map (Scheme.Γ.map ((etaleBaseChange f).map a.unop).left.op)
    rw [← liftRings.map_comp, ← liftRings.map_comp, ← Scheme.Γ.map_comp, ← Scheme.Γ.map_comp]
    apply congrArg liftRings.map
    apply congrArg Scheme.Γ.map
    simp only [← op_comp]
    exact congrArg Quiver.Hom.op (projection_naturality f a.unop).symm

/-- The actual ringed-site structure map is the sheafification adjoint of
regular-function pullback, not a supplied arbitrary ring sheaf morphism. -/
def ringSharp {X Y : Scheme.{u}} (f : X ⟶ Y) [HasInverseImage f] :
    structureRing Y ⟶
      ((etaleBaseChange f).sheafPushforwardContinuous CommRingCat
        Y.smallEtaleTopology X.smallEtaleTopology).obj (structureRing X) :=
  ((sheafificationAdjunction Y.smallEtaleTopology CommRingCat.{u+1}).homEquiv _ _).symm
    (rawPullback f ≫ Functor.whiskerLeft (etaleBaseChange f).op
      ((sheafificationAdjunction X.smallEtaleTopology CommRingCat.{u+1}).unit.app (rawRing X)))

/-- Arbitrary log schemes on the native small-etale ringed site. -/
structure LogScheme where
  scheme : Scheme.{u}
  log : LogStructure scheme.smallEtaleTopology (structureRing scheme)

/-- General fine/fs scope is an actual covering-chart property. -/
def LogScheme.IsFine (X : LogScheme.{u}) : Prop :=
  HasFineCharts X.scheme.smallEtaleTopology X.log

def LogScheme.IsFineSaturated (X : LogScheme.{u}) : Prop :=
  HasFineSaturatedCharts X.scheme.smallEtaleTopology X.log

/-- Morphisms along actual scheme maps use the computed ringed-site map.
The log arrow is the actual monoid-sheaf commuting triangle. -/
abbrev MorphismAlong (X Y : LogScheme.{u}) (f : X.scheme ⟶ Y.scheme) [HasInverseImage f] :=
  LogStructures.HomAlong X.scheme.smallEtaleTopology Y.scheme.smallEtaleTopology
    (etaleBaseChange f) (ringSharp f) X.log Y.log

structure Hom (X Y : LogScheme.{u}) where
  map : X.scheme ⟶ Y.scheme
  [inverseImage : HasInverseImage map]
  logMap : MorphismAlong X Y map

attribute [instance] Hom.inverseImage

end MathlibExt.AlgebraicGeometry.EtaleLogSchemes
