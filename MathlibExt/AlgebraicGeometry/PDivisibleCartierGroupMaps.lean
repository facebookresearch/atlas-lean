/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
public import MathlibExt.AlgebraicGeometry.PDivisibleGroupMaps
public import MathlibExt.AlgebraicGeometry.FullPDCrystallineSourceMaps
public import MathlibExt.AlgebraicGeometry.PDivisibleBaseChangeModels

/-!
# Actual Cartier-dual tower maps and covariant Ext maps

Finite dualization is the completed native Cartier functor applied to
each original finite group-scheme map. Assembling these into dual-tower
maps is a normalized construction request. The covariant Ext map is
then defined by native precomposition on the actual full PD basis.

The source group Frobenius is the original relative scheme Frobenius;
the source Verschiebung retains its Cartier-dual Frobenius normalization.

Source: BBM82; Scholze--Weinstein1211.6357v2, Sections3.1 and4.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleCartierGroupMaps

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open PDivisibleGroupSchemes PDivisibleCartierTowerModels
open MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat
open scoped CategoryTheory.MonObj

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
  {G H : PDivisibleGroup (Spec (.of R)) p} (f : PDivisibleGroupMaps.Hom p G H)

attribute [local instance] PDivisibleGroupMaps.Hom.group

/-- The original finite group map in the completed Cartier category. -/
def finiteMap (n : ℕ) : finiteLevel p R G n ⟶ finiteLevel p R H n :=
  ObjectProperty.homMk (ObjectProperty.homMk (Grp.ofHom (f.levels.app n)))

/-- Its actual native finite Cartier dual map. -/
def finiteDualMap (n : ℕ) : dualLevel p R H n ⟶ dualLevel p R G n :=
  (cartierDualFunctor R).map (finiteMap p R f n).op

variable (DG : CartierDualTower p R G) (DH : CartierDualTower p R H)

/-- An assembled dual map has exactly the original native Cartier map at every level. -/
structure DualHom where
  hom : PDivisibleGroupMaps.Hom p DH.group DG.group
  finite : ∀ n : ℕ,
    finiteMap p R hom n ≫ (DG.finiteIso n).hom =
      (DH.finiteIso n).hom ≫ finiteDualMap p R f n

variable {p R f DG DH}

/-- The covariant full-basis map is precomposition by the actual original dual group map. -/
def covariantFullMap (d : DualHom p R f DG DH)
    (A : FullPDCrystallineTests.PDBase) (s : Spec (.of R) ⟶ A.reduction) :
    FullPDCrystallineExtModules.nativeModule p A (Over.mk s)
      (FullPDCrystallineSheaves.groupSheaf p A (Over.mk s) DG.group) 1 ⟶
    FullPDCrystallineExtModules.nativeModule p A (Over.mk s)
      (FullPDCrystallineSheaves.groupSheaf p A (Over.mk s) DH.group) 1 :=
  FullPDCrystallineSourceMaps.nativeSourceMap p A (Over.mk s)
    (FullPDCrystallineSourceMaps.groupSheafMap p A (Over.mk s) d.hom) 1

variable (p R) [CharP R p]

/-- The original affine R-scheme over the prime field. -/
def primeFieldBase : Over (Spec (.of (ZMod p))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (ZMod.castHom (dvd_refl p) R)))

variable (G : PDivisibleGroup (Spec (.of R)) p)
  (Q : PDivisibleBaseChangeModels.FrobeniusVerschiebung p (primeFieldBase p R) G)

/-- The original relative Frobenius, as an actual tower map. -/
def frobeniusHom : PDivisibleGroupMaps.Hom p G Q.twist.group where
  levels :=
    { app := Q.frobenius
      naturality {n m} a := Q.frobenius_naturality n m a.le }
  group := Q.frobenius_group

/-- The original Verschiebung, as an actual tower map in the opposite direction. -/
def verschiebungHom : PDivisibleGroupMaps.Hom p Q.twist.group G where
  levels :=
    { app := Q.verschiebung
      naturality {n m} a := Q.verschiebung_naturality n m a.le }
  group := Q.verschiebung_group

/-- Source Cartier normalization of Verschiebung and all original dual maps. -/
structure CartierFrobeniusVerschiebung (DG : CartierDualTower p R G) where
  source : PDivisibleBaseChangeModels.FrobeniusVerschiebung p (primeFieldBase p R) G
  dualTwist : CartierDualTower p R source.twist.group
  dualFrobenius : DualHom p R (frobeniusHom p R G source) DG dualTwist
  dualVerschiebung : DualHom p R (verschiebungHom p R G source) dualTwist DG
  dualTwistLevels : dualTwist.group.levels ≅
    PDivisibleBaseChangeModels.pulledLevels p DG.group
      (PDivisibleBaseChangeModels.frobeniusBase p (primeFieldBase p R))
  verschiebung_source : ∀ n : ℕ,
    dualVerschiebung.hom.levels.app n ≫ dualTwistLevels.hom.app n =
      PDivisibleBaseChangeModels.relativeFrobenius p (primeFieldBase p R) DG.group n

end MathlibExt.AlgebraicGeometry.PDivisibleCartierGroupMaps
