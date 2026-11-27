/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeKummerFlatModels
public import MathlibExt.AlgebraicGeometry.NativeKummerFlatModelsRegularSections

/-!
# Native Kummer-flat chart and fine/saturated base-change requests

The category, actual characteristic stalks, original log generators,
native Z[P] maps, flat chart comparisons and covering families are fixed
before these source construction/proof requests. Fine/saturated log
pullbacks use that same category; the underlying scheme may change.
The infinite-root/topos/reconstruction conclusions are separate.

Source: Talpo--Vistoli arXiv:1410.1164v2, Definition6.10 and
Remarks6.11--6.12; Kato Section1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NativeKummerFlatModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams EtaleLogNativeCategory
open KatoChartCoefficientModels NativeKummerFlatModels

variable [InverseImageTheory.{0}] [N : NativeCategoryModel.{0}]

/-- The categorical fs log pullback retains the original log objects
and all native arrows; no scheme-pullback equality is asserted. -/
public theorem_wanted fineSaturatedLogPullbacks : HasPullbacks FineSaturatedSchemes

public def_wanted kummerFlatIdentity (D : RegularSectionComparisons)
    (X : LogScheme.{0}) (hX : X.IsFineSaturated) :
    KummerFlatData D (N.operations.identity X)

public def_wanted kummerFlatComposition (D : RegularSectionComparisons)
    {X Y Z : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y) (g : EtaleLogSchemes.Hom Y Z)
    (hf : KummerFlatData D f) (hg : KummerFlatData D g) :
    KummerFlatData D (N.operations.compose f g)

/-- Stability uses the actual categorical fs log fibre product. -/
public theorem_wanted kummerFlatBaseChange (D : RegularSectionComparisons)
    [HasPullbacks FineSaturatedSchemes]
    {X Y Z : FineSaturatedSchemes} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : IsKummerFlat D f.hom) :
    IsKummerFlat D (pullback.snd f g).hom

end WantedExt.AlgebraicGeometry.NativeKummerFlatModels
