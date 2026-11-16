/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EnhancedIndQuotientModels

/-!
# Actual real-parameter projections and addition over an arbitrary base

The ambient double-time space is M times the two original compactified
real lines. Its projections retain the same M-coordinate. The sum map
is defined solely on finite interior real coordinates using the already
constructed native real addition. The remaining graph-properness proof
concerns that exact map and is a separate structural source request.

Source: D'Agnolo--Kashiwara1311.2374v2, Notation4.1.1 and
Definition4.1.2. The compactification and finite-real homeomorphism
are reused from BorderedRealSpaceModels.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BorderedRealTimeModels

open _root_.CategoryTheory TopologicalSpace
open BorderedRealSpaceModels EnhancedIndQuotientModels

variable (M : TopCat.{0})

/-- M with two original bordered real coordinates. -/
def doubleTimeSpace : BorderedSpace :=
  product (fullBordered M) (product infiniteReal infiniteReal)

/-- The actual first real projection over the unchanged original base coordinate. -/
def timeFirst : (doubleTimeSpace M).ambient ⟶ (enhancedSpace M).ambient :=
  TopCat.ofHom ⟨fun p ↦ (p.1, p.2.1), continuous_fst.prodMk (continuous_fst.comp continuous_snd)⟩

/-- The actual second real projection over that same original base coordinate. -/
def timeSecond : (doubleTimeSpace M).ambient ⟶ (enhancedSpace M).ambient :=
  TopCat.ofHom ⟨fun p ↦ (p.1, p.2.2), continuous_fst.prodMk (continuous_snd.comp continuous_snd)⟩

/-- The two finite interior time coordinates, with their original native topology. -/
def finiteTimes : (doubleTimeSpace M).interior ⟶ (product infiniteReal infiniteReal).interior :=
  TopCat.ofHom ⟨fun p ↦ ⟨p.val.2, p.property.2⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩

/-- The source real sum is evaluated exclusively on the finite interior coordinates. -/
def timeSumInterior : (doubleTimeSpace M).interior ⟶ (enhancedSpace M).interior :=
  TopCat.ofHom
    { toFun := fun p ↦
        ⟨(p.val.1, (realAddition (finiteTimes M p)).val), p.property.1,
          (realAddition (finiteTimes M p)).property⟩
      continuous_toFun :=
        ((continuous_fst.comp continuous_subtype_val).prodMk
          (continuous_subtype_val.comp (realAddition.hom.continuous.comp (finiteTimes M).hom.continuous))).subtype_mk _ }

/-- Source graph properness refers only to the original finite real sum over M. -/
structure TimeSumGraphSource : Prop where
  proper : IsProperMap (graphProjection (doubleTimeSpace M) (enhancedSpace M) (timeSumInterior M))

/-- The actual source bordered addition over M. -/
def timeSumBordered (S : TimeSumGraphSource M) : BorderedMap (doubleTimeSpace M) (enhancedSpace M) :=
  ⟨timeSumInterior M, S.proper⟩

/-- The source involution fixes M and negates the original finite time coordinate. -/
def timeNegationInterior : (enhancedSpace M).interior ⟶ (enhancedSpace M).interior :=
  TopCat.ofHom
    { toFun := fun p ↦
        ⟨(p.val.1, (realNegation ⟨p.val.2, p.property.2⟩).val), p.property.1,
          (realNegation ⟨p.val.2, p.property.2⟩).property⟩
      continuous_toFun := by
        have hf : Continuous (fun p : (enhancedSpace M).openSet ↦
            (⟨p.val.2, p.property.2⟩ : infiniteReal.openSet)) :=
          (continuous_snd.comp continuous_subtype_val).subtype_mk _
        exact ((continuous_fst.comp continuous_subtype_val).prodMk
          (continuous_subtype_val.comp (realNegation.hom.continuous.comp hf))).subtype_mk _ }

end MathlibExt.AlgebraicGeometry.BorderedRealTimeModels
