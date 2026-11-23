/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ComponentBaseMap
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ComponentUnionWeakRestriction

/-!
# The original weak map on arbitrary simplicial components

The canonical component-union preimage restriction is weak without an
ambient Kan hypothesis. Its exact singleton identifications and original
inclusion square identify it with the original `componentBaseMap`.

The realization and singular-realization equations below retain the actual
original maps. No coefficient-unit quasi-isomorphism or chosen weak model
is used.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace SSet

/-- The actual singleton preimage restriction is the SAME original
component map under its two canonical subcomplex identifications. -/
public def componentBaseMapRestrictionIso
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : realizationWeakEquivalences f) (c : π₀ X) :
    Arrow.mk (componentUnionPreimageMap f {mapπ₀ f c}) ≅
      Arrow.mk (componentBaseMap f c) := by
  let r := componentUnionPreimageMap f {mapπ₀ f c}
  let eS := componentUnionPreimageSourceSingletonIso f hf c
  let eT := componentUnionPreimageTargetSingletonIso f c
  have hs : eS.hom ≫ componentBaseMap f c = r ≫ eT.hom := by
    apply (cancel_mono (π₀.component (mapπ₀ f c)).ι).mp
    calc
      (eS.hom ≫ componentBaseMap f c) ≫ (π₀.component (mapπ₀ f c)).ι =
          eS.hom ≫ ((π₀.component c).ι ≫ f) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => eS.hom ≫ k) (componentBaseMap_ι f c))
      _ = r ≫ eT.hom ≫ (π₀.component (mapπ₀ f c)).ι :=
        (componentUnionPreimageMap_singleton_ι f hf c).symm
      _ = (r ≫ eT.hom) ≫ (π₀.component (mapπ₀ f c)).ι :=
        (Category.assoc _ _ _).symm
  exact Arrow.isoMk eS eT hs

/-- The SAME original component map is weak for arbitrary simplicial
sources and targets; neither ambient object is assumed Kan. -/
public theorem realizationWeakEquivalences_componentBaseMap
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : realizationWeakEquivalences f)
    (c : π₀ X) : realizationWeakEquivalences (componentBaseMap f c) :=
  (realizationWeakEquivalences.arrow_mk_iso_iff
    (componentBaseMapRestrictionIso f hf c)).mp
      (componentUnionPreimageMap_weak f {mapπ₀ f c} hf)

/-- Realization retains the WHOLE original component-inclusion square. -/
@[reassoc]
public theorem componentBaseMap_realization_originalSquare
    {X Y : SSet.{u}} (f : X ⟶ Y) (c : π₀ X) :
    toTop.map (componentBaseMap f c) ≫ toTop.map (π₀.component (mapπ₀ f c)).ι =
      toTop.map (π₀.component c).ι ≫ toTop.map f :=
  (toTop.map_comp _ _).symm.trans
    ((congrArg toTop.map (componentBaseMap_ι f c)).trans (toTop.map_comp _ _))

/-- The ACTUAL singular-realization map retains that same square. -/
@[reassoc]
public theorem componentBaseMap_singularRealization_originalSquare
    {X Y : SSet.{u}} (f : X ⟶ Y) (c : π₀ X) :
    TopCat.toSSet.map (toTop.map (componentBaseMap f c)) ≫
        TopCat.toSSet.map (toTop.map (π₀.component (mapπ₀ f c)).ι) =
      TopCat.toSSet.map (toTop.map (π₀.component c).ι) ≫
        TopCat.toSSet.map (toTop.map f) :=
  (TopCat.toSSet.map_comp _ _).symm.trans
    ((congrArg TopCat.toSSet.map (componentBaseMap_realization_originalSquare f c)).trans
      (TopCat.toSSet.map_comp _ _))

end SSet

end
