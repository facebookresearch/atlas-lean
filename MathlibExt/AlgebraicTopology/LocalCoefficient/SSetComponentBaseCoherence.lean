/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ComponentBaseMap
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetComponentCofan

/-!
# Original coefficient squares on existing components

The component map is the original local-system map over the SAME ambient
coefficient base. Its whole square is forced by the existing actual
component inclusion identity and original over-base composition law.
No component coefficient or chain-map calibration is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe uR uX

namespace SSet

variable {R : Type uR} [CommRing R] {X Y : SSet.{uX}}

/-- The actual original coefficient map on a source component, written
over the target ambient coefficient base before composing inclusions. -/
public abbrev localCoefficientComponentBaseMapOver
    (f : X ⟶ Y) (c : π₀ X) (L : SSet.LocalSystem R Y) :
    localCoefficientChainComplex (L.pullback ((π₀.component c).ι ≫ f)) ⟶
      localCoefficientComponentComplex Y L (mapπ₀ f c) :=
  localCoefficientChainMapOver (componentBaseMap f c)
    (π₀.component (mapπ₀ f c)).ι ((π₀.component c).ι ≫ f)
    (componentBaseMap_ι f c).symm L

/-- The component coefficient map and inclusion give the SAME original
ambient map, as a WHOLE chain-map equation. -/
@[reassoc]
public theorem localCoefficientComponentBaseMapOver_comp
    (f : X ⟶ Y) (c : π₀ X) (L : SSet.LocalSystem R Y) :
    localCoefficientComponentBaseMapOver f c L ≫
        localCoefficientComponentInclusion Y L (mapπ₀ f c) =
      localCoefficientPullbackChainMap ((π₀.component c).ι ≫ f) L :=
  localCoefficientChainMapOver_comp (componentBaseMap f c)
    (π₀.component (mapπ₀ f c)).ι ((π₀.component c).ι ≫ f)
    (componentBaseMap_ι f c).symm L

/-- The ACTUAL source component system is transported through the
existing original pullback-composition Iso, retaining its full map square. -/
public theorem localCoefficientComponentBaseMapOver_original_square
    (f : X ⟶ Y) (c : π₀ X) (L : SSet.LocalSystem R Y) :
    localCoefficientChainMap (LocalSystem.pullbackCompIso
        (π₀.component c).ι f L).hom ≫
      localCoefficientComponentInclusion X (L.pullback f) c ≫
      localCoefficientPullbackChainMap f L =
    localCoefficientComponentBaseMapOver f c L ≫
      localCoefficientComponentInclusion Y L (mapπ₀ f c) := by
  rw [localCoefficientComponentBaseMapOver_comp]
  exact (localCoefficientPullbackChainMap_comp (π₀.component c).ι f L).symm

/-- The ACTUAL component coefficient base map from iterated source
pullback, using the inverse of the existing pullback-composition Iso. -/
public abbrev localCoefficientComponentBaseMap
    (f : X ⟶ Y) (c : π₀ X) (L : SSet.LocalSystem R Y) :
    localCoefficientComponentComplex X (L.pullback f) c ⟶
      localCoefficientComponentComplex Y L (mapπ₀ f c) :=
  localCoefficientChainMap (LocalSystem.pullbackCompIso
      (π₀.component c).ι f L).inv ≫
    localCoefficientComponentBaseMapOver f c L

/-- The actual component map commutes with the original ambient base map,
including the source pullback-composition transport. -/
@[reassoc]
public theorem localCoefficientComponentBaseMap_comp
    (f : X ⟶ Y) (c : π₀ X) (L : SSet.LocalSystem R Y) :
    localCoefficientComponentBaseMap f c L ≫
        localCoefficientComponentInclusion Y L (mapπ₀ f c) =
      localCoefficientComponentInclusion X (L.pullback f) c ≫
        localCoefficientPullbackChainMap f L := by
  let E := LocalSystem.pullbackCompIso (π₀.component c).ι f L
  let a := localCoefficientChainMap E.hom
  let b := localCoefficientChainMap E.inv
  have hb : b ≫ a = 𝟙 (localCoefficientComponentComplex X (L.pullback f) c) := by
    calc
      _ = localCoefficientChainMap (E.inv ≫ E.hom) :=
        (localCoefficientChainMap_comp E.inv E.hom).symm
      _ = localCoefficientChainMap (𝟙 _) := congrArg localCoefficientChainMap E.inv_hom_id
      _ = _ := localCoefficientChainMap_id
  let sx := localCoefficientComponentInclusion X (L.pullback f) c
  let tf := localCoefficientPullbackChainMap f L
  let co := localCoefficientComponentBaseMapOver f c L
  let sy := localCoefficientComponentInclusion Y L (mapπ₀ f c)
  have h0 : a ≫ (sx ≫ tf) = co ≫ sy :=
    localCoefficientComponentBaseMapOver_original_square f c L
  change (b ≫ co) ≫ sy = sx ≫ tf
  calc
    (b ≫ co) ≫ sy = b ≫ (co ≫ sy) := Category.assoc b co sy
    _ = b ≫ (a ≫ (sx ≫ tf)) := congrArg (fun k => b ≫ k) h0.symm
    _ = (b ≫ a) ≫ (sx ≫ tf) := (Category.assoc b a (sx ≫ tf)).symm
    _ = sx ≫ tf := by rw [hb, Category.id_comp]

/-- The WHOLE original component coproduct base map retains every actual
restricted component map and its original target index mapπ₀ f. -/
public def localCoefficientComponentCoproductBaseMap
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) :
    (∐ fun c : π₀ X => localCoefficientComponentComplex X (L.pullback f) c) ⟶
      (∐ fun d : π₀ Y => localCoefficientComponentComplex Y L d) :=
  Sigma.map' (f := fun d => localCoefficientComponentComplex Y L d)
    (g := fun c => localCoefficientComponentComplex X (L.pullback f) c)
    (mapπ₀ f) (fun c => localCoefficientComponentBaseMap f c L)

/-- The complete coproduct square identifies the SAME original ambient
coefficient pullback chain map. No carrier-only inference is used. -/
public theorem localCoefficientComponentCoproductBaseMap_square
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) :
    localCoefficientComponentCoproductBaseMap f L ≫
        localCoefficientComponentCoproductMap Y L =
      localCoefficientComponentCoproductMap X (L.pullback f) ≫
        localCoefficientPullbackChainMap f L := by
  apply Sigma.hom_ext
  intro c
  simp only [localCoefficientComponentCoproductBaseMap,
    Sigma.ι_comp_map'_assoc, localCoefficientComponentCoproductMap_ι_assoc,
    localCoefficientComponentCoproductMap_ι]
  exact localCoefficientComponentBaseMap_comp f c L

end SSet

end
