/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetPullbackBarSource
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetRelativeBaseComparison
public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarSubcomplexUnion

/-!
# Original local-system chains on a subcomplex intersection and union

The canonical original source charts and their actual map square transport
the weighted-bar pushout to the original pulled-back local-system chains.
The relative comparison is the stock cokernel map of this SAME pushout.
Composing it with an actual ambient-cover quotient comparison gives the
coefficient-relative excision map. No relative excision, flatness or chain
calibration is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CategoryHomology
open scoped Simplicial

universe uR uX

namespace SSet

variable {R : Type uR} [CommRing R] {T : SSet.{uX}}

/-- The original coefficient chain map for a subcomplex inclusion over T. -/
public def localCoefficientSubcomplexMap
    (L : SSet.LocalSystem R T) {U V : T.Subcomplex} (h : U ≤ V) :
    localCoefficientChainComplex (L.pullback U.ι) ⟶
      localCoefficientChainComplex (L.pullback V.ι) :=
  localCoefficientChainMapOver (Subcomplex.homOfLE h) V.ι U.ι
    (by rw [Subcomplex.homOfLE_ι]) L

/-- The actual subcomplex map is the original over-base coefficient map,
with its literal inclusion triangle. -/
public theorem localCoefficientSubcomplexMap_eq
    (L : SSet.LocalSystem R T) {U V : T.Subcomplex} (h : U ≤ V) :
    localCoefficientSubcomplexMap L h =
      localCoefficientChainMapOver (Subcomplex.homOfLE h) V.ι U.ι
        (by rw [Subcomplex.homOfLE_ι]) L := by
  unfold localCoefficientSubcomplexMap
  rfl

/-- This is a square of the actual original map and the existing weighted
bar map, including their forced source coefficient transports. -/
public theorem localCoefficientSubcomplexMap_barSource
    (L : SSet.LocalSystem R T) {U V : T.Subcomplex} (h : U ≤ V) :
    localCoefficientSubcomplexMap L h ≫
        (localCoefficientPullbackBarSourceIso V.ι L).hom =
      (localCoefficientPullbackBarSourceIso U.ι L).hom ≫
        nervePullbackCoefficientSubcomplexComplexMap
          (fundamentalGroupoidNerveUnit T) L h := by
  rw [nervePullbackCoefficientSubcomplexComplexMap_base]
  simpa only [localCoefficientSubcomplexMap] using
    localCoefficientChainMapOver_barSource (Subcomplex.homOfLE h)
      V.ι U.ι (by rw [Subcomplex.homOfLE_ι]) L

/-- The original local-system chains of the actual intersection and union
form a pushout. This is derived from the weighted-bar pushout and the FOUR
actual map squares, not a desired excision input. -/
public theorem localCoefficientSubcomplex_isPushout
    (L : SSet.LocalSystem R T) (U V : T.Subcomplex) :
    IsPushout
      (localCoefficientSubcomplexMap L (inf_le_left : U ⊓ V ≤ U))
      (localCoefficientSubcomplexMap L (inf_le_right : U ⊓ V ≤ V))
      (localCoefficientSubcomplexMap L (le_sup_left : U ≤ U ⊔ V))
      (localCoefficientSubcomplexMap L (le_sup_right : V ≤ U ⊔ V)) := by
  let eS := localCoefficientPullbackBarSourceIso (U ⊓ V).ι L
  let eU := localCoefficientPullbackBarSourceIso U.ι L
  let eV := localCoefficientPullbackBarSourceIso V.ι L
  let eB := localCoefficientPullbackBarSourceIso (U ⊔ V).ι L
  let sq := nervePullbackCoefficientSubcomplex_isPushout
    (fundamentalGroupoidNerveUnit T) L U V
  exact sq.of_iso' eS eU eV eB
    (localCoefficientSubcomplexMap_barSource L inf_le_left).symm
    (localCoefficientSubcomplexMap_barSource L inf_le_right).symm
    (localCoefficientSubcomplexMap_barSource L le_sup_left).symm
    (localCoefficientSubcomplexMap_barSource L le_sup_right).symm

/-- The actual relative quotients of the intersection/union pushout are
isomorphic by the stock cokernel universal property. -/
public def localCoefficientSubcomplexRelativeIso
    (L : SSet.LocalSystem R T) (U V : T.Subcomplex) :
    cokernel (localCoefficientSubcomplexMap L (inf_le_left : U ⊓ V ≤ U)) ≅
      cokernel (localCoefficientSubcomplexMap L (le_sup_right : V ≤ U ⊔ V)) := by
  let sq := localCoefficientSubcomplex_isPushout L U V
  let m := cokernel.map _ _ _ _ sq.w
  have hm : IsIso m := isIso_cokernel_map_of_isPushout sq
  exact @asIso _ _ _ _ m hm

/-- The quotient chart has the exact original inclusion/projection square. -/
@[reassoc]
public theorem localCoefficientSubcomplexRelativeIso_π
    (L : SSet.LocalSystem R T) (U V : T.Subcomplex) :
    cokernel.π (localCoefficientSubcomplexMap L (inf_le_left : U ⊓ V ≤ U)) ≫
        (localCoefficientSubcomplexRelativeIso L U V).hom =
      localCoefficientSubcomplexMap L (le_sup_left : U ≤ U ⊔ V) ≫
        cokernel.π (localCoefficientSubcomplexMap L (le_sup_right : V ≤ U ⊔ V)) := by
  let f := localCoefficientSubcomplexMap L (inf_le_left : U ⊓ V ≤ U)
  let g := localCoefficientSubcomplexMap L (inf_le_right : U ⊓ V ≤ V)
  let i := localCoefficientSubcomplexMap L (le_sup_left : U ≤ U ⊔ V)
  let j := localCoefficientSubcomplexMap L (le_sup_right : V ≤ U ⊔ V)
  let sq := localCoefficientSubcomplex_isPushout L U V
  have he : (localCoefficientSubcomplexRelativeIso L U V).hom =
      cokernel.map f j g i sq.w := by rfl
  rw [he]
  exact cokernel.π_desc f (i ≫ cokernel.π j) _

/-- The actual coefficient-relative excision map into the ambient complex:
first the computed union-relative Iso, then the original ambient base map. -/
public def localCoefficientSubcomplexExcisionMap
    (L : SSet.LocalSystem R T) (U V : T.Subcomplex) :
    cokernel (localCoefficientSubcomplexMap L (inf_le_left : U ⊓ V ≤ U)) ⟶
      cokernel (localCoefficientPullbackChainMap V.ι L) :=
  (localCoefficientSubcomplexRelativeIso L U V).hom ≫
    localCoefficientRelativeBaseMap
      (Subcomplex.homOfLE (le_sup_right : V ≤ U ⊔ V))
      (U ⊔ V).ι V.ι (by rw [Subcomplex.homOfLE_ι]) L

/-- The original subcomplex excision map retains the actual ambient
coefficient map and the original quotient projection. The endpoint
identification is proved in the defining owner, without exposing its body. -/
@[reassoc]
public theorem localCoefficientSubcomplexExcisionMap_π
    (L : SSet.LocalSystem R T) (U V : T.Subcomplex) :
    cokernel.π (localCoefficientSubcomplexMap L (inf_le_left : U ⊓ V ≤ U)) ≫
        localCoefficientSubcomplexExcisionMap L U V =
      localCoefficientPullbackChainMap U.ι L ≫
        cokernel.π (localCoefficientPullbackChainMap V.ι L) := by
  let i := localCoefficientSubcomplexMap L (le_sup_left : U ≤ U ⊔ V)
  let j := localCoefficientSubcomplexMap L (le_sup_right : V ≤ U ⊔ V)
  let e := localCoefficientSubcomplexRelativeIso L U V
  let q : cokernel j ⟶ cokernel (localCoefficientPullbackChainMap V.ι L) :=
    localCoefficientRelativeBaseMap
      (Subcomplex.homOfLE (le_sup_right : V ≤ U ⊔ V)) (U ⊔ V).ι V.ι
      (by rw [Subcomplex.homOfLE_ι]) L
  have he := localCoefficientSubcomplexRelativeIso_π L U V
  have hq : cokernel.π j ≫ q = localCoefficientPullbackChainMap (U ⊔ V).ι L ≫
      cokernel.π (localCoefficientPullbackChainMap V.ι L) :=
    localCoefficientRelativeBaseMap_π
      (Subcomplex.homOfLE (le_sup_right : V ≤ U ⊔ V)) (U ⊔ V).ι V.ι
      (by rw [Subcomplex.homOfLE_ι]) L
  have hi : i ≫ localCoefficientPullbackChainMap (U ⊔ V).ι L =
      localCoefficientPullbackChainMap U.ι L := by
    change localCoefficientSubcomplexMap L (le_sup_left : U ≤ U ⊔ V) ≫ _ = _
    rw [localCoefficientSubcomplexMap_eq]
    exact localCoefficientChainMapOver_comp _ _ _ _ L
  change cokernel.π _ ≫ (e.hom ≫ q) = _
  rw [← Category.assoc, he, Category.assoc, hq, ← Category.assoc]
  exact congrArg (fun k => k ≫ cokernel.π (localCoefficientPullbackChainMap V.ι L)) hi

/-- Every coefficient system uses the SAME computed excision map. Only
the actual ambient union comparison is required; a topological two-open
cover derives it separately. No coefficient flatness or desired excision
quasi-isomorphism is assumed. -/
public theorem localCoefficientSubcomplexExcisionMap_quasiIso
    (L : SSet.LocalSystem R T) (U V : T.Subcomplex)
    (hcover : QuasiIso (localCoefficientPullbackChainMap (U ⊔ V).ι L)) :
    QuasiIso (localCoefficientSubcomplexExcisionMap L U V) := by
  let e : cokernel (localCoefficientSubcomplexMap L (inf_le_left : U ⊓ V ≤ U)) ≅
      cokernel (localCoefficientSubcomplexMap L (le_sup_right : V ≤ U ⊔ V)) :=
    localCoefficientSubcomplexRelativeIso L U V
  let q : cokernel (localCoefficientSubcomplexMap L (le_sup_right : V ≤ U ⊔ V)) ⟶
      cokernel (localCoefficientPullbackChainMap V.ι L) := localCoefficientRelativeBaseMap
      (Subcomplex.homOfLE (le_sup_right : V ≤ U ⊔ V))
      (U ⊔ V).ι V.ι (by rw [Subcomplex.homOfLE_ι]) L
  let : IsIso e.hom := e.isIso_hom
  let : QuasiIso e.hom := _root_.quasiIso_of_isIso e.hom
  let : QuasiIso q :=
    localCoefficientRelativeBaseMap_quasiIso _ _ _ _ L hcover
  have hcomp : QuasiIso (e.hom ≫ q) := _root_.quasiIso_comp e.hom q
  have he : localCoefficientSubcomplexExcisionMap L U V = e.hom ≫ q := rfl
  exact he.symm ▸ hcomp

end SSet

end
