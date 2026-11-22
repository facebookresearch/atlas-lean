/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedCofibrationHomMonicity
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerBoundaryFactorization
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCarrierDisjointCoproduct
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictIsoHom
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomArrowRetract

/-!
# Every genuine global Bergner cofibration is monic on all full original Homs

The SAME changing-object boundary factorization first adds the original
target objects by its actual coproduct. The complete original Hom maps
of that inclusion are invertible. Its original fixed-label boundary
inclusion is monic, and the genuine whole enriched lifting retract
retains each complete original Hom arrow.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment

private theorem coefficientMono_of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) (h : IsIso f) :
    Mono f := by
  let _ : IsIso f := h
  infer_instance

private theorem monoHom_of_eq {C D : Carrier.{u}} {F G : C ⟶ D}
    (h : F = G) (x y : C) (hm : Mono (F.map x y)) : Mono (G.map x y) := by
  let t := congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b)
    (congrArg (fun K : C ⟶ D => K.obj x) h) (congrArg (fun K : C ⟶ D => K.obj y) h)
  have he : F.map x y ≫ eqToHom t = G.map x y :=
    EnrichedFunctor.homMap_transport_of_eq h x y
  exact he ▸ mono_comp' hm (inferInstance : Mono (eqToHom t))

/-- The SAME original object-addition inclusion is monic on every complete original source Hom. -/
theorem BergnerObjectAddition.left_hom_mono {C D : Carrier.{u}} (F : C ⟶ D) (x y : C) :
    Mono ((BergnerObjectAddition.left F).map x y) := by
  let E := BergnerFreeObjects.object (D : Type u)
  let c : BinaryCofan C E := BinaryCofan.mk
    (coprod.inl : C ⟶ C ⨿ E) (coprod.inr : E ⟶ C ⨿ E)
  let e := DisjointCoproduct.comparison C E c (coprodIsCoprod C E)
  have hm : Mono ((DisjointCoproduct.inl C E ≫ e.hom).map x y) := by
    change Mono (𝟙 (x ⟶[SSet.{u}] y) ≫
      e.hom.map ((DisjointCoproduct.inl C E).obj x) ((DisjointCoproduct.inl C E).obj y))
    exact mono_comp' (inferInstance : Mono (𝟙 (x ⟶[SSet.{u}] y)))
      (coefficientMono_of_isIso _ (isoHomIso e
        ((DisjointCoproduct.inl C E).obj x) ((DisjointCoproduct.inl C E).obj y)).isIso_hom)
  exact monoHom_of_eq (DisjointCoproduct.inl_comparison C E c (coprodIsCoprod C E)) x y hm

/-- The SAME full original global boundary-factorization left map is monic on every original Hom. -/
theorem Bergner.BoundaryFactorization.left_hom_mono {C D : Carrier.{u}}
    (F : C ⟶ D) (x y : C) : Mono ((Bergner.BoundaryFactorization.data F).i.map x y) := by
  let A := BergnerObjectAddition.object F
  let fixed := CarrierReindexing.fixedPart (BergnerObjectAddition.right F)
  let p := FixedObjects.FreeFactorization.boundary fixed
  have hm := FixedObjects.cofibration_original_hom_mono p.i p.hi
    ((BergnerObjectAddition.left F).obj x) ((BergnerObjectAddition.left F).obj y)
  exact mono_comp' (BergnerObjectAddition.left_hom_mono F x y) hm

/-- Every genuine global C0 cofibration preserves monicity of its SAME full original Hom arrows. -/
theorem Bergner.cofibration_original_hom_mono {C D : Carrier.{u}} (F : C ⟶ D)
    (hF : Bergner.cofibrations F) (x y : C) : Mono (F.map x y) := by
  let p := Bergner.BoundaryFactorization.data F
  let _ : HasLiftingProperty F p.p := hF p.p p.hp
  let r := RetractArrow.ofLeftLiftingProperty p.fac
  exact MorphismProperty.of_retract (P := MorphismProperty.monomorphisms SSet.{u})
    (originalHomArrowRetract r x y)
      (Bergner.BoundaryFactorization.left_hom_mono F (r.i.left.obj x) (r.i.left.obj y))

end CategoryTheory.SimplicialEnrichment
