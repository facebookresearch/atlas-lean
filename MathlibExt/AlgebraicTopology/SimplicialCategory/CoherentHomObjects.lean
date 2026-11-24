/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRepresentables
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictIsoHom

/-!
# The actual coherent realization mapping objects

A strict enriched isomorphism induces a genuine isomorphism on each
whole original Hom simplicial set. Applied to the proved standard-simplex
comparison, this identifies the actual realization Hom objects with the
original endpoint-containing interval-subset nerves, including all
scalar degrees and the original enriched composition.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment

/-- A whole enriched-functor equality gives the actual Hom-map equality with its precise
endpoint transports. -/
theorem enriched_map_of_eq {C D : Carrier.{u}} {F G : C ⟶ D} (h : F = G) (x y : C) :
    F.map x y ≫ eqToHom (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y)
      (congrArg (fun F : C ⟶ D => F.obj x) h) (congrArg (fun F : C ⟶ D => F.obj y) h)) =
        G.map x y :=
  functorHom_congr h x y

/-- Both actual enriched inverse maps read back the identity on the entire original Hom
simplicial set. -/
theorem iso_hom_inv_readback {C D : Carrier.{u}} (e : C ≅ D) (x y : C) :
    (e.hom.map x y ≫ e.inv.map (e.hom.obj x) (e.hom.obj y)) ≫
      eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
        (congrArg (fun F : C ⟶ C => F.obj x) e.hom_inv_id)
        (congrArg (fun F : C ⟶ C => F.obj y) e.hom_inv_id)) = 𝟙 (x ⟶[SSet.{u}] y) :=
  enriched_map_of_eq e.hom_inv_id x y

/-- The coherent-realization name retains the canonical whole strict Hom isomorphism and its
original maps. -/
abbrev isoHomIso {C D : Carrier.{u}} (e : C ≅ D) (x y : C) :
    (x ⟶[SSet.{u}] y) ≅ (e.hom.obj x ⟶[SSet.{u}] e.hom.obj y) :=
  SimplicialEnrichment.isoHomIso e x y

/-- The actual realization Hom at two individual standard-simplex vertices is the original coherent
  interval-subset nerve. -/
def simplexHomIso (n : SimplexCategory) (i j : Fin (n.len + 1)) :
    hom (SSet.stdSimplex.{u}.obj n)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n i))
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n j)) ≅
        nerve (SimplicialThickening.Path (ULift.up.{u} i) (ULift.up.{u} j)) :=
  isoHomIso (simplexIso n)
    (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n i))
    (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n j))

/-- The mapping-object comparison preserves the entire original enriched composition, which
is coherent-path union. -/
theorem simplexHomIso_comp (n : SimplexCategory) (i j k : Fin (n.len + 1)) :
    eComp SSet.{u} (C := realization (SSet.stdSimplex.obj n))
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n i))
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n j))
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n k)) ≫ (simplexHomIso n i k).hom =
        ((simplexHomIso n i j).hom ⊗ₘ (simplexHomIso n j k).hom) ≫
          eComp SSet.{u} (C := coherentSimplex n)
            (SimplicialThickening.mk (ULift.up i)) (SimplicialThickening.mk (ULift.up j))
            (SimplicialThickening.mk (ULift.up k)) :=
  (simplexIso n).hom.map_comp _ _ _

end CategoryTheory.CoherentRealization
