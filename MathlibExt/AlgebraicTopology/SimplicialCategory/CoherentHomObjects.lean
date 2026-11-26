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
# Mapping objects of coherent realization

An isomorphism of simplicial enrichments induces an isomorphism on every
Hom simplicial set. For a standard simplex, its realization Hom objects
are the nerves of endpoint-containing interval-subset posets, with
Composition induced by union.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment

/-- An enriched-functor equality gives the Hom-map equality with its precise
endpoint transports. -/
theorem enriched_map_of_eq {C D : Carrier.{u}} {F G : C ⟶ D} (h : F = G) (x y : C) :
    F.map x y ≫ eqToHom (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y)
      (congrArg (fun F : C ⟶ D => F.obj x) h) (congrArg (fun F : C ⟶ D => F.obj y) h)) =
        G.map x y :=
  EnrichedFunctor.homMap_transport_of_eq h x y

/-- Both enriched inverse maps read back the identity on the Hom
simplicial set. -/
theorem iso_hom_inv_readback {C D : Carrier.{u}} (e : C ≅ D) (x y : C) :
    (e.hom.map x y ≫ e.inv.map (e.hom.obj x) (e.hom.obj y)) ≫
      eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
        (congrArg (fun F : C ⟶ C => F.obj x) e.hom_inv_id)
        (congrArg (fun F : C ⟶ C => F.obj y) e.hom_inv_id)) = 𝟙 (x ⟶[SSet.{u}] y) :=
  enriched_map_of_eq e.hom_inv_id x y

/-- The coherent-realization name retains the canonical strict Hom isomorphism and its
Maps. -/
abbrev isoHomIso {C D : Carrier.{u}} (e : C ≅ D) (x y : C) :
    (x ⟶[SSet.{u}] y) ≅ (e.hom.obj x ⟶[SSet.{u}] e.hom.obj y) :=
  SimplicialEnrichment.isoHomIso e x y

/-- The realization Hom at two individual standard-simplex vertices is the coherent
 interval-subset nerve. -/
def simplexHomIso (n : SimplexCategory) (i j : Fin (n.len + 1)) :
    hom (SSet.stdSimplex.{u}.obj n)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n i))
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n j)) ≅
        nerve (SimplicialThickening.Path (ULift.up.{u} i) (ULift.up.{u} j)) :=
  isoHomIso (simplexIso n)
    (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n i))
    (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n j))

/-- The mapping-object comparison preserves the enriched composition, which
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
