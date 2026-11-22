/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomPrecompositionComponents
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomMaps

/-!
# The SAME original full precomposition square on fixed Hom labels

Only the actual original object equalities transport the complete Hom
precomposition action. The original enriched-functor law and these full
transport squares retain the SAME original coefficient and every scalar
operator. No weak Hom or component-invertibility outcome is supplied.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomPrecomposition
variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- Original endpoint equalities retain the SAME whole precomposition coefficient square. -/
theorem pre_endpoint_transport {x y z x' y' z' : C}
    (hx : x = x') (hy : y = y') (hz : z = z')
    (q : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    pre z q ≫ eqToHom (congrArg₂ (fun s t : C => s ⟶[SSet.{u}] t) hx hz) =
      eqToHom (congrArg₂ (fun s t : C => s ⟶[SSet.{u}] t) hy hz) ≫
        pre z' (q ≫ eqToHom (congrArg₂ (fun s t : C => s ⟶[SSet.{u}] t) hx hy)) := by
  cases hx
  cases hy
  cases hz
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

end CategoryTheory.SimplicialEnrichment.EnrichedHomPrecomposition

namespace CategoryTheory.SimplicialEnrichment.FixedObjects
open EnrichedHomPrecomposition EnrichedHomActionNaturality
variable {O : Type u} {P A : FixedObjects O}

/-- Each SAME original full fixed-label Hom map preserves the actual original precomposition coefficient square. -/
theorem pre_homMap_natural (F : P ⟶ A) (x y z : O)
    (q : 𝟙_ SSet.{u} ⟶ hom P x y) :
    pre (vertex P z) q ≫ homMap F x z =
      homMap F y z ≫ pre (vertex A z) (q ≫ homMap F x y) := by
  let q' := q ≫ F.val.map (vertex P x) (vertex P y)
  let E (a b : O) := eqToHom (congrArg₂ (fun s t : A.val => s ⟶[SSet.{u}] t)
    (map_vertex F a) (map_vertex F b))
  have hn := pre_natural F.val (vertex P z) q
  have ht := pre_endpoint_transport (map_vertex F x) (map_vertex F y) (map_vertex F z) q'
  have h := (congrArg (fun k => k ≫ E x z) hn).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => F.val.map (vertex P y) (vertex P z) ≫ k) ht).trans
        (Category.assoc _ _ _).symm))
  simpa only [q', E, homMap, Category.assoc] using h

end CategoryTheory.SimplicialEnrichment.FixedObjects
