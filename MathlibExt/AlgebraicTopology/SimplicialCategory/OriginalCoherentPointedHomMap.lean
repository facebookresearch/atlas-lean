/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentFullHomMonicity
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedEqualityTransport
import MathlibExt.CategoryTheory.Enriched.HomEndpointMaps

/-!
# The SAME full original raw Hom map with literal endpoint equations

An actual simplicial map and its two genuine original vertex equations
induce the SAME original realized Hom map. Exact equality transports
retain the full original Hom, identities, coefficients and monicity.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization

open SimplicialEnrichment

/-- The SAME entire original realized Hom map with both supplied original vertex equations. -/
def pointedHomMap {K L : SSet.{u}} (f : K ⟶ L) {x y : K _⦋0⦌} {x' y' : L _⦋0⦌}
    (hx : f.app (op ⦋0⦌) x = x') (hy : f.app (op ⦋0⦌) y = y') : hom K x y ⟶ hom L x' y' :=
  EnrichedFunctor.homMap (realizationMap f) hx hy

/-- Every actual original input mono remains monic on the SAME whole endpoint-specified raw Hom. -/
theorem pointedHomMap_mono {K L : SSet.{u}} (f : K ⟶ L) [Mono f]
    {x y : K _⦋0⦌} {x' y' : L _⦋0⦌}
    (hx : f.app (op ⦋0⦌) x = x') (hy : f.app (op ⦋0⦌) y = y') : Mono (pointedHomMap f hx hy) := by
  have hE : Mono (EqualityTransport.hom (C := realization L) hx hy) := by
    unfold EqualityTransport.hom
    infer_instance
  exact mono_comp' (realizationMap_full_hom_mono f x y) hE

/-- EVERY same original coherent generator retains its entire source-map image and original endpoint equations. -/
theorem pointedHomMap_simplexHom {K L : SSet.{u}} (f : K ⟶ L) {n : SimplexCategory}
    (σ : K.obj (op n)) (i j : coherentSimplex.{u} n) {x y : K _⦋0⦌} {x' y' : L _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y)
    (hfx : f.app (op ⦋0⦌) x = x') (hfy : f.app (op ⦋0⦌) y = y') :
    simplexHom K σ i j hx hy ≫ pointedHomMap f hfx hfy =
      simplexHom L (f.app (op n) σ) i j ((vertex_image f σ i hx).trans hfx)
        ((vertex_image f σ j hy).trans hfy) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun e => e ≫ EqualityTransport.hom (C := realization L) hfx hfy)
      (realizationMap_simplexHom f σ i j hx hy)).trans
        (simplexHom_reindex_comp L (f.app (op n) σ) i j
          (vertex_image f σ i hx) (vertex_image f σ j hy) hfx hfy))

/-- The SAME endpoint-specified raw Hom map retains the whole original identity. -/
theorem pointedHomMap_identity {K L : SSet.{u}} (f : K ⟶ L) {x : K _⦋0⦌} {x' : L _⦋0⦌}
    (hx : f.app (op ⦋0⦌) x = x') :
    eId SSet.{u} (C := realization K) x ≫ pointedHomMap f hx hx = eId SSet.{u} (C := realization L) x' :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun e => e ≫ EqualityTransport.hom (C := realization L) hx hx)
      ((realizationMap f).map_id x)).trans (EqualityTransport.identity hx))

/-- Both actual full original raw Hom factors retain the same three supplied endpoint equations. -/
theorem pointedHomMap_composition {K L : SSet.{u}} (f : K ⟶ L)
    {x y z : K _⦋0⦌} {x' y' z' : L _⦋0⦌}
    (hx : f.app (op ⦋0⦌) x = x') (hy : f.app (op ⦋0⦌) y = y') (hz : f.app (op ⦋0⦌) z = z') :
    eComp SSet.{u} (C := realization K) x y z ≫ pointedHomMap f hx hz =
      (pointedHomMap f hx hy ⊗ₘ pointedHomMap f hy hz) ≫ eComp SSet.{u} (C := realization L) x' y' z' :=
  EqualityTransport.composition_retarget (A := realization K) x y z hx hy hz
    ((realizationMap f).map x y) ((realizationMap f).map y z) ((realizationMap f).map x z)
      ((realizationMap f).map_comp x y z)

/-- The SAME whole original source-map equality retains its full original pointed Hom maps. -/
theorem pointedHomMap_eq {K L : SSet.{u}} {f g : K ⟶ L} (h : f = g)
    {x y : K _⦋0⦌} {x' y' : L _⦋0⦌}
    (hx : f.app (op ⦋0⦌) x = x') (hy : f.app (op ⦋0⦌) y = y')
    (hx' : g.app (op ⦋0⦌) x = x') (hy' : g.app (op ⦋0⦌) y = y') :
    pointedHomMap f hx hy = pointedHomMap g hx' hy' :=
  EnrichedFunctor.homMap_eq (congrArg realizationMap h) hx hy hx' hy'

/-- BOTH same actual original pointed source maps compose with their literal original endpoint equations. -/
theorem pointedHomMap_comp {K L M : SSet.{u}} (f : K ⟶ L) (g : L ⟶ M)
    {x y : K _⦋0⦌} {x' y' : L _⦋0⦌} {x'' y'' : M _⦋0⦌}
    (hx : f.app (op ⦋0⦌) x = x') (hy : f.app (op ⦋0⦌) y = y')
    (ha : g.app (op ⦋0⦌) x' = x'') (hb : g.app (op ⦋0⦌) y' = y'') :
    pointedHomMap f hx hy ≫ pointedHomMap g ha hb =
      pointedHomMap (f ≫ g) ((congrArg (fun v => g.app (op ⦋0⦌) v) hx).trans ha)
        ((congrArg (fun v => g.app (op ⦋0⦌) v) hy).trans hb) :=
  (EnrichedFunctor.homMap_comp (realizationMap f) (realizationMap g) hx hy ha hb).trans
    (EnrichedFunctor.homMap_eq (realizationMap_comp f g).symm
      ((congrArg (realizationMap g).obj hx).trans ha) ((congrArg (realizationMap g).obj hy).trans hb)
      ((congrArg (fun v => g.app (op ⦋0⦌) v) hx).trans ha)
      ((congrArg (fun v => g.app (op ⦋0⦌) v) hy).trans hb))

end CategoryTheory.CoherentRealization
