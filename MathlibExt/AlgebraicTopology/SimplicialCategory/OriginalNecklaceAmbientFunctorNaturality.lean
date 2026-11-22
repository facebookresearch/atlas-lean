/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceAmbientHom
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentPointedHomMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceCoefficientFunctor

/-!
# The SAME full native ambient functor naturality

Every original native necklace map retains its complete ambient simplex
square and both original vertices. The SAME realization and standard
simplex Iso give the whole enriched functor equality; no weak outcome
or desired Hom identification is supplied.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace SimplicialEnrichment

variable {T U : Data}

/-- Every SAME original native map retains its literal source vertex equation. -/
theorem nativeMap_source (f : T ⟶ U) :
    f.map.{u}.app (op ⦋0⦌) (sourceVertex T) = sourceVertex U :=
  (SSet.yonedaEquiv_comp T.source f.map.{u}).symm.trans
    (congrArg SSet.yonedaEquiv (source_map f))

/-- Every SAME original native map retains its literal target vertex equation. -/
theorem nativeMap_target (f : T ⟶ U) :
    f.map.{u}.app (op ⦋0⦌) (targetVertex T) = targetVertex U :=
  (SSet.yonedaEquiv_comp T.target f.map.{u}).symm.trans
    (congrArg SSet.yonedaEquiv (target_map f))

/-- The complete SAME original native map on the whole endpoint-specified raw realized Hom. -/
def nativeHomMap (f : T ⟶ U) :
    hom T.object.{u} (sourceVertex T) (targetVertex T) ⟶
      hom U.object.{u} (sourceVertex U) (targetVertex U) :=
  pointedHomMap f.map.{u} (nativeMap_source f) (nativeMap_target f)

/-- EVERY whole original native ambient simplex square retains the SAME entire realized functor square. -/
theorem ambientFunctor_square (T U : Data) (f : T.object.{u} ⟶ U.object.{u})
    (φ : ⦋T.dimension⦌ ⟶ ⦋U.dimension⦌)
    (hsq : f ≫ (complex.{u} U.joints).ι = (complex.{u} T.joints).ι ≫ SSet.stdSimplex.map φ) :
    realizationMap f ≫ ambientFunctor U = ambientFunctor T ≫ coherentSimplexMap φ := by
  have h := congrArg (fun e : T.object.{u} ⟶ (Δ[U.dimension] : SSet.{u}) => realizationMap e) hsq
  rw [realizationMap_comp, realizationMap_comp] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun e => e ≫ (simplexIso.{u} ⦋U.dimension⦌).hom) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun e => realizationMap (complex.{u} T.joints).ι ≫ e)
          (simplexIso_naturality φ)).trans (Category.assoc _ _ _).symm)))

/-- The SAME whole enriched ambient functor square retains the original native operator map. -/
theorem ambientFunctor_native (f : T ⟶ U) :
    realizationMap f.map.{u} ≫ ambientFunctor U = ambientFunctor T ≫ coherentSimplexMap f.operator :=
  ambientFunctor_square T U f.map f.operator (Morphism.map_ι f)

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
