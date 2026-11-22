/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceAllMaps
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceConcatenationPushout

/-!
# Same original native concatenation maps

Both whole original necklace maps glue through the genuine native
pushout. The map retains the SAME complete prefix and suffix vertex
operators, original endpoints and every full original source map.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open OriginalTwoBead.OrdinalCharts

/-- The complete original prefix inclusion retains EVERY original vertex. -/
theorem concatLeft_vertex (T U : Data) (i : Fin (T.dimension + 1)) :
    vertexMap.{u} T.joints i ≫ concatLeft T U =
      vertexMap (T.concat U).joints (prefixEmbedding T.dimension U.dimension i) := by
  apply (cancel_mono (complex.{u} (T.concat U).joints).ι).1
  rw [Category.assoc, concatLeft_ι, ← Category.assoc, vertexMap_ι, vertexMap_ι,
    ← SSet.stdSimplex.map_comp]
  rfl

/-- The complete original suffix inclusion retains EVERY original vertex. -/
theorem concatRight_vertex (T U : Data) (i : Fin (U.dimension + 1)) :
    vertexMap.{u} U.joints i ≫ concatRight T U =
      vertexMap (T.concat U).joints (suffix T.dimension U.dimension i) := by
  apply (cancel_mono (complex.{u} (T.concat U).joints).ι).1
  rw [Category.assoc, concatRight_ι, ← Category.assoc, vertexMap_ι, vertexMap_ι,
    ← SSet.stdSimplex.map_comp]
  rfl

variable {T T' U U' : Data} (f : T ⟶ T') (g : U ⟶ U')

/-- Both entire original maps agree at the SAME original pivot before their native gluing. -/
theorem concatMap_square :
    T.target.{u} ≫ (f.map ≫ concatLeft T' U') = U.source ≫ (g.map ≫ concatRight T' U') := by
  rw [← Category.assoc, target_map, ← Category.assoc, source_map]
  exact concat_square T' U'

/-- The whole actual original native map on both concatenated necklaces. -/
def concatMap : (T.concat U).object.{u} ⟶ (T'.concat U').object :=
  concatInput T U (f.map ≫ concatLeft T' U') (g.map ≫ concatRight T' U') (concatMap_square f g)

/-- The SAME native concatenation map reads back the complete first original map. -/
theorem concatLeft_map : concatLeft.{u} T U ≫ concatMap f g = f.map ≫ concatLeft T' U' :=
  concatLeft_input _ _ _ _ _

/-- The SAME native concatenation map reads back the complete second original map. -/
theorem concatRight_map : concatRight.{u} T U ≫ concatMap f g = g.map ≫ concatRight T' U' :=
  concatRight_input _ _ _ _ _

/-- The whole original concatenation map preserves its SAME original initial vertex. -/
theorem concatMap_source : (T.concat U).source.{u} ≫ concatMap f g = (T'.concat U').source := by
  rw [← concatLeft_source T U, Category.assoc, concatLeft_map, ← Category.assoc, source_map,
    concatLeft_source]

/-- The whole original concatenation map preserves its SAME original terminal vertex. -/
theorem concatMap_target : (T.concat U).target.{u} ≫ concatMap f g = (T'.concat U').target := by
  rw [← concatRight_target T U, Category.assoc, concatRight_map, ← Category.assoc, target_map,
    concatRight_target]

/-- The SAME original pointed native map as its actual original necklace morphism. -/
def concatMapMorphism : Morphism (T.concat U) (T'.concat U') :=
  Morphism.ofMap (concatMap.{u} f g) (concatMap_source f g) (concatMap_target f g)

/-- The whole original necklace morphism reads precisely the SAME supplied concatenation map. -/
theorem concatMapMorphism_map : (concatMapMorphism.{u} f g).map.{u} = concatMap f g :=
  Morphism.ofMap_map _ _ _

/-- Every original first-bead vertex has its SAME original prefix operator formula after gluing. -/
theorem concatMapMorphism_prefix (i : Fin (T.dimension + 1)) :
    (concatMapMorphism.{u} f g).operator.toOrderHom (prefixEmbedding T.dimension U.dimension i) =
      prefixEmbedding T'.dimension U'.dimension (f.operator.toOrderHom i) := by
  apply (vertexMap_injective.{u} (T'.concat U'))
  rw [← Morphism.vertex_map, concatMapMorphism_map, ← concatLeft_vertex T U i,
    Category.assoc, concatLeft_map, ← Category.assoc, Morphism.vertex_map, concatLeft_vertex]

/-- Every original second-bead vertex has its SAME original suffix operator formula after gluing. -/
theorem concatMapMorphism_suffix (i : Fin (U.dimension + 1)) :
    (concatMapMorphism.{u} f g).operator.toOrderHom (suffix T.dimension U.dimension i) =
      suffix T'.dimension U'.dimension (g.operator.toOrderHom i) := by
  apply (vertexMap_injective.{u} (T'.concat U'))
  rw [← Morphism.vertex_map, concatMapMorphism_map, ← concatRight_vertex T U i,
    Category.assoc, concatRight_map, ← Category.assoc, Morphism.vertex_map, concatRight_vertex]

end SSet.OriginalNecklace
