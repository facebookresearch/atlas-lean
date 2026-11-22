/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverMappingFunctor
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Actual source-isomorphism transport of relative marked restrictions

The relative source restriction is the native pullback map whose first
component is the original whole source restriction and whose base-point
component is the identity. Isomorphisms of both actual absolute mapping
restrictions therefore give an isomorphism of this same relative map.
All original projections, source/base maps and points are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace SSet.Marked

/-- The relative marked restriction is literally the native pullback map on the original full restrictions
  and base point. -/
theorem relativeMappingPre_eq_pullbackMap (k : ParameterMarking) {X X' Y Z : Marked.{u}}
    (f : X' ⟶ X) (r : X ⟶ Z) (r' : X' ⟶ Z) (p : Y ⟶ Z) (hf : f ≫ r = r') :
    relativeMappingPre k f r r' p hf =
      pullback.map (mappingComplexPost k X p) (mappingBasePoint k r)
        (mappingComplexPost k X' p) (mappingBasePoint k r')
        (mappingComplexPre k f Y) (𝟙 _) (mappingComplexPre k f Z)
        (mappingComplexPre_post k f p).symm
        (by rw [← mappingBasePoint_pre, hf, Category.id_comp]) := by
  apply pullback.hom_ext
  · exact (relativeMappingPre_fst k f r r' p hf).trans (pullback.lift_fst _ _ _).symm
  · exact (relativeMappingPre_snd k f r r' p hf).trans
      ((Category.comp_id _).symm.trans (pullback.lift_snd _ _ _).symm)

/-- Isomorphisms of the two actual source-restriction legs induce an isomorphism of their same original
  relative pullback restriction. -/
theorem relativeMappingPre_isIso (k : ParameterMarking) {X X' Y Z : Marked.{u}}
    (f : X' ⟶ X) (r : X ⟶ Z) (r' : X' ⟶ Z) (p : Y ⟶ Z) (hf : f ≫ r = r')
    [ht : IsIso (mappingComplexPre k f Y)] [hb : IsIso (mappingComplexPre k f Z)] :
    IsIso (relativeMappingPre k f r r' p hf) := by
  rw [relativeMappingPre_eq_pullbackMap]
  exact @pullback.map_isIso SSet.{u} _ _ _ _ _ _ _
    (mappingComplexPost k X p) (mappingBasePoint k r) inferInstance
    (mappingComplexPost k X' p) (mappingBasePoint k r') inferInstance
    (mappingComplexPre k f Y) (𝟙 _) (mappingComplexPre k f Z)
    (mappingComplexPre_post k f p).symm
    (by rw [← mappingBasePoint_pre, hf, Category.id_comp]) ht inferInstance hb

end SSet.Marked
