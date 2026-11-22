/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PointedRightMappingSpace
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightMappingTrivialFibrations

/-!
# Actual trivial-fibration preservation on the two-pointed carrier

Endpoint equalities identify the entire pointed mapping-space map with
the original same-map right mapping functor. The proved original boundary
lifting then preserves genuine trivial fibrations, with no condition on
whether the two supplied endpoint vertices coincide.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.PointedRightMappingSpace

/-- The whole pointed mapping map is the same original right mapping map followed only by the two proved
  endpoint equalities. -/
theorem map_eq_raw {P Q : Under endpointPair.{u}} (f : P ⟶ Q) :
    functor.map f = mappingSpaceRight.map P.right (sourceVertex P) (targetVertex P) f.right ≫
      (endpointIso (sourceVertex_map f) (targetVertex_map f)).hom := by
  ext n σ
  apply Subtype.ext
  exact (map_val f n σ).trans
    (endpointIso_hom_val (sourceVertex_map f) (targetVertex_map f) n
      ((mappingSpaceRight.map P.right (sourceVertex P) (targetVertex P) f.right).app n σ)).symm

/-- The entire pointed map is isomorphic as an arrow to the same original unwrapped right mapping-space map. -/
def mapArrowIso {P Q : Under endpointPair.{u}} (f : P ⟶ Q) :
    Arrow.mk (functor.map f) ≅
      Arrow.mk (mappingSpaceRight.map P.right (sourceVertex P) (targetVertex P) f.right) :=
  Arrow.isoMk (Iso.refl (object P)) (endpointIso (sourceVertex_map f) (targetVertex_map f)).symm (by
    let e := endpointIso (sourceVertex_map f) (targetVertex_map f)
    let g := mappingSpaceRight.map P.right (sourceVertex P) (targetVertex P) f.right
    change (𝟙 (object P)) ≫ g = functor.map f ≫ e.inv
    have h := congrArg (fun k : object P ⟶ object Q => k ≫ e.inv) (map_eq_raw f)
    have hc : (g ≫ e.hom) ≫ e.inv = g :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun k => g ≫ k) e.hom_inv_id).trans (Category.comp_id _))
    exact (Category.id_comp g).trans (h.trans hc).symm)

/-- The genuine pointed right mapping functor preserves the full original boundary RLP of a trivial fibration. -/
theorem map_mem_I_rlp {P Q : Under endpointPair.{u}} (f : P ⟶ Q)
    (hf : modelCategoryQuillen.I.rlp f.right) :
    modelCategoryQuillen.I.rlp (functor.map f) :=
  (modelCategoryQuillen.I.rlp.arrow_mk_iso_iff (mapArrowIso f)).mpr
    (mappingSpaceRight.map_mem_I_rlp hf (sourceVertex P) (targetVertex P))

end SSet.PointedRightMappingSpace
