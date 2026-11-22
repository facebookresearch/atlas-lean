/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentEdgeLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRelativeFullBoundaryLift

/-!
# The actual original degree-one coherent boundary lift

The two complete original zero faces give the individual source and
target objects. Original Hom boundary lifting constructs the SAME
whole enriched edge and retains both supplied boundary maps.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RelativeCoherentOneBoundary
open SimplicialEnrichment HomMappingCells

variable {C D : Carrier.{u}} (F : C ⟶ D)
  (f : (∂Δ[1] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (σ : coherentSimplex.{u} ⦋1⦌ ⟶ D)
  (sq : CommSq f (SSet.boundary.{u} 1).ι (coherentNerveFunctor.map F) (SSet.yonedaEquiv.symm σ))

/-- The complete original zero face at either same original boundary label. -/
def faceFunctor (j : Fin 2) : coherentSimplex.{u} ⦋0⦌ ⟶ C :=
  SSet.yonedaEquiv (SSet.boundary.ι j ≫ f)

/-- The individual original source object read from its supplied complete first face. -/
def source : C := verticesEquiv C (faceFunctor f 1)

/-- The individual original target object read from its supplied complete last face. -/
def target : C := verticesEquiv C (faceFunctor f 0)

include sq in
/-- The original boundary square identifies the whole image of both supplied zero faces. -/
theorem face_image (j : Fin 2) :
    faceFunctor f j ≫ F = coherentSimplexMap (SimplexCategory.δ j) ≫ σ := by
  have hJ : (SSet.boundary.ι j ≫ f) ≫ coherentNerveFunctor.map F =
      SSet.stdSimplex.δ j ≫
        (SSet.yonedaEquiv (X := coherentNerveFunctor.obj D) (n := ⦋1⦌)).symm σ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => SSet.boundary.ι j ≫ q) sq.w).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun q => q ≫
            (SSet.yonedaEquiv (X := coherentNerveFunctor.obj D) (n := ⦋1⦌)).symm σ)
              (SSet.boundary.ι_ι j))))
  have hY := (SSet.yonedaEquiv_comp (SSet.boundary.ι j ≫ f) (coherentNerveFunctor.map F)).symm
  have hN := SSet.yonedaEquiv_naturality (SimplexCategory.δ j)
    ((SSet.yonedaEquiv (X := coherentNerveFunctor.obj D) (n := ⦋1⦌)).symm σ)
  exact hY.trans ((congrArg SSet.yonedaEquiv hJ).trans
    (hN.symm.trans (congrArg (fun q => coherentSimplexMap (SimplexCategory.δ j) ≫ q)
      ((SSet.yonedaEquiv (X := coherentNerveFunctor.obj D) (n := ⦋1⦌)).apply_symm_apply σ))))

include sq in
/-- The same individual source object has exactly its prescribed original target image. -/
theorem source_image :
    F.obj (source f) = σ.obj (.mk (ULift.up (0 : Fin 2))) :=
  congrArg (fun q : coherentSimplex.{u} ⦋0⦌ ⟶ D => q.obj zeroPoint) (face_image F f σ sq 1)

include sq in
/-- The same individual target object has exactly its prescribed original target image. -/
theorem target_image :
    F.obj (target f) = σ.obj (.mk (ULift.up (Fin.last 1))) :=
  congrArg (fun q : coherentSimplex.{u} ⦋0⦌ ⟶ D => q.obj zeroPoint) (face_image F f σ sq 0)

/-- Both genuine endpoint equations recover the complete original boundary, as a simplicial map. -/
theorem boundary_of_endpoints (τ : FixedSimplex (source f) (target f) (n := 0)) :
    (SSet.boundary.{u} 1).ι ≫
      (SSet.yonedaEquiv (X := coherentNerveFunctor.obj C) (n := ⦋1⦌)).symm τ.val = f := by
  let l : (Δ[1] : SSet.{u}) ⟶ coherentNerveFunctor.obj C :=
    (SSet.yonedaEquiv (X := coherentNerveFunctor.obj C) (n := ⦋1⦌)).symm τ.val
  apply SSet.boundary.hom_ext
  intro j
  have hFace : coherentSimplexMap (SimplexCategory.δ j) ≫ τ.val = faceFunctor f j := by
    apply (verticesEquiv C).injective
    fin_cases j
    · exact τ.property.2
    · exact τ.property.1
  have hJ : SSet.stdSimplex.δ j ≫ l = SSet.boundary.ι j ≫ f := by
    apply SSet.yonedaEquiv.injective
    have hY := (SSet.yonedaEquiv_naturality (SimplexCategory.δ j) l).symm
    exact hY.trans
      ((congrArg (fun q => coherentSimplexMap (SimplexCategory.δ j) ≫ q)
        ((SSet.yonedaEquiv (X := coherentNerveFunctor.obj C) (n := ⦋1⦌)).apply_symm_apply τ.val)).trans hFace)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ l) (SSet.boundary.ι_ι j)).trans hJ)

include sq in
/-- Genuine original full-Hom boundary lifting constructs the SAME entire prescribed enriched one-simplex and boundary.
-/
theorem exists_enriched_boundary_lift
    (hF : ∀ x y : C, SSet.modelCategoryQuillen.I.rlp (F.map x y)) :
    ∃ τ : coherentSimplex.{u} ⦋1⦌ ⟶ C,
      (SSet.boundary.{u} 1).ι ≫ SSet.yonedaEquiv.symm τ = f ∧ τ ≫ F = σ := by
  let S := OriginalCoherentEdgeLifting.fixedTarget F (source f) (target f) σ
    (source_image F f σ sq) (target_image F f σ sq)
  obtain ⟨τ,hτ⟩ := OriginalCoherentEdgeLifting.exists_fixed_edge_lift_of_hom_boundaries
    F (source f) (target f) (hF _ _) S
  exact ⟨τ.val, boundary_of_endpoints f τ, hτ⟩

end CategoryTheory.CoherentRealization.RelativeCoherentOneBoundary
