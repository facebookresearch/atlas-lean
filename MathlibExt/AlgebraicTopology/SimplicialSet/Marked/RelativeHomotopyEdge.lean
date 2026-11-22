/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeMappingVertex
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalEndpointComparison
import MathlibExt.AlgebraicTopology.ModelCategory.CylinderHomotopyCategory

/-!
# Original relative marked homotopies are actual maximal mapping edges

The native interval coordinate swap and fixed-base currying preserve the
whole original marked cylinder map. Its two original endpoint equations
are exactly the source and target equations of a maximal relative mapping
edge. Both directions retain the original base triangle, full simplices
and marks; no fibrancy or weak-equivalence premise is required.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

private def relativeParameterHomEquiv (Z : Marked.{u}) (X Y : Over Z) (K : SSet.{u}) :
    ((overParameterFunctor Z X).obj K ⟶ Y) ≃ (K ⟶ relativeMappingComplex .maximal X.hom Y.hom) :=
  overParameterHomEquiv Z X K Y

private theorem relativeMapping_endpoint_family (Z : Marked.{u}) (X : Over Z) (ε : Fin 2) :
    (overParameterFunctor Z X).map (relativeIntervalScalarEndpoint.{u} ε) ≫
        (relativeIntervalProductIso Z X).hom =
      (relativePointProductIso Z X).hom ≫ ((relativeIntervalCylinder Z).app X).endpoint ε := by
  let U := relativePointProductIso Z X
  let V := relativeIntervalProductIso Z X
  let a := (overParameterFunctor Z X).map (relativeIntervalScalarEndpoint.{u} ε)
  let ep := ((relativeIntervalCylinder Z).app X).endpoint ε
  have h : ep ≫ V.inv = U.inv ≫ a := relativeIntervalEndpoint_product_map Z X ε
  apply (cancel_mono V.inv).mp
  calc
    (a ≫ V.hom) ≫ V.inv = a := (Category.assoc _ _ _).trans
      ((congrArg (fun t => a ≫ t) V.hom_inv_id).trans (Category.comp_id a))
    _ = U.hom ≫ (U.inv ≫ a) := (U.hom_inv_id_assoc a).symm
    _ = (U.hom ≫ ep) ≫ V.inv := (congrArg (fun t => U.hom ≫ t) h.symm).trans (Category.assoc _ _ _).symm

/-- The original marked fixed-base interval homotopy curries to the same whole maximal relative mapping edge. -/
def relativeHomotopyMappingEdge {Z : Marked.{u}} {X Y : Over Z} {f₀ f₁ : X ⟶ Y}
    (H : ((relativeIntervalCylinder Z).app X).LeftHomotopy f₀ f₁) :
    SSet.Edge (relativeMappingVertexEquiv Z X Y f₀) (relativeMappingVertexEquiv Z X Y f₁) := by
  let G := overParameterFunctor Z X
  let U := relativePointProductIso Z X
  let V := relativeIntervalProductIso Z X
  let E₀ := relativeParameterHomEquiv Z X Y (Δ[0] : SSet.{u})
  let E₁ := relativeParameterHomEquiv Z X Y (Δ[1] : SSet.{u})
  let h : G.obj (Δ[1] : SSet.{u}) ⟶ Y := V.hom ≫ H.h
  let c := E₁ h
  have hf₀ : G.map (stdSimplex.{u}.δ (1 : Fin 2)) ≫ h = U.hom ≫ f₀ := by
    have he : G.map (stdSimplex.{u}.δ (1 : Fin 2)) ≫ V.hom = U.hom ≫ ((relativeIntervalCylinder Z).app X).endpoint 0 :=
      relativeMapping_endpoint_family Z X 0
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ H.h) he).trans
      ((Category.assoc _ _ _).trans (congrArg (fun t => U.hom ≫ t) H.h₀)))
  have hf₁ : G.map (stdSimplex.{u}.δ (0 : Fin 2)) ≫ h = U.hom ≫ f₁ := by
    have he : G.map (stdSimplex.{u}.δ (0 : Fin 2)) ≫ V.hom = U.hom ≫ ((relativeIntervalCylinder Z).app X).endpoint 1 :=
      relativeMapping_endpoint_family Z X 1
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ H.h) he).trans
      ((Category.assoc _ _ _).trans (congrArg (fun t => U.hom ≫ t) H.h₁)))
  have hc₀ : stdSimplex.{u}.δ (1 : Fin 2) ≫ c = E₀ (U.hom ≫ f₀) := by
    have hm : E₀.symm (stdSimplex.{u}.δ (1 : Fin 2) ≫ c) = G.map (stdSimplex.{u}.δ (1 : Fin 2)) ≫ E₁.symm c :=
      overParameterHomEquiv_symm_pre Z X Y _ c
    apply E₀.symm.injective
    exact hm.trans ((congrArg (fun t => G.map (stdSimplex.{u}.δ (1 : Fin 2)) ≫ t) (E₁.symm_apply_apply h)).trans
      (hf₀.trans (E₀.symm_apply_apply (U.hom ≫ f₀)).symm))
  have hc₁ : stdSimplex.{u}.δ (0 : Fin 2) ≫ c = E₀ (U.hom ≫ f₁) := by
    have hm : E₀.symm (stdSimplex.{u}.δ (0 : Fin 2) ≫ c) = G.map (stdSimplex.{u}.δ (0 : Fin 2)) ≫ E₁.symm c :=
      overParameterHomEquiv_symm_pre Z X Y _ c
    apply E₀.symm.injective
    exact hm.trans ((congrArg (fun t => G.map (stdSimplex.{u}.δ (0 : Fin 2)) ≫ t) (E₁.symm_apply_apply h)).trans
      (hf₁.trans (E₀.symm_apply_apply (U.hom ≫ f₁)).symm))
  refine SSet.Edge.mk (yonedaEquiv c) ?_ ?_
  · exact (stdSimplex.yonedaEquiv_δ_comp c (1 : Fin 2)).symm.trans (congrArg yonedaEquiv hc₀)
  · exact (stdSimplex.yonedaEquiv_δ_comp c (0 : Fin 2)).symm.trans (congrArg yonedaEquiv hc₁)

/-- The actual maximal relative mapping edge uncurries to the same original marked cylinder homotopy over
  its supplied base. -/
def relativeMappingEdgeHomotopy {Z : Marked.{u}} {X Y : Over Z} {f₀ f₁ : X ⟶ Y}
    (e : SSet.Edge (relativeMappingVertexEquiv Z X Y f₀) (relativeMappingVertexEquiv Z X Y f₁)) :
    ((relativeIntervalCylinder Z).app X).LeftHomotopy f₀ f₁ := by
  let G := overParameterFunctor Z X
  let U := relativePointProductIso Z X
  let V := relativeIntervalProductIso Z X
  let E₀ := relativeParameterHomEquiv Z X Y (Δ[0] : SSet.{u})
  let E₁ := relativeParameterHomEquiv Z X Y (Δ[1] : SSet.{u})
  let c := yonedaEquiv.symm e.edge
  let h : G.obj (Δ[1] : SSet.{u}) ⟶ Y := E₁.symm c
  have hv₀ : E₀.symm (yonedaEquiv.symm (relativeMappingVertexEquiv Z X Y f₀)) = U.hom ≫ f₀ :=
    (congrArg E₀.symm (relativeMappingVertexEquiv_yoneda_symm Z X Y f₀)).trans (E₀.symm_apply_apply _)
  have hv₁ : E₀.symm (yonedaEquiv.symm (relativeMappingVertexEquiv Z X Y f₁)) = U.hom ≫ f₁ :=
    (congrArg E₀.symm (relativeMappingVertexEquiv_yoneda_symm Z X Y f₁)).trans (E₀.symm_apply_apply _)
  have hm₀ : G.map (stdSimplex.{u}.δ (1 : Fin 2)) ≫ h = E₀.symm (stdSimplex.{u}.δ (1 : Fin 2) ≫ c) :=
    (overParameterHomEquiv_symm_pre Z X Y (stdSimplex.{u}.δ (1 : Fin 2)) c).symm
  have hm₁ : G.map (stdSimplex.{u}.δ (0 : Fin 2)) ≫ h = E₀.symm (stdSimplex.{u}.δ (0 : Fin 2) ≫ c) :=
    (overParameterHomEquiv_symm_pre Z X Y (stdSimplex.{u}.δ (0 : Fin 2)) c).symm
  refine { h := V.inv ≫ h, h₀ := ?_, h₁ := ?_ }
  · calc
      ((relativeIntervalCylinder Z).app X).i₀ ≫ (V.inv ≫ h) =
          (((relativeIntervalCylinder Z).app X).endpoint 0 ≫ V.inv) ≫ h := (Category.assoc _ _ _).symm
      _ = (U.inv ≫ G.map (stdSimplex.{u}.δ (1 : Fin 2))) ≫ h :=
        congrArg (fun t => t ≫ h) (relativeIntervalEndpoint_product_map Z X 0)
      _ = U.inv ≫ E₀.symm (stdSimplex.{u}.δ (1 : Fin 2) ≫ c) :=
        (Category.assoc _ _ _).trans (congrArg (fun t => U.inv ≫ t) hm₀)
      _ = U.inv ≫ (U.hom ≫ f₀) := congrArg (fun t => U.inv ≫ E₀.symm t) (SSet.Edge.δ_one_yonedaEquiv_symm e) |>.trans
        (congrArg (fun t => U.inv ≫ t) hv₀)
      _ = f₀ := U.inv_hom_id_assoc f₀
  · calc
      ((relativeIntervalCylinder Z).app X).i₁ ≫ (V.inv ≫ h) =
          (((relativeIntervalCylinder Z).app X).endpoint 1 ≫ V.inv) ≫ h := (Category.assoc _ _ _).symm
      _ = (U.inv ≫ G.map (stdSimplex.{u}.δ (0 : Fin 2))) ≫ h :=
        congrArg (fun t => t ≫ h) (relativeIntervalEndpoint_product_map Z X 1)
      _ = U.inv ≫ E₀.symm (stdSimplex.{u}.δ (0 : Fin 2) ≫ c) :=
        (Category.assoc _ _ _).trans (congrArg (fun t => U.inv ≫ t) hm₁)
      _ = U.inv ≫ (U.hom ≫ f₁) := congrArg (fun t => U.inv ≫ E₀.symm t) (SSet.Edge.δ_zero_yonedaEquiv_symm e) |>.trans
        (congrArg (fun t => U.inv ≫ t) hv₁)
      _ = f₁ := U.inv_hom_id_assoc f₁

/-- Elementary homotopy for the whole original marked relative cylinder is exactly the actual relative
  mapping edge relation. -/
theorem relativeElementaryHomotopy_iff_mappingEdge {Z : Marked.{u}} {X Y : Over Z} (f₀ f₁ : X ⟶ Y) :
    Nonempty (((relativeIntervalCylinder Z).app X).LeftHomotopy f₀ f₁) ↔
      SSet.π₀Rel (relativeMappingVertexEquiv Z X Y f₀) (relativeMappingVertexEquiv Z X Y f₁) :=
  ⟨fun ⟨H⟩ => ⟨relativeHomotopyMappingEdge H⟩, fun ⟨e⟩ => ⟨relativeMappingEdgeHomotopy e⟩⟩

end SSet.Marked
