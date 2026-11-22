/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCompositionTriangles
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentDiagramCoefficientFibrancy
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningMarked

/-!
# Original marked composition in coherent unstraightening

Actual coefficient-model fibrancy identifies its unchanged marks with
its original equivalence edges. The two actual root inclusion triangles
give composition and cancellation. The full natural section transports
the original zero-face coefficient edge through the SAME whole original
path `{0,1}`. This proves composition for the original coherent
unstraightening marking, without a saturation or filler outcome as input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- The two SAME original root triangles compose marked short edges and cancel their already marked constant-maximum
edge in an actual fibrant coefficient. -/
theorem rootTriangle_marked_composition (A : Marked.{u}) (hA : IsFibrant A)
    (g : coneWeight rootTriangleZero ⟶ A)
    (hfirst : g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleFirst).edge ∈ A.marking)
    (hmiddle : g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleMiddle).edge ∈ A.marking) :
    g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleDirect).edge ∈ A.marking := by
  have h₀₁ : ((nerve.edgeMk rootTriangleFirst).map g.hom).IsEquivalence :=
    ((coefficientFibrant_marking_iff A hA _).mp hfirst).of_edge_eq rfl
  have h₁₂ : ((nerve.edgeMk rootTriangleMiddle).map g.hom).IsEquivalence :=
    ((coefficientFibrant_marking_iff A hA _).mp hmiddle).of_edge_eq rfl
  have hfull : ((nerve.edgeMk rootTriangleFull).map g.hom).IsEquivalence :=
    Edge.IsEquivalence.of_compStruct (rootTriangleFirstComp.map g.hom) h₀₁ h₁₂
  have hc : ((nerve.edgeMk rootTriangleConstant).map g.hom).IsEquivalence :=
    ((coefficientFibrant_marking_iff A hA _).mp (g.preserve rootTriangle_constant_marked)).of_edge_eq rfl
  let _ : IsIso ((nerve.edgeMk rootTriangleConstant).map g.hom).toHoHom := hc
  let _ : IsIso (((nerve.edgeMk rootTriangleDirect).map g.hom).toHoHom ≫
      ((nerve.edgeMk rootTriangleConstant).map g.hom).toHoHom) := by
    rw [Edge.toHoHom_comp (rootTriangleSecondComp.map g.hom)]
    exact hfull
  have hd : ((nerve.edgeMk rootTriangleDirect).map g.hom).IsEquivalence :=
    IsIso.of_isIso_comp_right ((nerve.edgeMk rootTriangleDirect).map g.hom).toHoHom
      ((nerve.edgeMk rootTriangleConstant).map g.hom).toHoHom
  exact (coefficientFibrant_marking_iff A hA _).mpr (hd.of_edge_eq rfl)

/-- The entire SAME original two-simplex section preserves its original marked composition, using the whole original
coherent path action. -/
theorem coherentUnstraightening_composition_marking (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → ∀ a : UnstraighteningSimplex F 2,
      (unstraighteningCore (realization B) F).δ (2 : Fin 3) a ∈
        (coherentUnstraightening (realization B) F).marking →
      (unstraighteningCore (realization B) F).δ (0 : Fin 3) a ∈
        (coherentUnstraightening (realization B) F).marking →
      (unstraighteningCore (realization B) F).δ (1 : Fin 3) a ∈
        (coherentUnstraightening (realization B) F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF a h₂ h₀
  let i₀ : Index.{u} 2 := SimplicialThickening.mk rootTriangleZero
  let i₁ : Index.{u} 2 := SimplicialThickening.mk rootTriangleOne
  let g₀ := a.sectionMap.app (op i₀)
  let g₁ := a.sectionMap.app (op i₁)
  let v := (coneImage (coneCofaceEmbedding.{u} (0 : Fin 3)).toOrderHom zeroOne).hom.app
    (op ⦋1⦌) coefficientEdge
  change g₀.hom.app (op ⦋1⦌)
    ((coneImage (coneCofaceEmbedding (2 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌)
      coefficientEdge) ∈ (F.obj (op (a.base.obj i₀))).marking at h₂
  rw [rootTriangle_first_image] at h₂
  change g₁.hom.app (op ⦋1⦌) v ∈ (F.obj (op (a.base.obj i₁))).marking at h₀
  have hn := enrichedDiagramAction_natural a.sectionMap (op i₁) (op i₀)
  rw [coneDiagram_action] at hn
  have hr := congrArg (fun f => f.hom.app (op ⦋1⦌) (rootTrianglePathWord.{u}, v)) hn
  change g₀.hom.app (op ⦋1⦌)
      ((coneAction rootTriangleZero rootTriangleOne).hom.app (op ⦋1⦌)
        (rootTrianglePathWord, v)) =
    (enrichedDiagramAction (simplexCoefficient F a.base) (op i₁) (op i₀)).hom.app
      (op ⦋1⦌) (rootTrianglePathWord, g₁.hom.app (op ⦋1⦌) v) at hr
  have hp := (enrichedDiagramAction (simplexCoefficient F a.base) (op i₁) (op i₀)).preserve
    (show (rootTrianglePathWord, g₁.hom.app (op ⦋1⦌) v) ∈
      (prod (max ((op i₁) ⟶[SSet.{u}] (op i₀)))
        ((simplexCoefficient F a.base).obj (op i₁))).marking from ⟨Set.mem_univ _, h₀⟩)
  change g₀.hom.app (op ⦋1⦌)
    ((coneImage (coneCofaceEmbedding (1 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌)
      coefficientEdge) ∈ (F.obj (op (a.base.obj i₀))).marking
  rw [rootTriangle_direct_image]
  apply rootTriangle_marked_composition _
    (coherentDiagramCoefficient_isFibrant B F (op (a.base.obj i₀)) hF) g₀ h₂
  change g₀.hom.app (op ⦋1⦌)
    ((coneAction rootTriangleZero rootTriangleOne).hom.app (op ⦋1⦌)
      (rootTrianglePathWord, v)) = _ at hr
  have hv : (coneAction rootTriangleZero rootTriangleOne).hom.app (op ⦋1⦌)
      (rootTrianglePathWord, v) = (nerve.edgeMk rootTriangleMiddle).edge := rootTriangle_middle_action
  rw [hv] at hr
  exact hr.symm ▸ hp

/-- The SAME whole original coherent two-simplex map reads exactly the original composition marking on its three
actual faces. -/
theorem coherentUnstraightening_composition_map (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → ∀ t : (Δ[2] : SSet.{u}) ⟶ (coherentUnstraightening (realization B) F).toSSet,
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3))) ∈
        (coherentUnstraightening (realization B) F).marking →
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (0 : Fin 3))) ∈
        (coherentUnstraightening (realization B) F).marking →
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (1 : Fin 3))) ∈
        (coherentUnstraightening (realization B) F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF t h₂ h₀
  let a := yonedaEquiv t
  have face (k : Fin 3) : (unstraighteningCore (realization B) F).δ k a =
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ k)) :=
    (stdSimplex.yonedaEquiv_δ_comp t k).symm.trans (yonedaEquiv_comp _ t)
  rw [← face 2] at h₂
  rw [← face 0] at h₀
  exact (face 1) ▸ coherentUnstraightening_composition_marking B F hF a h₂ h₀

end SSet.Marked.CoherentWeight
