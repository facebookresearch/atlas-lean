/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientRelativeRootCancellation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningCompositionWeak

/-!
# Original relative cancellation on actual native model-fibration maps

Both original root triangles and the zero-face action along the whole
original path are retained. Actual coefficient fibrations lift the
original weak root cancellation cell. The same native map and entire
coherent projection equation therefore recover the original first-edge
mark from its target mark and the source long and second-edge marks.
Neither diagram is assumed fibrant and the original base is arbitrary.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] vertexDecidableEq markedSimplicialCategory enrichedDiagramCategory
  coefficientMarkedModelCategory

/-- The same original coherent two-simplex section retains relative cancellation along an actual coherent-model
fibration. -/
theorem coherentUnstraightening_relative_cancellation_marking (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ a : UnstraighteningSimplex F 2,
      (unstraighteningCore (realization B) F).δ (0 : Fin 3) a ∈
        (coherentUnstraightening (realization B) F).marking →
      (unstraighteningCore (realization B) F).δ (1 : Fin 3) a ∈
        (coherentUnstraightening (realization B) F).marking →
      (unstraighteningCore (realization B) G).δ (2 : Fin 3) (a.mapCoefficient q) ∈
        (coherentUnstraightening (realization B) G).marking →
      (unstraighteningCore (realization B) F).δ (2 : Fin 3) a ∈
        (coherentUnstraightening (realization B) F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq a h₀ h₁ h₂
  let i₀ : Index.{u} 2 := SimplicialThickening.mk rootTriangleZero
  let i₁ : Index.{u} 2 := SimplicialThickening.mk rootTriangleOne
  let g₀ := a.sectionMap.app (op i₀)
  let g₁ := a.sectionMap.app (op i₁)
  let v := (coneImage (coneCofaceEmbedding.{u} (0 : Fin 3)).toOrderHom zeroOne).hom.app
    (op ⦋1⦌) coefficientEdge
  change g₁.hom.app (op ⦋1⦌) v ∈ (F.obj (op (a.base.obj i₁))).marking at h₀
  change g₀.hom.app (op ⦋1⦌)
    ((coneImage (coneCofaceEmbedding (1 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌)
      coefficientEdge) ∈ (F.obj (op (a.base.obj i₀))).marking at h₁
  rw [rootTriangle_direct_image] at h₁
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
  have hmiddle : g₀.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleMiddle.{u}).edge ∈
      (F.obj (op (a.base.obj i₀))).marking := by
    change g₀.hom.app (op ⦋1⦌)
      ((coneAction rootTriangleZero rootTriangleOne).hom.app (op ⦋1⦌)
        (rootTrianglePathWord, v)) = _ at hr
    rw [rootTriangle_middle_action] at hr
    exact hr.symm ▸ hp
  change (g₀ ≫ q.app (op (a.base.obj i₀))).hom.app (op ⦋1⦌)
    ((coneImage (coneCofaceEmbedding (2 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌)
      coefficientEdge) ∈ (G.obj (op (a.base.obj i₀))).marking at h₂
  rw [rootTriangle_first_image] at h₂
  change g₀.hom.app (op ⦋1⦌)
    ((coneImage (coneCofaceEmbedding (2 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌)
      coefficientEdge) ∈ (F.obj (op (a.base.obj i₀))).marking
  rw [rootTriangle_first_image]
  exact coherentDiagramCoefficient_relative_rootCancellation B q (op (a.base.obj i₀)) g₀ h₁ hmiddle h₂ hq

/-- The same full original coherent two-simplex map keeps relative cancellation at all three original faces. -/
theorem coherentUnstraightening_relative_cancellation_map (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ t : (Δ[2] : SSet.{u}) ⟶ (coherentUnstraightening (realization B) F).toSSet,
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (0 : Fin 3))) ∈
        (coherentUnstraightening (realization B) F).marking →
      t.app (op ⦋1⦌) compositionLongEdge.{u} ∈ (coherentUnstraightening (realization B) F).marking →
      (t ≫ (coherentUnstraighteningMap q).hom).app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3))) ∈
        (coherentUnstraightening (realization B) G).marking →
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3))) ∈
        (coherentUnstraightening (realization B) F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq t h₀ h₁ h₂
  let a := yonedaEquiv t
  have face (k : Fin 3) : (unstraighteningCore (realization B) F).δ k a =
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ k)) :=
    (stdSimplex.yonedaEquiv_δ_comp t k).symm.trans (yonedaEquiv_comp _ t)
  have hqwhole : a.mapCoefficient q = yonedaEquiv (t ≫ (coherentUnstraighteningMap q).hom) :=
    (yonedaEquiv_comp t (coherentUnstraighteningMap q).hom).symm
  have faceq (k : Fin 3) : (unstraighteningCore (realization B) G).δ k (a.mapCoefficient q) =
      (t ≫ (coherentUnstraighteningMap q).hom).app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ k)) := by
    rw [hqwhole]
    exact (stdSimplex.yonedaEquiv_δ_comp (t ≫ (coherentUnstraighteningMap q).hom) k).symm.trans
      (yonedaEquiv_comp _ _)
  rw [← face 0] at h₀
  change t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (1 : Fin 3))) ∈ _ at h₁
  rw [← face 1] at h₁
  rw [← faceq 2] at h₂
  exact (face 2) ▸ coherentUnstraightening_relative_cancellation_marking B q hq a h₀ h₁ h₂

/-- The same actual native total map reflects cancellation along every original whole two-simplex, without diagram
or base fibrancy. -/
theorem nativeUnstraightening_map_relativeCancellation (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ t : (Δ[2] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet,
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (0 : Fin 3))) ∈ (nativeUnstraighteningTotal B F).marking →
      t.app (op ⦋1⦌) compositionLongEdge.{u} ∈ (nativeUnstraighteningTotal B F).marking →
      (t ≫ ((nativeUnstraightening B).map q).left.hom).app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3))) ∈
        (nativeUnstraighteningTotal B G).marking →
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3))) ∈ (nativeUnstraighteningTotal B F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq t h₀ h₁ h₂
  have h₀' := (nativeUnstraightening_marking_coherent_iff B F _).mp h₀
  have h₁' := (nativeUnstraightening_marking_coherent_iff B F _).mp h₁
  have h₂' := (nativeUnstraightening_marking_coherent_iff B G _).mp h₂
  apply (nativeUnstraightening_marking_coherent_iff B F _).mpr
  apply coherentUnstraightening_relative_cancellation_map B q hq
    (t ≫ (nativeUnstraighteningCoherentProjection B F).hom) h₀' h₁'
  have hw := congrArg Hom.hom (nativeUnstraightening_map_coherentProjection B q)
  have ht := congrArg (fun f => t ≫ f) hw
  have he : (t ≫ ((nativeUnstraightening B).map q).left.hom) ≫
        (nativeUnstraighteningCoherentProjection B G).hom =
      (t ≫ (nativeUnstraighteningCoherentProjection B F).hom) ≫ (coherentUnstraighteningMap q).hom :=
    (Category.assoc _ _ _).trans (ht.trans (Category.assoc _ _ _).symm)
  exact (congrArg (fun f => f.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3)))) he) ▸ h₂'

/-- The original full native composition triangle retains its first-edge mark by actual relative cancellation under
a coherent-model fibration. -/
theorem nativeUnstraightening_map_relativeCancellationCompStruct (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G)
    {x₀ x₁ x₂ : (nativeUnstraighteningTotal B F).toSSet _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (H : Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (h₁₂ : e₁₂.edge ∈ (nativeUnstraighteningTotal B F).marking)
    (h₀₂ : e₀₂.edge ∈ (nativeUnstraighteningTotal B F).marking)
    (h₀₁ : ((nativeUnstraightening B).map q).left.hom.app (op ⦋1⦌) e₀₁.edge ∈
      (nativeUnstraighteningTotal B G).marking) :
    let _ := coherentDiagramModelCategory B
    Fibration q → e₀₁.edge ∈ (nativeUnstraighteningTotal B F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let t := yonedaEquiv.symm H.simplex
  have face (k : Fin 3) : (nativeUnstraighteningTotal B F).toSSet.δ k H.simplex =
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ k)) := by
    have hf := (stdSimplex.yonedaEquiv_δ_comp t k).symm.trans (yonedaEquiv_comp _ t)
    have ht : yonedaEquiv t = H.simplex := Equiv.apply_symm_apply _ _
    rw [ht] at hf
    exact hf
  have h₂ := (face 2).symm.trans H.d₂
  have h₀ := (face 0).symm.trans H.d₀
  have h₁ := (face 1).symm.trans H.d₁
  have ht₀ : t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (0 : Fin 3))) ∈
      (nativeUnstraighteningTotal B F).marking := by rw [h₀]; exact h₁₂
  have ht₁ : t.app (op ⦋1⦌) compositionLongEdge.{u} ∈ (nativeUnstraighteningTotal B F).marking := by
    change t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (1 : Fin 3))) ∈ _
    rw [h₁]
    exact h₀₂
  have ht₂ : (t ≫ ((nativeUnstraightening B).map q).left.hom).app (op ⦋1⦌)
      (yonedaEquiv (stdSimplex.δ (2 : Fin 3))) ∈ (nativeUnstraighteningTotal B G).marking := by
    change ((nativeUnstraightening B).map q).left.hom.app (op ⦋1⦌)
      (t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3)))) ∈ _
    rw [h₂]
    exact h₀₁
  exact h₂ ▸ nativeUnstraightening_map_relativeCancellation B q hq t ht₀ ht₁ ht₂

end SSet.Marked
