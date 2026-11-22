/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientRelativeRootComposition
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningCompositionMarking

/-!
# Original relative composition marks for native maps of actual fibrations

The whole original coefficient map retains both root triangles and the
original zero-face path action. Every actual coefficient fibration lifts
the same original weak root marking cell, so its direct edge is marked
when the source short edges and the target direct edge are marked. The
same native pullback map and its entire coherent projection equation
transfer this property to the original native total map. Neither diagram
is assumed fibrant, and the original base is arbitrary.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] vertexDecidableEq markedSimplicialCategory enrichedDiagramCategory
  coefficientMarkedModelCategory

/-- The same whole original coherent section reflects a relative composition mark along an actual model fibration,
without diagram fibrancy. -/
theorem coherentUnstraightening_relative_composition_marking (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ a : UnstraighteningSimplex F 2,
      (unstraighteningCore (realization B) F).δ (2 : Fin 3) a ∈
        (coherentUnstraightening (realization B) F).marking →
      (unstraighteningCore (realization B) F).δ (0 : Fin 3) a ∈
        (coherentUnstraightening (realization B) F).marking →
      (unstraighteningCore (realization B) G).δ (1 : Fin 3) (a.mapCoefficient q) ∈
        (coherentUnstraightening (realization B) G).marking →
      (unstraighteningCore (realization B) F).δ (1 : Fin 3) a ∈
        (coherentUnstraightening (realization B) F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq a h₂ h₀ h₁
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
  have hmiddle : g₀.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleMiddle.{u}).edge ∈
      (F.obj (op (a.base.obj i₀))).marking := by
    change g₀.hom.app (op ⦋1⦌)
      ((coneAction rootTriangleZero rootTriangleOne).hom.app (op ⦋1⦌)
        (rootTrianglePathWord, v)) = _ at hr
    rw [rootTriangle_middle_action] at hr
    exact hr.symm ▸ hp
  change (g₀ ≫ q.app (op (a.base.obj i₀))).hom.app (op ⦋1⦌)
    ((coneImage (coneCofaceEmbedding (1 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌)
      coefficientEdge) ∈ (G.obj (op (a.base.obj i₀))).marking at h₁
  rw [rootTriangle_direct_image] at h₁
  exact coherentDiagramCoefficient_relative_rootComposition B q (op (a.base.obj i₀)) g₀ h₂ hmiddle h₁ hq

/-- The same full original coherent two-simplex map retains the original relative composition along an actual model
fibration. -/
theorem coherentUnstraightening_relative_composition_map (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ t : (Δ[2] : SSet.{u}) ⟶ (coherentUnstraightening (realization B) F).toSSet,
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3))) ∈
        (coherentUnstraightening (realization B) F).marking →
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (0 : Fin 3))) ∈
        (coherentUnstraightening (realization B) F).marking →
      (t ≫ (coherentUnstraighteningMap q).hom).app (op ⦋1⦌) compositionLongEdge.{u} ∈
        (coherentUnstraightening (realization B) G).marking →
      t.app (op ⦋1⦌) compositionLongEdge.{u} ∈ (coherentUnstraightening (realization B) F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq t h₂ h₀ h₁
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
  rw [← face 2] at h₂
  rw [← face 0] at h₀
  change (t ≫ (coherentUnstraighteningMap q).hom).app (op ⦋1⦌)
    (yonedaEquiv (stdSimplex.δ (1 : Fin 3))) ∈ _ at h₁
  rw [← faceq 1] at h₁
  exact (face 1) ▸ coherentUnstraightening_relative_composition_marking B q hq a h₂ h₀ h₁

/-- The same original native map retains its entire coherent projection composite. -/
theorem nativeUnstraightening_map_coherentProjection (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    ((nativeUnstraightening B).map q).left ≫ nativeUnstraighteningCoherentProjection B G =
      nativeUnstraighteningCoherentProjection B F ≫ coherentUnstraighteningMap q := by
  change pullback.lift
    (nativeUnstraighteningCoherentProjection B F ≫ coherentUnstraighteningMap q)
    (nativeUnstraighteningProjection B F) _ ≫
      pullback.fst (coherentUnstraighteningProjection (realization B) G) (maximal.map (unit B)) = _
  exact pullback.lift_fst _ _ _

/-- The same original native total map reflects the relative original composition mark along an actual
coherent-model fibration over every base. -/
theorem nativeUnstraightening_map_relativeComposition (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ t : (Δ[2] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet,
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3))) ∈ (nativeUnstraighteningTotal B F).marking →
      t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (0 : Fin 3))) ∈ (nativeUnstraighteningTotal B F).marking →
      (t ≫ ((nativeUnstraightening B).map q).left.hom).app (op ⦋1⦌) compositionLongEdge.{u} ∈
        (nativeUnstraighteningTotal B G).marking →
      t.app (op ⦋1⦌) compositionLongEdge.{u} ∈ (nativeUnstraighteningTotal B F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq t h₂ h₀ h₁
  have h₂' := (nativeUnstraightening_marking_coherent_iff B F _).mp h₂
  have h₀' := (nativeUnstraightening_marking_coherent_iff B F _).mp h₀
  have h₁' := (nativeUnstraightening_marking_coherent_iff B G _).mp h₁
  apply (nativeUnstraightening_marking_coherent_iff B F _).mpr
  apply coherentUnstraightening_relative_composition_map B q hq
    (t ≫ (nativeUnstraighteningCoherentProjection B F).hom) h₂' h₀'
  have hw := congrArg Hom.hom (nativeUnstraightening_map_coherentProjection B q)
  have ht := congrArg (fun f => t ≫ f) hw
  have he : (t ≫ ((nativeUnstraightening B).map q).left.hom) ≫
        (nativeUnstraighteningCoherentProjection B G).hom =
      (t ≫ (nativeUnstraighteningCoherentProjection B F).hom) ≫ (coherentUnstraighteningMap q).hom :=
    (Category.assoc _ _ _).trans (ht.trans (Category.assoc _ _ _).symm)
  exact (congrArg (fun f => f.app (op ⦋1⦌) compositionLongEdge.{u}) he) ▸ h₁'

end SSet.Marked
