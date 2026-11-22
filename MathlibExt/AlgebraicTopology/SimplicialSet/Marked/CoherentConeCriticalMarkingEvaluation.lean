/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalMarkingFreeCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ColimitCriterion
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Both entire original critical marking squares are pointwise marked pushouts

The free interval marking map and the whole cone or horn marking map
are literal identities on their original underlying carriers. Every
new marked edge has the actual whole-path representative of the same
original critical edge. The genuine marked universal property therefore
holds at every original coefficient, retaining the full horn inclusion.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The SAME whole sharp free horn leg followed by the original inclusion is precisely the entire cone leg. -/
theorem coneCriticalEdgeHornSharpLeg_inclusion (n : ℕ) :
    coneCriticalEdgeHornSharpLeg n ≫ coneCriticalHornInclusion n = coneCriticalEdgeConeSharpLeg.{u} n := by
  let C := (Index.{u} (n + 2))ᵒᵖ
  let c := op (SimplicialThickening.mk (coneCriticalPrevious.{u} n))
  let D := max (coneWeight (⊥ : Vertex.{u} 1)).toSSet
  apply (enrichedFreeHomEquiv C c D (coneCriticalDiagram n)).injective
  have h := (enrichedFreeEvaluationAdjunction C c).homEquiv_naturality_right
    (coneCriticalEdgeHornSharpLeg n) (coneCriticalHornInclusion n)
  change enrichedFreeUnit C c D ≫ (coneCriticalEdgeHornSharpLeg n ≫ coneCriticalHornInclusion n).app c =
    (enrichedFreeUnit C c D ≫ (coneCriticalEdgeHornSharpLeg n).app c) ≫ (coneCriticalHornInclusion n).app c at h
  rw [coneCriticalEdgeHornSharpLeg_unit] at h
  have hr : coneCriticalEdgeSharpHornRoot n ≫ (coneCriticalHornInclusion n).app c =
      coneCriticalEdgeSharpRoot n := by
    let e := coneCriticalHornAboveIso n (coneCriticalPrevious_pos.{u} n)
    have hi : e.inv ≫ coneCriticalHornCoefficientInclusion n (coneCriticalPrevious n) = 𝟙 _ :=
      (congrArg (fun f => e.inv ≫ f) (coneCriticalHornAboveIso_hom n (coneCriticalPrevious_pos.{u} n))).symm.trans
        e.inv_hom_id
    change (coneCriticalEdgeSharpRoot n ≫ e.inv) ≫
      coneCriticalHornCoefficientInclusion n (coneCriticalPrevious n) = coneCriticalEdgeSharpRoot n
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => coneCriticalEdgeSharpRoot n ≫ f) hi).trans (Category.comp_id _))
  exact h.trans (hr.trans (coneCriticalEdgeConeSharpLeg_unit n).symm)

/-- The entire original critical free cone leg realizes every supplied original maximum-changing marked edge. -/
theorem coneCriticalEdgeConeSharpLeg_represents (n : ℕ) (i : Vertex.{u} (n + 2))
    (e : (nerve (ConeSubset i)) _⦋1⦌)
    (h₀ : (e.obj 0).maximum = coneCriticalPrevious n)
    (h₁ : (e.obj 1).maximum = coneCriticalLast n) :
    ((coneCriticalEdgeConeSharpLeg n).app (op (SimplicialThickening.mk i))).hom.app (op ⦋1⦌)
      (coneCriticalEdgePathWord n i e h₀, coneCriticalIntervalWord) = e := by
  change (enrichedDiagramAction (coneCriticalDiagram n)
    (op (SimplicialThickening.mk (coneCriticalPrevious n))) (op (SimplicialThickening.mk i))).hom.app (op ⦋1⦌)
      (coneCriticalEdgePathWord n i e h₀, (coneCriticalEdgeSharpRoot n).hom.app (op ⦋1⦌) coneCriticalIntervalWord) = e
  rw [coneCriticalDiagram_action]
  exact coneCriticalEdgePath_represents n i e h₀ h₁

/-- Every SAME original critical horn marked edge has that whole original free representative with its exact
original support retained. -/
theorem coneCriticalEdgeHornSharpLeg_represents (n : ℕ) (i : Vertex.{u} (n + 2))
    (e : (coneCriticalHornWeight n i).toSSet _⦋1⦌)
    (h₀ : (e.val.obj 0).maximum = coneCriticalPrevious n)
    (h₁ : (e.val.obj 1).maximum = coneCriticalLast n) :
    ((coneCriticalEdgeHornSharpLeg n).app (op (SimplicialThickening.mk i))).hom.app (op ⦋1⦌)
      (coneCriticalEdgePathWord n i e.val h₀, coneCriticalIntervalWord) = e := by
  have h := congrArg
    (fun f => (f.app (op (SimplicialThickening.mk i))).hom.app (op ⦋1⦌)
      (coneCriticalEdgePathWord n i e.val h₀, coneCriticalIntervalWord))
    (coneCriticalEdgeHornSharpLeg_inclusion.{u} n)
  apply Subtype.ext
  exact h.trans (coneCriticalEdgeConeSharpLeg_represents n i e.val h₀ h₁)

/-- Every actual original coefficient of the full critical cone carries its SAME free marking square. -/
def coneCriticalEdgeConeComponentCocone (n : ℕ) (i : Vertex.{u} (n + 2)) :
    PushoutCocone ((coneCriticalEdgeFreeMap n).app (op (SimplicialThickening.mk i)))
      ((coneCriticalEdgeConeMinimalLeg n).app (op (SimplicialThickening.mk i))) :=
  PushoutCocone.mk ((coneCriticalEdgeConeSharpLeg n).app (op (SimplicialThickening.mk i)))
    ((coneCriticalDiagramMark n).app (op (SimplicialThickening.mk i)))
      (congrArg (fun f => f.app (op (SimplicialThickening.mk i))) (coneCriticalEdgeConeFree_condition n))

/-- The SAME entire original cone coefficient is the genuine marked pushout of that original predecessor free
marking cell. -/
def coneCriticalEdgeConeComponentIsColimit (n : ℕ) (i : Vertex.{u} (n + 2)) :
    IsColimit (coneCriticalEdgeConeComponentCocone n i) := by
  let c := op (SimplicialThickening.mk i)
  let f := (coneCriticalEdgeFreeMap n).app c
  let g := (coneCriticalEdgeConeMinimalLeg n).app c
  let l := (coneCriticalEdgeConeSharpLeg n).app c
  let r := (coneCriticalDiagramMark n).app c
  have hc : f ≫ l = g ≫ r := congrArg (fun x => x.app c) (coneCriticalEdgeConeFree_condition n)
  let _ : IsIso (forget.map f) := by
    change IsIso (𝟙 _)
    infer_instance
  let _ : IsIso (forget.map r) := by
    change IsIso (𝟙 _)
    infer_instance
  have hw : CommSq (forget.map f) (forget.map g) (forget.map l) (forget.map r) :=
    ⟨(forget.map_comp f l).symm.trans ((congrArg forget.map hc).trans (forget.map_comp g r))⟩
  have hp := IsPushout.of_horiz_isIso hw
  apply isColimitOfUnderlyingMarking
    ((isColimitMapCoconePushoutCoconeEquiv forget hc).symm hp.isColimit)
  intro e he
  rcases (coneCriticalWeight_marked_iff n i e).mp he with h | ⟨h₀, h₁⟩
  · exact ⟨WalkingSpan.right, e, h, rfl⟩
  · exact ⟨WalkingSpan.left, (coneCriticalEdgePathWord n i e h₀, coneCriticalIntervalWord),
      ⟨Set.mem_univ _, Set.mem_univ _⟩, coneCriticalEdgeConeSharpLeg_represents n i e h₀ h₁⟩

/-- Each actual original coefficient of the SAME full critically marked horn retains its whole free marking square. -/
def coneCriticalEdgeHornComponentCocone (n : ℕ) (i : Vertex.{u} (n + 2)) :
    PushoutCocone ((coneCriticalEdgeFreeMap n).app (op (SimplicialThickening.mk i)))
      ((coneCriticalEdgeHornMinimalLeg n).app (op (SimplicialThickening.mk i))) :=
  PushoutCocone.mk ((coneCriticalEdgeHornSharpLeg n).app (op (SimplicialThickening.mk i)))
    ((coneCriticalHornDiagramMark n).app (op (SimplicialThickening.mk i)))
      (congrArg (fun f => f.app (op (SimplicialThickening.mk i))) (coneCriticalEdgeHornFree_condition n))

/-- The SAME entire original horn coefficient is the actual marked pushout, with all original support and newly
marked edge representatives retained. -/
def coneCriticalEdgeHornComponentIsColimit (n : ℕ) (i : Vertex.{u} (n + 2)) :
    IsColimit (coneCriticalEdgeHornComponentCocone n i) := by
  let c := op (SimplicialThickening.mk i)
  let f := (coneCriticalEdgeFreeMap n).app c
  let g := (coneCriticalEdgeHornMinimalLeg n).app c
  let l := (coneCriticalEdgeHornSharpLeg n).app c
  let r := (coneCriticalHornDiagramMark n).app c
  have hc : f ≫ l = g ≫ r := congrArg (fun x => x.app c) (coneCriticalEdgeHornFree_condition n)
  let _ : IsIso (forget.map f) := by
    change IsIso (𝟙 _)
    infer_instance
  let _ : IsIso (forget.map r) := by
    change IsIso (𝟙 _)
    infer_instance
  have hw : CommSq (forget.map f) (forget.map g) (forget.map l) (forget.map r) :=
    ⟨(forget.map_comp f l).symm.trans ((congrArg forget.map hc).trans (forget.map_comp g r))⟩
  have hp := IsPushout.of_horiz_isIso hw
  apply isColimitOfUnderlyingMarking
    ((isColimitMapCoconePushoutCoconeEquiv forget hc).symm hp.isColimit)
  intro e he
  rcases (coneCriticalWeight_marked_iff n i e.val).mp he with h | ⟨h₀, h₁⟩
  · exact ⟨WalkingSpan.right, e, h, rfl⟩
  · exact ⟨WalkingSpan.left, (coneCriticalEdgePathWord n i e.val h₀, coneCriticalIntervalWord),
      ⟨Set.mem_univ _, Set.mem_univ _⟩, coneCriticalEdgeHornSharpLeg_represents n i e h₀ h₁⟩

end SSet.Marked.CoherentWeight
