/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningEndpointMinimalCorners
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningEndpointPrismMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductUnit

/-!
# The original endpoint and edge-mark parameter corner has native lifts

The whole original minimally parameter-marked interval prism already
supplies the underlying map and marked verticals. Its original marked
target row supplies the newly marked scalar edge. Actual native
relative composition and cancellation preserve every original product
mark. The full original marked pushout and both side equations retain
the same whole marked diagonal, with no diagram or base fibrancy.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

private def rightMinimalPointUnit (T : SSet.{u}) : prod (max T) (min (Δ[0] : SSet.{u})) ≅ max T :=
  prodSwapIso (max T) (min (Δ[0] : SSet.{u})) ≪≫ zeroParameterUnitIso .minimal (max T)

private def rightMinimalPointUnitUnderlying (T : SSet.{u}) : T ⊗ (Δ[0] : SSet.{u}) ≅ T :=
  forget.mapIso (rightMinimalPointUnit T)

private theorem minimalPoint_inv_eq_section (T : SSet.{u}) :
    (rightMinimalPointUnitUnderlying T).inv = prismSectionZero T := by
  apply CartesianMonoidalCategory.hom_ext
  · change 𝟙 T = prismSectionZero T ≫ CartesianMonoidalCategory.fst T (Δ[0] : SSet.{u})
    rw [← prismSectionAt_zero]
    exact (prismSectionAt_comp_fst T (0 : Fin 1)).symm
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem minimalPoint_native_graph (T : SSet.{u}) (ε : Fin 2) :
    (rightMinimalPointUnitUnderlying T).inv ≫ ((𝟙 T) ⊗ₘ stdSimplex.δ ε.rev) = prismSectionAt T ε := by
  rw [minimalPoint_inv_eq_section]
  fin_cases ε
  · exact prismSectionZero_whiskerLeft_δ_one T
  · exact prismSectionZero_whiskerLeft_δ_zero T

private theorem minimalPoint_endpoint_graph (T : SSet.{u}) (ε : Fin 2)
    (f : min (Δ[0] : SSet.{u}) ⟶ max (Δ[1] : SSet.{u}))
    (hf : f.hom = stdSimplex.δ ε.rev) :
    (rightMinimalPointUnitUnderlying T).inv ≫ (prodMap (𝟙 (max T)) f).hom = prismSectionAt T ε :=
  (congrArg (fun g => (rightMinimalPointUnitUnderlying T).inv ≫ ((𝟙 T) ⊗ₘ g)) hf).trans
    (minimalPoint_native_graph T ε)

/-- The original minimally-to-maximally marked parameter edge keeps its entire identity on the interval-prism
carrier. -/
theorem nativeEndpointParameterMarking_tensor_hom :
    (prodMap edgeMarkCell.{u} (𝟙 (max (Δ[1] : SSet.{u})))).hom =
      𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1]) := rfl

/-- Its original point-row parameter map likewise retains its whole identity. -/
theorem nativeEndpointParameterMarking_point_hom :
    (prodMap edgeMarkCell.{u} (𝟙 (min (Δ[0] : SSet.{u})))).hom =
      𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[0]) := rfl

/-- Every same original endpoint/edge-marking parameter corner lifts the actual native map of an actual
coherent-model fibration, through the original full marked prism and both side equations. -/
theorem nativeUnstraightening_map_endpointMarkingCornerLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → HasLiftingProperty (markedPushoutProduct cartesianEndpointCell.{u} edgeMarkCell.{u})
      ((nativeUnstraightening B).map q).left := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let p : nativeUnstraighteningTotal B F ⟶ nativeUnstraighteningTotal B G :=
    ((nativeUnstraightening B).map q).left
  let sq := markedProductPushout cartesianEndpointCell.{u} edgeMarkCell.{u}
  refine ⟨fun {top bottom} h => ?_⟩
  let Hmarked : prod (min (Δ[1] : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ nativeUnstraighteningTotal B F :=
    sq.inl ≫ top
  let L : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet := Hmarked.hom
  let cmarked : max (Δ[1] : SSet.{u}) ⟶ nativeUnstraighteningTotal B F :=
    (rightMinimalPointUnit (Δ[1] : SSet.{u})).inv ≫ sq.inr ≫ top
  let u : (Δ[1] : SSet.{u}) ⟶ (Δ[1] ⊗ Δ[0] : SSet.{u}) :=
    (rightMinimalPointUnitUnderlying (Δ[1] : SSet.{u})).inv
  let t : (Δ[1] ⊗ Δ[0] : SSet.{u}) ⟶ (Δ[1] ⊗ Δ[1] : SSet.{u}) :=
    (prodMap (𝟙 (min (Δ[1] : SSet.{u}))) cartesianEndpointCell).hom
  let cD := (sq.inr ≫ top).hom
  have hg : u ≫ t = prismSectionAt (Δ[1] : SSet.{u}) 1 :=
    minimalPoint_endpoint_graph _ 1 cartesianEndpointCell rfl
  have hw : t ≫ L = (prodMap edgeMarkCell.{u} (𝟙 (min (Δ[0] : SSet.{u})))).hom ≫ cD :=
    congrArg Hom.hom (congrArg (fun f => f ≫ top) sq.isPushout.w)
  have hpoint : t ≫ L = cD := hw.trans
    ((congrArg (fun f => f ≫ cD) nativeEndpointParameterMarking_point_hom).trans (Category.id_comp cD))
  have hrow : prismSectionAt (Δ[1] : SSet.{u}) 1 ≫ L = cmarked.hom :=
    (congrArg (fun f => f ≫ L) hg.symm).trans
      ((Category.assoc u t L).trans (congrArg (fun f => u ≫ f) hpoint))
  have hleft : (sq.inl ≫ top) ≫ p = (prodMap edgeMarkCell.{u} (𝟙 (max (Δ[1] : SSet.{u})))) ≫ bottom := by
    have hside : sq.inl ≫ markedPushoutProduct cartesianEndpointCell.{u} edgeMarkCell.{u} =
        prodMap edgeMarkCell.{u} (𝟙 (max (Δ[1] : SSet.{u}))) := sq.inl_ι
    exact (Category.assoc sq.inl top p).trans
      ((congrArg (fun f => sq.inl ≫ f) h.w).trans
        ((Category.assoc sq.inl (markedPushoutProduct cartesianEndpointCell edgeMarkCell) bottom).symm.trans
          (congrArg (fun f => f ≫ bottom) hside)))
  have hbase : L ≫ p.hom = bottom.hom := (congrArg Hom.hom hleft).trans
    ((congrArg (fun f => f ≫ bottom.hom) nativeEndpointParameterMarking_tensor_hom).trans (Category.id_comp bottom.hom))
  have hv : nativePrismOneVerticalsMarked B F L := by
    intro x
    exact Hmarked.preserve (show verticalOneSimplex x ∈
      (prod (min (Δ[1] : SSet.{u})) (max (Δ[1] : SSet.{u}))).marking from
      ⟨(min (Δ[1] : SSet.{u})).degenerate_mem x, Set.mem_univ _⟩)
  let l : prod (max (Δ[1] : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ nativeUnstraighteningTotal B F :=
    nativeMarkedEndpointPrismOfTarget B q L bottom hbase hv (by
      intro e he
      have hr := congrArg (fun f => f.app (op ⦋1⦌) e) hrow
      exact hr.symm ▸ cmarked.preserve he) hq
  refine CommSq.HasLift.mk' ⟨l, ?_, Hom.ext hbase⟩
  apply sq.isPushout.hom_ext
  · apply Hom.ext
    change (sq.inl.hom ≫ (markedPushoutProduct cartesianEndpointCell edgeMarkCell).hom) ≫ L = L
    exact (congrArg (fun f => f.hom ≫ L) sq.inl_ι).trans
      ((congrArg (fun f => f ≫ L) nativeEndpointParameterMarking_tensor_hom).trans (Category.id_comp L))
  · apply Hom.ext
    apply (cancel_epi u).mp
    have ht : sq.inr.hom ≫ (markedPushoutProduct cartesianEndpointCell edgeMarkCell).hom = t :=
      congrArg Hom.hom sq.inr_ι
    change u ≫ ((sq.inr.hom ≫ (markedPushoutProduct cartesianEndpointCell edgeMarkCell).hom) ≫ L) = u ≫ cD
    exact (congrArg (fun f => u ≫ (f ≫ L)) ht).trans (congrArg (fun f => u ≫ f) hpoint)

end SSet.Marked
