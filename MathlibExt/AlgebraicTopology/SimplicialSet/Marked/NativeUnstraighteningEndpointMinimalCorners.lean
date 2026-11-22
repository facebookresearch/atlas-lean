/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningEndpointMinimalPrism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningEndpointPrismMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductUnit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.BoundaryCells

/-!
# Original minimally marked boundary parameters in native endpoint corners

The original minimally marked boundary cell and original marked endpoint
retain their whole marked pushout. Its original boundary verticals lift
through the same native prism filtration, and the target row carries
only the actual minimal parameter marks. The same original marked
product triangles preserve every target prism mark under an actual
coherent-model fibration. No scalar, diagram or base fibrancy is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

private def rightMinimalPointUnit (T : SSet.{u}) : prod (min T) (min (Δ[0] : SSet.{u})) ≅ min T :=
  prodSwapIso (min T) (min (Δ[0] : SSet.{u})) ≪≫ zeroParameterUnitIso .minimal (min T)

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
    (rightMinimalPointUnitUnderlying T).inv ≫ (prodMap (𝟙 (min T)) f).hom = prismSectionAt T ε :=
  (congrArg (fun g => (rightMinimalPointUnitUnderlying T).inv ≫ ((𝟙 T) ⊗ₘ g)) hf).trans
    (minimalPoint_native_graph T ε)

private theorem minimalPoint_unit_natural {T T' : SSet.{u}} (a : T ⟶ T') :
    (rightMinimalPointUnitUnderlying T).inv ≫
        (prodMap (minimal.map a) (𝟙 (min (Δ[0] : SSet.{u})))).hom =
      a ≫ (rightMinimalPointUnitUnderlying T').inv := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro j
    exact Fin.eq_zero _

/-- Every original whole marked scalar-boundary/endpoint corner lifts the same native map of an actual
coherent-model fibration. -/
theorem nativeUnstraightening_map_endpointMinimalBoundaryCornerLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (n : ℕ) :
    let _ := coherentDiagramModelCategory B
    Fibration q → HasLiftingProperty (markedPushoutProduct cartesianEndpointCell.{u} (boundaryCell.{u} n))
      ((nativeUnstraightening B).map q).left := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let a := (boundary.{u} n).ι
  let sq := markedProductPushout cartesianEndpointCell.{u} (boundaryCell.{u} n)
  let p : nativeUnstraighteningTotal B F ⟶ nativeUnstraighteningTotal B G :=
    ((nativeUnstraightening B).map q).left
  refine ⟨fun {top bottom} h => ?_⟩
  let Hmarked : prod (min (boundary.{u} n : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ nativeUnstraighteningTotal B F :=
    sq.inl ≫ top
  let cmarked : min (Δ[n] : SSet.{u}) ⟶ nativeUnstraighteningTotal B F :=
    (rightMinimalPointUnit (Δ[n] : SSet.{u})).inv ≫ sq.inr ≫ top
  let H : (boundary.{u} n : SSet.{u}) ⊗ Δ[1] ⟶ (nativeUnstraighteningTotal B F).toSSet := Hmarked.hom
  let c : (Δ[n] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet := cmarked.hom
  let K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B G).toSSet := bottom.hom
  have hw : (prodMap (𝟙 (min (boundary.{u} n : SSet.{u}))) cartesianEndpointCell).hom ≫ H =
      (prodMap (minimal.map a) (𝟙 (min (Δ[0] : SSet.{u})))).hom ≫ (sq.inr ≫ top).hom :=
    congrArg Hom.hom (congrArg (fun f => f ≫ top) sq.isPushout.w)
  let uA : (boundary.{u} n : SSet.{u}) ⟶ (boundary.{u} n : SSet.{u}) ⊗ Δ[0] :=
    (rightMinimalPointUnitUnderlying (boundary.{u} n : SSet.{u})).inv
  let uD : (Δ[n] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) ⊗ Δ[0] :=
    (rightMinimalPointUnitUnderlying (Δ[n] : SSet.{u})).inv
  let tA : (boundary.{u} n : SSet.{u}) ⊗ Δ[0] ⟶ (boundary.{u} n : SSet.{u}) ⊗ Δ[1] :=
    (prodMap (𝟙 (min (boundary.{u} n : SSet.{u}))) cartesianEndpointCell).hom
  let tD : (Δ[n] : SSet.{u}) ⊗ Δ[0] ⟶ (Δ[n] : SSet.{u}) ⊗ Δ[1] :=
    (prodMap (𝟙 (min (Δ[n] : SSet.{u}))) cartesianEndpointCell).hom
  let tB : (boundary.{u} n : SSet.{u}) ⊗ Δ[0] ⟶ (Δ[n] : SSet.{u}) ⊗ Δ[0] :=
    (prodMap (minimal.map a) (𝟙 (min (Δ[0] : SSet.{u})))).hom
  let cD : (Δ[n] : SSet.{u}) ⊗ Δ[0] ⟶ (nativeUnstraighteningTotal B F).toSSet := (sq.inr ≫ top).hom
  have hgA : uA ≫ tA = prismSectionAt (boundary.{u} n : SSet.{u}) 1 :=
    minimalPoint_endpoint_graph _ 1 cartesianEndpointCell rfl
  have hgD : uD ≫ tD = prismSectionAt (Δ[n] : SSet.{u}) 1 :=
    minimalPoint_endpoint_graph _ 1 cartesianEndpointCell rfl
  have hn : uA ≫ tB = a ≫ uD := minimalPoint_unit_natural a
  have hc : c = uD ≫ cD := rfl
  have hHsrc : prismSectionAt (boundary.{u} n : SSet.{u}) 1 ≫ H = a ≫ c := by
    exact (congrArg (fun f => f ≫ H) hgA.symm).trans
      ((Category.assoc uA tA H).trans
        ((congrArg (fun f => uA ≫ f) hw).trans
          ((Category.assoc uA tB cD).symm.trans
            ((congrArg (fun f => f ≫ cD) hn).trans
              ((Category.assoc a uD cD).trans (congrArg (fun f => a ≫ f) hc.symm))))))
  have hHmarkedBase : (sq.inl ≫ top) ≫ p = (prodMap (minimal.map a) (𝟙 (max (Δ[1] : SSet.{u})))) ≫ bottom := by
    have hside : sq.inl ≫ markedPushoutProduct cartesianEndpointCell (boundaryCell n) =
        prodMap (minimal.map a) (𝟙 (max (Δ[1] : SSet.{u}))) := sq.inl_ι
    exact (Category.assoc sq.inl top p).trans
      ((congrArg (fun f => sq.inl ≫ f) h.w).trans
        ((Category.assoc sq.inl (markedPushoutProduct cartesianEndpointCell (boundaryCell n)) bottom).symm.trans
          (congrArg (fun f => f ≫ bottom) hside)))
  have hHbase : H ≫ p.hom = (a ▷ (Δ[1] : SSet.{u})) ≫ K := congrArg Hom.hom hHmarkedBase
  have hcDbase : cD ≫ p.hom = tD ≫ K := by
    have hside : sq.inr ≫ markedPushoutProduct cartesianEndpointCell (boundaryCell n) =
        prodMap (𝟙 (min (Δ[n] : SSet.{u}))) cartesianEndpointCell := sq.inr_ι
    have hbase : (sq.inr ≫ top) ≫ p =
        (prodMap (𝟙 (min (Δ[n] : SSet.{u}))) cartesianEndpointCell) ≫ bottom :=
      (Category.assoc sq.inr top p).trans
        ((congrArg (fun f => sq.inr ≫ f) h.w).trans
          ((Category.assoc sq.inr (markedPushoutProduct cartesianEndpointCell (boundaryCell n)) bottom).symm.trans
            (congrArg (fun f => f ≫ bottom) hside)))
    exact congrArg Hom.hom hbase
  have hcbase : c ≫ p.hom = prismSectionAt (Δ[n] : SSet.{u}) 1 ≫ K := by
    exact (congrArg (fun f => f ≫ p.hom) hc).trans
      ((Category.assoc uD cD p.hom).trans
        ((congrArg (fun f => uD ≫ f) hcDbase).trans
          ((Category.assoc uD tD K).symm.trans (congrArg (fun f => f ≫ K) hgD))))
  have hv : nativePrismOneVerticalsMarked B F H := by
    intro x
    exact Hmarked.preserve (show verticalOneSimplex x ∈
      (prod (min (boundary.{u} n : SSet.{u})) (max (Δ[1] : SSet.{u}))).marking from
      ⟨(min (boundary.{u} n : SSet.{u})).degenerate_mem x, Set.mem_univ _⟩)
  obtain ⟨L, hLr, hLt, hLp, hLv⟩ := nativeUnstraightening_endpointPrism_boundary_minimal B q n
    H c bottom hHsrc hcbase.symm hHbase hv hq
  let l : prod (min (Δ[n] : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ nativeUnstraighteningTotal B F :=
    nativeMarkedEndpointPrismOfTarget B q L bottom hLp hLv (by
      intro e hm
      have he : (prismSectionAt (Δ[n] : SSet.{u}) 1 ≫ L).app (op ⦋1⦌) e = c.app (op ⦋1⦌) e :=
        congrArg (fun f => f.app (op ⦋1⦌) e) hLt
      exact he.symm ▸ cmarked.preserve hm) hq
  refine CommSq.HasLift.mk' ⟨l, ?_, ?_⟩
  · apply sq.isPushout.hom_ext
    · apply Hom.ext
      change (sq.inl.hom ≫ (markedPushoutProduct cartesianEndpointCell (boundaryCell n)).hom) ≫ L = H
      exact (congrArg (fun f => f.hom ≫ L) sq.inl_ι).trans hLr
    · apply Hom.ext
      apply (cancel_epi (rightMinimalPointUnitUnderlying (Δ[n] : SSet.{u})).inv).mp
      have ht : sq.inr.hom ≫ (markedPushoutProduct cartesianEndpointCell (boundaryCell n)).hom = tD :=
        congrArg Hom.hom sq.inr_ι
      change uD ≫ ((sq.inr.hom ≫ (markedPushoutProduct cartesianEndpointCell (boundaryCell n)).hom) ≫ L) = c
      exact (congrArg (fun g => uD ≫ (g ≫ L)) ht).trans
        (((Category.assoc _ _ _).symm).trans ((congrArg (fun g => g ≫ L) hgD).trans hLt))
  · exact Hom.ext hLp


end SSet.Marked
