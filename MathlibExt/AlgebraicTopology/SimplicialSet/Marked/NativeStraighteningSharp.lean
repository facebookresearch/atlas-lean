/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningSimplex
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningSharpFibre

/-!
# The native straightening chart of an original marked edge

The chart is the actual enriched left extension of the sharp cone
weight along the original coherent edge. Native interval Yoneda,
the actual unit pullback and the proved sharp section fibre identify
its whole marked Hom with the original sharp interval slice Hom into
unstraightening. No representation or adjunction outcome is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

private def swapPredicates {A : Type u} (P Q : A → Prop) :
    {a : {x : A // P x} // Q a.val} ≃ {a : {x : A // Q x} // P a.val} where
  toFun a := ⟨⟨a.val.val, a.property⟩, a.val.property⟩
  invFun a := ⟨⟨a.val.val, a.property⟩, a.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The original sharp interval basis is the exact whole marked edge over the supplied original base. -/
def nativeSharpBasis (B : SSet.{u}) (σ : B _⦋1⦌) : Over (max B) :=
  Over.mk (toMax (SSet.yonedaEquiv.symm σ) : max (Δ[1] : SSet.{u}) ⟶ max B)

/-- The actual native sharp chart is its original whole sharp-cone enriched left extension. -/
def nativeSharpChart (B : SSet.{u}) (σ : B _⦋1⦌) : EnrichedDiagram (realization B)ᵒᵖ :=
  EnrichedLeftKan.object (EnrichedFunctor.opposite (simplexInto B σ)) (sharpConeDiagram 1)

/-- Native marked interval maps retain their exact original fixed-base marked unstraightening edge. -/
def nativeSharpUnMarkedFibreEquiv (B : SSet.{u}) (σ : B _⦋1⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    (nativeSharpBasis B σ ⟶ (nativeUnstraightening B).obj F) ≃
      {a : {e : UnstraighteningSimplex F 1 // e.base = simplexInto B σ} //
        a.val ∈ (coherentUnstraightening (realization B) F).marking} :=
  ((Over.mapPullbackAdj (maximal.map (unit B))).homEquiv
    (nativeSharpBasis B σ) ((coherentUnstraighteningFunctor (realization B)).obj F)).symm.trans
    ((overMaxIntervalHomEquiv ((coherentUnstraighteningFunctor (realization B)).obj F)
      (toMax (SSet.yonedaEquiv.symm σ ≫ unit B) : max (Δ[1] : SSet.{u}) ⟶
        max (coherentBase (realization B)))).trans
      ((Equiv.subtypeEquiv (Equiv.refl _) (fun a => by
        change (a.val.base = SSet.yonedaEquiv (SSet.yonedaEquiv.symm σ ≫ unit B)) ↔
          a.val.base = simplexInto B σ
        rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
        rfl)).trans
        (swapPredicates (fun a => a ∈ (coherentUnstraightening (realization B) F).marking)
          (fun a => a.base = simplexInto B σ))))

/-- Native marked interval maps into unstraightening are exactly the original sharp-cone sections over the
  same base edge. -/
def nativeSharpUnSectionEquiv (B : SSet.{u}) (σ : B _⦋1⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    (nativeSharpBasis B σ ⟶ (nativeUnstraightening B).obj F) ≃
      EnrichedDiagramMap (sharpConeDiagram 1) (simplexCoefficient F (simplexInto B σ)) :=
  (nativeSharpUnMarkedFibreEquiv B σ F).trans (fixedSharpSectionEquiv F (simplexInto B σ))

/-- The actual sharp chart represents precisely the original whole sharp-edge slice Hom into native unstraightening. -/
def nativeSharpChartHomEquiv (B : SSet.{u}) (σ : B _⦋1⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    (nativeSharpChart B σ ⟶ F) ≃ (nativeSharpBasis B σ ⟶ (nativeUnstraightening B).obj F) :=
  (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (sharpConeDiagram 1) F).trans
    (nativeSharpUnSectionEquiv B σ F).symm

end SSet.Marked
