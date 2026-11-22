/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathRowPointFibre
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The whole point-fibre target of the Segal path comparison

The original source-edge family is pulled back at the actual entire
tail simplex. Native pullback pasting retains both original legs and
identifies that target with the existing mapping fibre from x to the
original first vertex of that same tail.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

private theorem congrHom_fst {X Y Z : SSet.{u}} (f : X ⟶ Z) {a c : Y ⟶ Z} (h : a = c) :
    (pullback.congrHom (show f = f from rfl) h).hom ≫ pullback.fst f c = pullback.fst f a := by
  subst c
  simp [pullback.congrHom_hom, pullback.map]

/-- The complete original point fibre of the leading-edge family target. -/
abbrev leadingEdgePointTarget (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) : SSet.{u} :=
  pullback (pullback.snd (sourceEdgesTarget W x) (InitialEdgeTailMapping.tailFirstVertex W n)) b

/-- The whole target is the original mapping fibre through its same actual pullback legs. -/
def leadingEdgePointTargetIso (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    leadingEdgePointTarget W x n b ≅ mappingFibre W x (tailFirstPoint W n b) :=
  pullbackLeftPullbackSndIso (sourceEdgesTarget W x) (InitialEdgeTailMapping.tailFirstVertex W n) b ≪≫
    pullback.congrHom rfl (by simp only [tailFirstPoint, Equiv.symm_apply_apply]) ≪≫
      (mappingSourceTargetIso W x (tailFirstPoint W n b)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The entire target isomorphism retains the actual original leading edge. -/
theorem leadingEdgePointTargetIso_edge (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    (leadingEdgePointTargetIso W x n b).hom ≫ mappingFibre.fst W x (tailFirstPoint W n b) =
      pullback.fst (pullback.snd (sourceEdgesTarget W x) (InitialEdgeTailMapping.tailFirstVertex W n)) b ≫
        pullback.fst (sourceEdgesTarget W x) (InitialEdgeTailMapping.tailFirstVertex W n) ≫
          pullback.fst (W.diagram.δ (1 : Fin 2)) (SSet.yonedaEquiv.symm x) := by
  unfold leadingEdgePointTargetIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, mappingSourceTargetIso,
    sourceTargetFibreToMapping, pullback.lift_fst]
  have hc : b ≫ InitialEdgeTailMapping.tailFirstVertex W n =
      SSet.yonedaEquiv.symm (tailFirstPoint W n b) := by
    simp only [tailFirstPoint, Equiv.symm_apply_apply]
  have hi := congrHom_fst (sourceEdgesTarget W x) hc
  have hp := pullbackLeftPullbackSndIso_hom_fst
    (sourceEdgesTarget W x) (InitialEdgeTailMapping.tailFirstVertex W n) b
  calc
    _ = ((pullbackLeftPullbackSndIso (sourceEdgesTarget W x)
        (InitialEdgeTailMapping.tailFirstVertex W n) b).hom ≫
        (pullback.congrHom (show sourceEdgesTarget W x = sourceEdgesTarget W x from rfl) hc).hom ≫
        pullback.fst (sourceEdgesTarget W x) (SSet.yonedaEquiv.symm (tailFirstPoint W n b))) ≫
        pullback.fst (W.diagram.δ (1 : Fin 2)) (SSet.yonedaEquiv.symm x) := by
      simp only [Category.assoc]
    _ = ((pullbackLeftPullbackSndIso (sourceEdgesTarget W x)
        (InitialEdgeTailMapping.tailFirstVertex W n) b).hom ≫
        pullback.fst (sourceEdgesTarget W x) (b ≫ InitialEdgeTailMapping.tailFirstVertex W n)) ≫ _ :=
      congrArg (fun q => q ≫ _) (congrArg
        (fun q => (pullbackLeftPullbackSndIso (sourceEdgesTarget W x)
          (InitialEdgeTailMapping.tailFirstVertex W n) b).hom ≫ q) hi)
    _ = _ := congrArg (fun q => q ≫ _) hp

end SimplicialSpace.LeftDecalageObject
