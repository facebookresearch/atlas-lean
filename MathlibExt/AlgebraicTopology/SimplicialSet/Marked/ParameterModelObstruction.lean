/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PointEndpointAuxiliaryRight
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PointEndpointWeakEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PointEndpointMonoRight

/-!
# The actual auxiliary marked WFS is not the genuine model WFS

Over the original point, the fully marked source endpoint is a Cartesian
cell-right map and is mapping weak, but it is not monomorphism-right: it
misses the other original vertex. The target endpoint gives the dual
cocartesian counterexample. Since the original endpoint is monic, these
also disprove identification of the auxiliary cell-left class with all
weak marked monomorphisms. Genuine marked model recognition must use a
larger local testing trivial-cofibration WFS. No model or straightening
outcome is assumed here.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty
open scoped Simplicial

namespace SSet.Marked

/-- The original Cartesian auxiliary right class contains a genuine weak monomorphism that is not mono-right. -/
theorem cartesianAuxiliaryRight_weak_not_monoRight :
    Mono (pointEndpoint.{u} (1 : Fin 2)) ∧
      (cartesianCellsOver (Δ[0] : SSet.{u})).rlp (pointEndpoint.{u} 1) ∧
      cartesianWeakEquivalences (Δ[0] : SSet.{u}) (pointEndpoint.{u} 1) ∧
      ¬ (monomorphisms (Over (max (Δ[0] : SSet.{u})))).rlp (pointEndpoint.{u} 1) :=
  ⟨pointEndpoint_mono 1, pointSourceEndpoint_cartesianAuxiliaryRight,
    pointSourceEndpoint_cartesian_weak, pointEndpoint_not_monoRight 1⟩

/-- The actual cocartesian auxiliary right class has the corresponding original target-endpoint counterexample. -/
theorem cocartesianAuxiliaryRight_weak_not_monoRight :
    Mono (pointEndpoint.{u} (0 : Fin 2)) ∧
      (cocartesianCellsOver (Δ[0] : SSet.{u})).rlp (pointEndpoint.{u} 0) ∧
      cocartesianWeakEquivalences (Δ[0] : SSet.{u}) (pointEndpoint.{u} 0) ∧
      ¬ (monomorphisms (Over (max (Δ[0] : SSet.{u})))).rlp (pointEndpoint.{u} 0) :=
  ⟨pointEndpoint_mono 0, pointTargetEndpoint_cocartesianAuxiliaryRight,
    pointTargetEndpoint_cocartesian_weak, pointEndpoint_not_monoRight 0⟩

/-- The Cartesian auxiliary cell-right weak intersection is strictly different from the genuine monomorphism
  right class. -/
theorem cartesianAuxiliaryRight_inf_weak_ne_monoRight :
    (cartesianCellsOver (Δ[0] : SSet.{u})).rlp ⊓ cartesianWeakEquivalences (Δ[0] : SSet.{u}) ≠
      (monomorphisms (Over (max (Δ[0] : SSet.{u})))).rlp := by
  intro h
  have hx : ((cartesianCellsOver (Δ[0] : SSet.{u})).rlp ⊓ cartesianWeakEquivalences (Δ[0] : SSet.{u}))
      (pointEndpoint.{u} 1) :=
    ⟨pointSourceEndpoint_cartesianAuxiliaryRight, pointSourceEndpoint_cartesian_weak⟩
  exact pointEndpoint_not_monoRight 1 (h ▸ hx)

/-- The dual cocartesian auxiliary intersection also fails the genuine right-class equality. -/
theorem cocartesianAuxiliaryRight_inf_weak_ne_monoRight :
    (cocartesianCellsOver (Δ[0] : SSet.{u})).rlp ⊓ cocartesianWeakEquivalences (Δ[0] : SSet.{u}) ≠
      (monomorphisms (Over (max (Δ[0] : SSet.{u})))).rlp := by
  intro h
  have hx : ((cocartesianCellsOver (Δ[0] : SSet.{u})).rlp ⊓ cocartesianWeakEquivalences (Δ[0] : SSet.{u}))
      (pointEndpoint.{u} 0) :=
    ⟨pointTargetEndpoint_cocartesianAuxiliaryRight, pointTargetEndpoint_cocartesian_weak⟩
  exact pointEndpoint_not_monoRight 0 (h ▸ hx)

/-- Neither original endpoint can lift against itself: the whole right equation would supply its missing vertex. -/
theorem pointEndpoint_not_self_lifting (ε : Fin 2) :
    ¬ HasLiftingProperty (pointEndpoint.{u} ε) (pointEndpoint.{u} ε) := by
  intro h
  let _ : HasLiftingProperty (pointEndpoint.{u} ε) (pointEndpoint.{u} ε) := h
  let i := pointEndpoint.{u} ε
  let sq : CommSq (𝟙 _) i i (𝟙 _) := ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩
  have hr : sq.lift.left.hom ≫ i.left.hom = 𝟙 _ := congrArg (fun f => f.left.hom) sq.fac_right
  apply pointEndpoint_not_surjective_zero ε
  intro y
  refine ⟨sq.lift.left.hom.app (Opposite.op ⦋0⦌) y, ?_⟩
  exact ConcreteCategory.congr_hom (congr_app hr (Opposite.op ⦋0⦌)) y

/-- The auxiliary Cartesian cell-left class omits the actual weak monic vertical source endpoint. -/
theorem pointSourceEndpoint_not_cartesianAuxiliaryLeft :
    ¬ (cartesianCellsOver (Δ[0] : SSet.{u})).rlp.llp (pointEndpoint.{u} 1) := by
  intro h
  exact pointEndpoint_not_self_lifting 1 (h _ pointSourceEndpoint_cartesianAuxiliaryRight)

/-- The corresponding actual weak monic target endpoint is omitted by the cocartesian auxiliary left class. -/
theorem pointTargetEndpoint_not_cocartesianAuxiliaryLeft :
    ¬ (cocartesianCellsOver (Δ[0] : SSet.{u})).rlp.llp (pointEndpoint.{u} 0) := by
  intro h
  exact pointEndpoint_not_self_lifting 0 (h _ pointTargetEndpoint_cocartesianAuxiliaryRight)

/-- Actual Cartesian weak monomorphisms strictly exceed the unchanged auxiliary cell-left class. -/
theorem cartesianAuxiliaryLeft_ne_weakMonomorphisms :
    (cartesianCellsOver (Δ[0] : SSet.{u})).rlp.llp ≠
      monomorphisms (Over (max (Δ[0] : SSet.{u}))) ⊓ cartesianWeakEquivalences (Δ[0] : SSet.{u}) := by
  intro h
  have hx : (monomorphisms (Over (max (Δ[0] : SSet.{u}))) ⊓ cartesianWeakEquivalences (Δ[0] : SSet.{u}))
      (pointEndpoint.{u} 1) := ⟨pointEndpoint_mono 1, pointSourceEndpoint_cartesian_weak⟩
  exact pointSourceEndpoint_not_cartesianAuxiliaryLeft (h.symm ▸ hx)

/-- The unchanged cocartesian auxiliary cell-left class likewise is not the full actual weak monomorphism class. -/
theorem cocartesianAuxiliaryLeft_ne_weakMonomorphisms :
    (cocartesianCellsOver (Δ[0] : SSet.{u})).rlp.llp ≠
      monomorphisms (Over (max (Δ[0] : SSet.{u}))) ⊓ cocartesianWeakEquivalences (Δ[0] : SSet.{u}) := by
  intro h
  have hx : (monomorphisms (Over (max (Δ[0] : SSet.{u}))) ⊓ cocartesianWeakEquivalences (Δ[0] : SSet.{u}))
      (pointEndpoint.{u} 0) := ⟨pointEndpoint_mono 0, pointTargetEndpoint_cocartesian_weak⟩
  exact pointTargetEndpoint_not_cocartesianAuxiliaryLeft (h.symm ▸ hx)

end SSet.Marked
