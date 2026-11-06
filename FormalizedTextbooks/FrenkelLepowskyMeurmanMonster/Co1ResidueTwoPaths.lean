/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueLocalRepresentation
public import Mathlib.GroupTheory.Commutator.Basic

/-! Ivanov II Lemma 2.2.3 for the actual source presentation. Abelianity of the
neighborhood quotients is an explicit input, rather than a consequence of binary pairing. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- The exact residue abelianity required by the source two-path argument. -/
def co1ResidueQuotientsAbelian : Prop :=
  ∀ p : MonsterCo1GeometryPoint, ∀ a b : Co1ResidueLocalQuotient p, Commute a b

/-- When the actual residue quotient is abelian, the commutator of two neighbors is
identity or the distinguished point involution. -/
theorem co1Residue_neighbor_commutator_cases (h : co1ResidueQuotientsAbelian)
    (w u v : MonsterCo1GeometryPoint)
    (hu : monsterCo1GeometryAdjacent w u) (hv : monsterCo1GeometryAdjacent w v) :
    ⁅(PresentedGroup.of u : Co1UniversalPresentation),
      (PresentedGroup.of v : Co1UniversalPresentation)⁆ = 1 ∨
      ⁅(PresentedGroup.of u : Co1UniversalPresentation),
      (PresentedGroup.of v : Co1UniversalPresentation)⁆ =
        PresentedGroup.of w := by
  let a : co1ResidueLocal w := ⟨PresentedGroup.of u, co1ResidueLocal_neighbor_mem w u hu⟩
  let b : co1ResidueLocal w := ⟨PresentedGroup.of v, co1ResidueLocal_neighbor_mem w v hv⟩
  have hm : QuotientGroup.mk' (co1ResidueBaseKernel w) ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact (h w _ _).commutator_eq
  have hk : ⁅a, b⁆ ∈ co1ResidueBaseKernel w := (QuotientGroup.eq_one_iff _).mp hm
  rcases (co1ResidueBaseKernel_mem_iff w ⁅a, b⁆).mp hk with h1 | h2
  · exact Or.inl (congrArg (fun g : co1ResidueLocal w => g.val) h1)
  · exact Or.inr (congrArg (fun g : co1ResidueLocal w => g.val) h2)

/-- Two distinct genuine common neighbors force commutation, once the actual residue
quotients are abelian. Distinctness uses faithful source point images, not an assumed quotient. -/
theorem co1Residue_commute_of_two_common_neighbors (h : co1ResidueQuotientsAbelian)
    (u v w z : MonsterCo1GeometryPoint) (hwz : w ≠ z)
    (hwu : monsterCo1GeometryAdjacent w u) (hwv : monsterCo1GeometryAdjacent w v)
    (hzu : monsterCo1GeometryAdjacent z u) (hzv : monsterCo1GeometryAdjacent z v) :
    Commute (PresentedGroup.of u : Co1UniversalPresentation) (PresentedGroup.of v) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rcases co1Residue_neighbor_commutator_cases h w u v hwu hwv with h1 | hw
  · exact h1
  rcases co1Residue_neighbor_commutator_cases h z u v hzu hzv with h1 | hz
  · exact h1
  exact False.elim (hwz (co1UniversalPoint_injective (hw.symm.trans hz)))

/-- The genuine distance-at-most-two commutation consequence with the required two-path
geometry exposed. This statement does not identify graph distance with polar orthogonality. -/
theorem co1Residue_commute_of_close_geometry (h : co1ResidueQuotientsAbelian)
    (u v : MonsterCo1GeometryPoint)
    (hclose : u = v ∨ monsterCo1GeometryAdjacent u v ∨
      ∃ w z : MonsterCo1GeometryPoint, w ≠ z ∧
        monsterCo1GeometryAdjacent w u ∧ monsterCo1GeometryAdjacent w v ∧
        monsterCo1GeometryAdjacent z u ∧ monsterCo1GeometryAdjacent z v) :
    Commute (PresentedGroup.of u : Co1UniversalPresentation) (PresentedGroup.of v) := by
  rcases hclose with rfl | hadj | ⟨w, z, hwz, hwu, hwv, hzu, hzv⟩
  · exact Commute.refl _
  · exact co1UniversalPoint_commute_of_adjacent u v hadj
  · exact co1Residue_commute_of_two_common_neighbors h u v w z hwz hwu hwv hzu hzv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
