/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual local polar connectivity reduces source group recognition to polar-zero commutation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoAbelian
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalConnected

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Genuine polar-orthogonal commutation forces the original source group abelian. -/
theorem co1Universal_commutator_eq_bot_of_polar_commutation
    (hclose : ∀ p q : MonsterCo1GeometryPoint, ¬ monsterCo1GeometryPolarAdjacent p q →
      Commute (PresentedGroup.of p : Co1UniversalPresentation) (PresentedGroup.of q)) :
    commutator Co1UniversalPresentation = ⊥ := by
  obtain ⟨hf, hc⟩ := co1Universal_commutator_card_le_two_of_polar_geometry
    monsterCo1Geometry_polar_local_connected hclose
  exact co1Universal_commutator_eq_bot_of_finite_card_le_two hf hc

/-- Exact original genuine-line source group recognition, with polar-zero commutation explicit. -/
def co1UniversalBinaryEquivOfPolarCommutation
    (hclose : ∀ p q : MonsterCo1GeometryPoint, ¬ monsterCo1GeometryPolarAdjacent p q →
      Commute (PresentedGroup.of p : Co1UniversalPresentation) (PresentedGroup.of q)) :
    Co1UniversalPresentation ≃* Multiplicative (Fin 24 → ZMod 2) :=
  co1UniversalBinaryEquivOfBound
    (co1Universal_commutator_card_le_two_of_polar_geometry
      monsterCo1Geometry_polar_local_connected hclose).1
    (co1Universal_commutator_card_le_two_of_polar_geometry
      monsterCo1Geometry_polar_local_connected hclose).2

/-- The conditional source isomorphism takes every original point to its actual binary vector. -/
theorem co1UniversalBinaryEquivOfPolarCommutation_point
    (hclose : ∀ p q : MonsterCo1GeometryPoint, ¬ monsterCo1GeometryPolarAdjacent p q →
      Commute (PresentedGroup.of p : Co1UniversalPresentation) (PresentedGroup.of q))
    (p : MonsterCo1GeometryPoint) :
    co1UniversalBinaryEquivOfPolarCommutation hclose (PresentedGroup.of p) =
      Multiplicative.ofAdd p.val := co1UniversalIntoBinary_point p

/-- The conditional source isomorphism retains the exact action of every actual Conway element. -/
theorem co1UniversalBinaryEquivOfPolarCommutation_action
    (hclose : ∀ p q : MonsterCo1GeometryPoint, ¬ monsterCo1GeometryPolarAdjacent p q →
      Commute (PresentedGroup.of p : Co1UniversalPresentation) (PresentedGroup.of q))
    (g : Co1) (x : Co1UniversalPresentation) :
    co1UniversalBinaryEquivOfPolarCommutation hclose (co1UniversalRepresentation g x) =
      Multiplicative.ofAdd (co1BinaryAction g
        (co1UniversalBinaryEquivOfPolarCommutation hclose x).toAdd) :=
  co1UniversalIntoBinary_action g x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
