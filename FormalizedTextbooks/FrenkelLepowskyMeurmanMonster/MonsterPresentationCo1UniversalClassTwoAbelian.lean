/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual nonsplitting excludes the nonabelian bounded case of the independent source group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoQAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitExact

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual nonsplit Conway action excludes a nontrivial bounded source commutator. -/
theorem co1Universal_commutator_eq_bot_of_finite_card_le_two
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) :
    commutator Co1UniversalPresentation = ⊥ := by
  by_contra hne
  exact co1BinaryAction_no_automorphism_lift
    ⟨co1UniversalQAction hfinite hcard hne, co1UniversalQAction_binary hfinite hcard hne⟩

/-- Under the explicit bound, the actual natural source binary quotient is faithful. -/
theorem co1UniversalIntoBinary_injective_of_finite_card_le_two
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) :
    Function.Injective co1UniversalIntoBinary :=
  co1UniversalIntoBinary.ker_eq_bot_iff.mp
    (co1UniversalIntoBinary_ker.trans
      (co1Universal_commutator_eq_bot_of_finite_card_le_two hfinite hcard))

/-- The exact source group is abelian once the remaining explicit commutator bound holds. -/
theorem co1Universal_commute_of_finite_card_le_two
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (x y : Co1UniversalPresentation) : Commute x y := by
  apply co1UniversalIntoBinary_injective_of_finite_card_le_two hfinite hcard
  rw [map_mul, map_mul, mul_comm]

/-- The natural isomorphism of the original source group with its actual binary coordinates.
Finiteness and order at most two of its commutator remain explicit premises. -/
def co1UniversalBinaryEquivOfBound
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) :
    Co1UniversalPresentation ≃* Multiplicative (Fin 24 → ZMod 2) :=
  MulEquiv.ofBijective co1UniversalIntoBinary
    ⟨co1UniversalIntoBinary_injective_of_finite_card_le_two hfinite hcard,
      co1UniversalIntoBinary_surjective⟩

/-- The bounded-case natural group isomorphism retains every original genuine point generator. -/
theorem co1UniversalBinaryEquivOfBound_point
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) (p : MonsterCo1GeometryPoint) :
    co1UniversalBinaryEquivOfBound hfinite hcard (PresentedGroup.of p) =
      Multiplicative.ofAdd p.val := co1UniversalIntoBinary_point p

/-- The bounded-case isomorphism preserves the exact original full Conway action. -/
theorem co1UniversalBinaryEquivOfBound_action
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (g : Co1) (x : Co1UniversalPresentation) :
    co1UniversalBinaryEquivOfBound hfinite hcard (co1UniversalRepresentation g x) =
      Multiplicative.ofAdd
        (co1BinaryAction g (co1UniversalBinaryEquivOfBound hfinite hcard x).toAdd) :=
  co1UniversalIntoBinary_action g x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
