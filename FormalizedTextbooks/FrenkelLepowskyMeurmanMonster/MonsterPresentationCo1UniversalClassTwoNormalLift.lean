/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The ordered source block lifts realize the actual extraspecial coordinate section. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoHalfCoordinates

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- The actual-coordinate source section, with second block preceding first block. -/
def co1UniversalNormalLift
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (v : Fin 24 → ZMod 2) :
    Co1UniversalPresentation :=
  co1UniversalHalfLift hfinite hcard hne 1
      (Multiplicative.ofAdd (fun i => v (Fin.natAdd 12 i))) *
    co1UniversalHalfLift hfinite hcard hne 0
      (Multiplicative.ofAdd (fun i => v (Fin.castAdd 12 i)))

/-- The ordered source section takes the zero coordinate to the identity. -/
theorem co1UniversalNormalLift_zero
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    co1UniversalNormalLift hfinite hcard hne 0 = 1 := by
  change co1UniversalHalfLift hfinite hcard hne 1 1 *
    co1UniversalHalfLift hfinite hcard hne 0 1 = 1
  rw [map_one, map_one, one_mul]

/-- The actual binary image of the entire ordered source section is its original coordinate. -/
theorem co1UniversalNormalLift_image
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (v : Fin 24 → ZMod 2) :
    co1UniversalIntoBinary (co1UniversalNormalLift hfinite hcard hne v) =
      Multiplicative.ofAdd v := by
  change co1UniversalIntoBinary (_ * _) = _
  rw [map_mul, co1UniversalHalfLift_image, co1UniversalHalfLift_image]
  apply congrArg Multiplicative.ofAdd
  change co1UniversalHalfVector 1 (fun i => v (Fin.natAdd 12 i)) +
    co1UniversalHalfVector 0 (fun i => v (Fin.castAdd 12 i)) = v
  rw [add_comm]
  exact co1UniversalHalfVector_reconstruct v

/-- Swapping the opposite source blocks gives precisely the actual cocycle coefficient. -/
theorem co1UniversalHalfLift_cross_commutator
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (v w : Fin 24 → ZMod 2) :
    ⁅co1UniversalHalfLift hfinite hcard hne 0
        (Multiplicative.ofAdd (fun i => v (Fin.castAdd 12 i))),
      co1UniversalHalfLift hfinite hcard hne 1
        (Multiplicative.ofAdd (fun i => w (Fin.natAdd 12 i)))⁆ =
      co1UniversalCentralEmbedding hfinite hcard hne (Multiplicative.ofAdd (qBeta v w)) := by
  rw [co1UniversalCommutator_eq_central_polar hfinite hcard hne,
    co1UniversalHalfLift_image, co1UniversalHalfLift_image]
  change co1UniversalCentralEmbedding hfinite hcard hne
    (Multiplicative.ofAdd (co1BinaryPolar
      (co1UniversalHalfVector 0 (fun i => v (Fin.castAdd 12 i)))
      (co1UniversalHalfVector 1 (fun i => w (Fin.natAdd 12 i))))) = _
  rw [co1UniversalHalfVector_polar]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
