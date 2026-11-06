/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual hyperbolic coordinate preimages satisfy the source extraspecial relations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoCentralEmbedding

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- A chosen original source preimage of one actual binary coordinate unit. -/
def co1UniversalBasisLift (i : Fin 24) : Co1UniversalPresentation :=
  co1UniversalBinaryLift (Pi.single i 1)

/-- The chosen source coordinate element retains its full actual coordinate image. -/
theorem co1UniversalBasisLift_image (i : Fin 24) :
    co1UniversalIntoBinary (co1UniversalBasisLift i) = Multiplicative.ofAdd (Pi.single i 1) :=
  co1UniversalBinaryLift_image _

/-- Actual coordinate units are isotropic for the actual squares form. -/
theorem co1Universal_coordinate_square (i : Fin 24) :
    squareQuad (Pi.single i 1) = 0 := by
  have h : ∀ i : Fin 24, squareQuad (Pi.single i 1) = 0 := by decide +kernel
  exact h i

/-- Every chosen source coordinate preimage is an involution under the explicit bound. -/
theorem co1UniversalBasisLift_square
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (i : Fin 24) :
    co1UniversalBasisLift i ^ 2 = 1 := by
  have hs : co1UniversalSquareCoefficient (Pi.single i 1) = 0 := by
    rw [co1UniversalSquareCoefficient_eq_squareQuad hfinite hcard hne,
      co1Universal_coordinate_square]
  have hz := (co1UniversalCommutatorCoefficient_eq_zero
    (co1UniversalBinarySquare (Pi.single i 1))).mp hs
  exact congrArg Subtype.val hz

/-- Every source commutator equals the central embedding of its actual polar coefficient. -/
theorem co1UniversalCommutator_eq_central_polar
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (x y : Co1UniversalPresentation) :
    ⁅x, y⁆ = co1UniversalCentralEmbedding hfinite hcard hne
      (Multiplicative.ofAdd (co1BinaryPolar
        (co1UniversalIntoBinary x).toAdd (co1UniversalIntoBinary y).toAdd)) := by
  have h := co1UniversalCentralEmbedding_coefficient hfinite hcard hne
    (co1UniversalCommutator x y)
  have hc : co1UniversalCommutatorCoefficient (co1UniversalCommutator x y) =
      co1BinaryPolar (co1UniversalIntoBinary x).toAdd (co1UniversalIntoBinary y).toAdd := by
    rw [← co1UniversalBinaryCommutator_image hfinite hcard]
    exact co1UniversalCommutatorPairing_eq_polar hfinite hcard hne _ _
  rw [hc] at h
  exact h.symm

/-- The first and second actual hyperbolic blocks of coordinate indices. -/
def co1UniversalHalfIndex (b : Fin 2) (i : Fin 12) : Fin 24 :=
  if b = 0 then Fin.castAdd 12 i else Fin.natAdd 12 i

/-- Every individual actual hyperbolic block is totally isotropic for the polar pairing. -/
theorem co1UniversalHalfIndex_polar (b : Fin 2) (i j : Fin 12) :
    co1BinaryPolar (Pi.single (co1UniversalHalfIndex b i) 1)
      (Pi.single (co1UniversalHalfIndex b j) 1) = 0 := by
  have h : ∀ b : Fin 2, ∀ i j : Fin 12,
      co1BinaryPolar (Pi.single (co1UniversalHalfIndex b i) 1)
        (Pi.single (co1UniversalHalfIndex b j) 1) = 0 := by decide +kernel
  exact h b i j

/-- Chosen preimages within either actual hyperbolic block commute in the original source group. -/
theorem co1UniversalBasisLift_half_commute
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (b : Fin 2) (i j : Fin 12) :
    Commute (co1UniversalBasisLift (co1UniversalHalfIndex b i))
      (co1UniversalBasisLift (co1UniversalHalfIndex b j)) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [co1UniversalCommutator_eq_central_polar hfinite hcard hne,
    co1UniversalBasisLift_image, co1UniversalBasisLift_image]
  change co1UniversalCentralEmbedding hfinite hcard hne
    (Multiplicative.ofAdd (co1BinaryPolar (Pi.single (co1UniversalHalfIndex b i) 1)
      (Pi.single (co1UniversalHalfIndex b j) 1))) = 1
  rw [co1UniversalHalfIndex_polar]
  exact map_one _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
