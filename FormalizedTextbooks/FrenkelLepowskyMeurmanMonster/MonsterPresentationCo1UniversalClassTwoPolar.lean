/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The original source commutators have the actual nondegenerate Conway polar pairing. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoQuadratic

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every source commutator coefficient is the actual Conway polar pairing of its coordinates. -/
theorem co1UniversalCommutatorPairing_eq_polar
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (v w : Fin 24 → ZMod 2) :
    co1UniversalCommutatorPairing v w = co1BinaryPolar v w := by
  have h := co1UniversalSquareCoefficient_add hfinite hcard w v
  simp only [co1UniversalSquareCoefficient_eq_squareQuad hfinite hcard hne] at h
  rw [add_comm w v] at h
  rw [co1BinaryPolar_quadratic]
  linear_combination -h

/-- The genuine source commutator bilinear form is exactly the actual Conway polar form. -/
theorem co1UniversalCommutatorBilin_eq_polar
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    co1UniversalCommutatorBilin hfinite hcard = co1BinaryPolar := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  exact co1UniversalCommutatorPairing_eq_polar hfinite hcard hne v w

/-- Vanishing of every source commutator against a binary coordinate forces that coordinate zero. -/
theorem co1UniversalCommutatorPairing_nondegenerate
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (v : Fin 24 → ZMod 2)
    (hv : ∀ w, co1UniversalCommutatorPairing v w = 0) : v = 0 := by
  have hz : co1BinaryPolar v = 0 := by
    apply LinearMap.ext
    intro w
    rw [← co1UniversalCommutatorPairing_eq_polar hfinite hcard hne]
    exact hv w
  exact co1BinaryPolarEquiv.injective (hz.trans (map_zero co1BinaryPolarEquiv).symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
