/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalTriple

/-! The two odd shapes represent the same actual monomial family modulo twice the lattice. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The genuine signed first-octad short vector used to change the normalized triple shape. -/
def monsterCo1PolarTripleShort : Fin 24 → ℤ :=
  fun i => if i = 1 ∨ i = 2 then -2 else if i.val < 8 then 2 else 0

/-- This literal signed octad vector is in the actual source lattice. -/
theorem monsterCo1PolarTripleShort_mem : monsterCo1PolarTripleShort ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, golayStandardOctad, golayStandardOctad_mem, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

/-- The normalized triple vector itself satisfies the genuine source lattice congruences. -/
theorem monsterCo1PolarTripleVector_mem : monsterCo1PolarTripleVector ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨1, Or.inr rfl, 0, golayCode.zero_mem, ?_, ?_⟩
  · intro i
    simp only [Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero]
    revert i
    decide +kernel
  · decide +kernel

/-- Subtracting twice the short vector gives a pentad on the last five octad positions. -/
theorem monsterCo1PolarTriple_sub_short :
    monsterCo1PolarTripleVector - (monsterCo1PolarTripleShort + monsterCo1PolarTripleShort) =
      monsterCo1PolarPentadVector (Finset.univ.filter fun i : Fin 24 => 3 ≤ i.val ∧ i.val < 8) := by
  decide +kernel

/-- The short-vector subtraction leaves the genuine lattice quotient class unchanged. -/
theorem monsterCo1PolarTriple_reduction :
    leechReduction ⟨monsterCo1PolarTripleVector, monsterCo1PolarTripleVector_mem⟩ =
      leechReduction ⟨monsterCo1PolarPentadVector
        (Finset.univ.filter fun i : Fin 24 => 3 ≤ i.val ∧ i.val < 8),
        monsterCo1PolarPentadVector_mem _ (by decide +kernel)⟩ := by
  let t : leechIntegral := ⟨monsterCo1PolarTripleVector, monsterCo1PolarTripleVector_mem⟩
  let w : leechIntegral := ⟨monsterCo1PolarTripleShort, monsterCo1PolarTripleShort_mem⟩
  have hv : t - (w + w) = ⟨monsterCo1PolarPentadVector
      (Finset.univ.filter fun i : Fin 24 => 3 ≤ i.val ∧ i.val < 8),
      monsterCo1PolarPentadVector_mem _ (by decide +kernel)⟩ :=
    Subtype.ext monsterCo1PolarTriple_sub_short
  rw [← hv, map_sub, map_add, ZModModule.add_self, sub_zero]

/-- An actual permutation transports each normalized triple's quotient class to a pentad class. -/
theorem monsterCo1PolarLocal_triple_reduction (u : leechIntegral)
    (hn : leechSquareSum u.val = 64) (hr : ∀ i, (u.val i : ZMod 4) = 1)
    (hs : leechNormEightMultiplicity u.val = leechNormEightShapeCounts 6) :
    ∃ p : golayAutomorphismSubgroup,
      leechReduction (leechIntegralAction (golayPermutationIsometry p) u) =
        leechReduction ⟨monsterCo1PolarPentadVector
          (Finset.univ.filter fun i : Fin 24 => 3 ≤ i.val ∧ i.val < 8),
          monsterCo1PolarPentadVector_mem _ (by decide +kernel)⟩ := by
  obtain ⟨p, hp⟩ := monsterCo1PolarLocal_triple_to_standard u hn hr hs
  refine ⟨p, ?_⟩
  have hu : leechIntegralAction (golayPermutationIsometry p) u =
      ⟨monsterCo1PolarTripleVector, monsterCo1PolarTripleVector_mem⟩ := by
    apply Subtype.ext
    rw [leechIntegralAction_golayPermutation, hp]
  rw [hu]
  exact monsterCo1PolarTriple_reduction

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
