/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadInitialSystems

/-! The nine original whole frame systems contain exactly135 different nonzero actual lattice
classes. Identification with the Ninth-axis marking is not part of this statement. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Nonzero intrinsic coordinates within an original four-dimensional frame system. -/
abbrev GeneratedNinthSpreadNonzeroCoefficient := {a : Fin 4 → ZMod 2 // a ≠ 0}

/-- Every displayed nonzero intrinsic coordinate gives its actual lattice quotient class. -/
def generatedNinthSpreadInitialPoint
    (p : Fin 9 × GeneratedNinthSpreadNonzeroCoefficient) : LeechModTwo :=
  generatedAxisE8FrameRootEmbedding
    (generatedAxisE8FrameSystemCandidateMap (generatedNinthSpreadInitialIndex p.1) p.2.val)

/-- All135 displayed nonzero points are different actual lattice quotient classes. -/
theorem generatedNinthSpreadInitialPoint_injective :
    Function.Injective generatedNinthSpreadInitialPoint := by
  intro p q h
  have he := generatedAxisE8FrameRootEmbedding_injective h
  by_cases hij : p.1 = q.1
  · apply Prod.ext hij
    apply Subtype.ext
    rw [hij] at he
    exact generatedAxisE8FrameSystemCandidateMap_injective _ he
  · rw [generatedAxisE8FrameSystemCandidateMap_bits,
      generatedAxisE8FrameSystemCandidateMap_bits] at he
    have hl := generatedAxisE8FrameLabel_left.injective he
    have hz := (generatedNinth_spread_initial_label_intersection p.1 q.1 hij
      p.2.val q.2.val hl).1
    exact False.elim (p.2.property hz)

/-- The entire union of the nine original systems with their common zero removed. -/
def generatedNinthSpreadInitialNonzero : Set LeechModTwo :=
  ⋃ i : Fin 9,
    (generatedAxisE8ActualFrameSystemCandidate (generatedNinthSpreadInitialIndex i) :
      Set LeechModTwo) \ {0}

/-- The displayed coordinates exhaust the whole nonzero union. -/
theorem generatedNinth_spread_initial_point_range :
    Set.range generatedNinthSpreadInitialPoint = generatedNinthSpreadInitialNonzero := by
  ext v
  constructor
  · rintro ⟨⟨i, a⟩, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, ⟨?_, ?_⟩⟩
    · exact Submodule.mem_map.mpr ⟨_, ⟨a.val, rfl⟩, rfl⟩
    · intro hv
      have he : generatedNinthSpreadInitialPoint (i, a) = 0 :=
        Set.mem_singleton_iff.mp hv
      have hz := generatedAxisE8FrameRootEmbedding_injective
        (he.trans (map_zero generatedAxisE8FrameRootEmbedding).symm)
      have ha := generatedAxisE8FrameSystemCandidateMap_injective _
        (hz.trans (map_zero (generatedAxisE8FrameSystemCandidateMap
          (generatedNinthSpreadInitialIndex i))).symm)
      exact a.property ha
  · intro hv
    obtain ⟨i, hi, hzero⟩ := Set.mem_iUnion.mp hv
    obtain ⟨u, hu, huv⟩ := Submodule.mem_map.mp hi
    obtain ⟨a, rfl⟩ := hu
    have ha : a ≠ 0 := by
      intro h
      apply hzero
      apply Set.mem_singleton_iff.mpr
      simpa only [h, map_zero] using huv.symm
    exact ⟨(i, ⟨a, ha⟩), huv⟩

/-- The actual nonzero union has cardinal135, derived from its injective coefficient map. -/
theorem generatedNinth_spread_initial_nonzero_card :
    Nat.card generatedNinthSpreadInitialNonzero = 135 := by
  rw [← generatedNinth_spread_initial_point_range,
    ← Nat.card_congr (Equiv.ofInjective generatedNinthSpreadInitialPoint
      generatedNinthSpreadInitialPoint_injective)]
  rw [Nat.card_prod, Nat.card_fin]
  have hc : Nat.card GeneratedNinthSpreadNonzeroCoefficient = 15 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
