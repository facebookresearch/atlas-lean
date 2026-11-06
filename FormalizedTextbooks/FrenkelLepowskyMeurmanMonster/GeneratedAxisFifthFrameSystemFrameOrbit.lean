/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemGenerators

/-! The full original section/system stabilizer is transitive on its fifteen actual frames. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Six original system-preserving permutations followed by the original Xi. -/
def generatedFifthFrameGenerator (k : Fin 7) : leechIsomSubgroup :=
  if h : k.val < 6 then
    golayPermutationIsometry (generatedFifthMonomialSpatialPermutation ⟨k.val, h⟩)
  else co1XiIsometry

/-- The actual finite frame-class transitions of these original generators. -/
def generatedFifthFrameTransition (k : Fin 7) : Fin 15 → Fin 15 :=
  if h : k.val < 6 then generatedFifthMonomialFrameImageIndex ⟨k.val, h⟩
  else generatedFifthFrameSignXiTarget 12

/-- Every finite frame transition is the original quotient action. -/
theorem generatedFifthFrameGenerator_action (k : Fin 7) (j : Fin 15) :
    generatedFifthFrameGenerator k • generatedFifthFrameClass j =
      generatedFifthFrameClass (generatedFifthFrameTransition k j) := by
  by_cases h : k.val < 6
  · simp only [generatedFifthFrameGenerator, generatedFifthFrameTransition, h]
    exact generatedFifthMonomial_frame_class _ j
  · simp only [generatedFifthFrameGenerator, generatedFifthFrameTransition, h]
    exact generatedFifthFrameSignXi_action 12 j

/-- Each original frame generator belongs to the full actual section/system stabilizer. -/
theorem generatedFifthFrameGenerator_mem (k : Fin 7) :
    generatedFifthFrameGenerator k ∈ generatedFifthFrameSystemStabilizer := by
  by_cases h : k.val < 6
  · simp only [generatedFifthFrameGenerator, h]
    exact generatedFifthFrameSystem_monomial_mem _
  · simp only [generatedFifthFrameGenerator, h]
    exact generatedFifthFrameSystem_xi_mem

/-- Original words reaching each of the fifteen genuine classes from the original frame. -/
def generatedFifthFrameWord : Fin 15 → List (Fin 7) :=
  ![[], [0, 4, 6], [0, 6, 4, 6], [2, 0, 4, 6], [6, 6, 4, 6], [1, 5, 4, 6], [1, 6, 5, 4, 6], [6],
    [6, 6], [2, 4, 6], [6, 2, 4, 6], [4, 6], [6, 4, 6], [5, 4, 6], [6, 5, 4, 6]]

/-- The original words genuinely reach all fifteen classes in the actual quotient. -/
theorem generatedFifthFrame_word_action (j : Fin 15) :
    ((generatedFifthFrameWord j).map generatedFifthFrameGenerator).prod •
      generatedFifthFrameClass 0 = generatedFifthFrameClass j := by
  fin_cases j <;> simp [generatedFifthFrameWord, mul_smul, generatedFifthFrameGenerator_action,
    generatedFifthFrameTransition, generatedFifthMonomialFrameImageIndex,
    generatedFifthFrameSignXiTarget]

/-- Each actual frame word belongs to the full original stabilizer. -/
theorem generatedFifthFrame_word_mem (j : Fin 15) :
    ((generatedFifthFrameWord j).map generatedFifthFrameGenerator).prod ∈
      generatedFifthFrameSystemStabilizer := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hg
  exact generatedFifthFrameGenerator_mem k

/-- The fifteen original actual quotient classes are distinct. -/
theorem generatedFifthFrameClass_injective : Function.Injective generatedFifthFrameClass := by
  intro i j h
  have he := congrArg leechHyperbolicCoordinates h
  apply generatedFifthFrameIncidentClass_injective
  simpa only [generatedFifthFrameClass, LinearEquiv.apply_symm_apply] using he

/-- The full actual section/system stabilizer has precisely the fifteen nonzero frame images. -/
theorem generatedFifthFrameSystem_frame_orbit :
    MulAction.orbit generatedFifthFrameSystemStabilizer (generatedFifthFrameClass 0) =
      Set.range generatedFifthFrameClass := by
  ext b
  constructor
  · rintro ⟨g, rfl⟩
    have hm : leechModTwoAction g.val (generatedFifthFrameClass 0) ∈
        generatedFifthFrameSystem.map (leechModTwoAction g.val).toLinearMap :=
      Submodule.mem_map.mpr ⟨_, generatedFifthMonomial_frame_mem 0, rfl⟩
    rw [((generatedAxisE8FrameSystemStabilizer_mem generatedFifthFlagOctad
      generatedFifthFrameSystem g.val).mp g.property).2] at hm
    have hn : leechModTwoAction g.val (generatedFifthFrameClass 0) ≠ 0 := by
      intro h
      have he := (leechModTwoAction g.val).injective (h.trans (map_zero _).symm)
      have hz := congrArg leechHyperbolicCoordinates he
      exact generatedFifthFrameIncidentClass_ne_zero 0
        (by simpa only [generatedFifthFrameClass, LinearEquiv.apply_symm_apply, map_zero] using hz)
    obtain ⟨j, hj⟩ := generatedFifthFrameSystem_class_cover _ hm hn
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨_, generatedFifthFrame_word_mem j⟩, generatedFifthFrame_word_action j⟩

/-- The full actual section/system stabilizer acts transitively on exactly fifteen frame classes. -/
theorem generatedFifthFrameSystem_frame_orbit_card :
    Nat.card (MulAction.orbit generatedFifthFrameSystemStabilizer (generatedFifthFrameClass 0)) =
      15 := by
  rw [generatedFifthFrameSystem_frame_orbit,
    ← Nat.card_congr (Equiv.ofInjective generatedFifthFrameClass
      generatedFifthFrameClass_injective)]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
