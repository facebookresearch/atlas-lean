/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- All six original point vertices commute with each abstract A11 closing root. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationWreathLocalGenerationClosingRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonCandidates
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every letter of the literal closing-root word is a vertex of its two-arm path. -/
theorem y555A11ClosingWord_mem_path (a b : Fin 3) (v : Y555Vertex)
    (hv : v ∈ y555A11ClosingWord a b) : ∃ i : Fin 11, y555A11Path a b i = v := by
  simp only [y555A11ClosingWord, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨3, rfl⟩
    | exact ⟨4, rfl⟩
    | exact ⟨5, rfl⟩
    | exact ⟨6, rfl⟩
    | exact ⟨7, rfl⟩
    | exact ⟨8, rfl⟩
    | exact ⟨9, rfl⟩
    | exact ⟨10, rfl⟩

/-- A source generator commuting with the entire path commutes with its closing root. -/
theorem y555A11ClosingRoot_commute_external (a b : Fin 3) (v : Y555Vertex)
    (hv : ∀ i : Fin 11, Commute
      (PresentedGroup.of (y555A11Path a b i) : BimonsterPresentation) (PresentedGroup.of v)) :
    Commute (y555A11ClosingRoot a b) (PresentedGroup.of v) := by
  apply Commute.list_prod_left
  intro g hg
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
  obtain ⟨i, rfl⟩ := y555A11ClosingWord_mem_path a b u hu
  exact hv i

private theorem closing_point_generators_commute (u v : Y555Vertex) (huv : u ≠ v)
    (ha : ¬ y555Adjacent u v) :
    Commute (PresentedGroup.of u : BimonsterPresentation) (PresentedGroup.of v) := by
  have h := y555_coxeter_relation u v huv
  simp only [ha, ↓reduceIte, pow_two] at h
  have hi := eq_inv_of_mul_eq_one_left h
  have hiu : (PresentedGroup.of u : BimonsterPresentation)⁻¹ = PresentedGroup.of u := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using y555_generator_sq u
  have hiv : (PresentedGroup.of v : BimonsterPresentation)⁻¹ = PresentedGroup.of v := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using y555_generator_sq v
  change (PresentedGroup.of u : BimonsterPresentation) * PresentedGroup.of v = _
  simpa only [mul_inv_rev, hiu, hiv] using hi

/-- Every two-arm closing root commutes with all six original point vertices. -/
theorem y555A11ClosingRoot_commute_point (a b : Fin 3) (hab : a ≠ b) (p : Fin 6) :
    Commute (y555A11ClosingRoot a b) (PresentedGroup.of (y555NortonPointVertex p)) := by
  rw [y555A11ClosingRoot_eq_reflection]
  have hChain := y555A11Chain_relations a b hab
  fin_cases a <;> fin_cases b <;> fin_cases p <;> norm_num at hab
  all_goals first
    | simpa [y555A11Generators, y555A11Path, y555NortonPointVertex] using
        typeAClosingReflection_commute_interior hChain 1
          (by omega) (by omega)
    | simpa [y555A11Generators, y555A11Path, y555NortonPointVertex] using
        typeAClosingReflection_commute_interior hChain 3
          (by omega) (by omega)
    | simpa [y555A11Generators, y555A11Path, y555NortonPointVertex] using
        typeAClosingReflection_commute_interior hChain 7
          (by omega) (by omega)
    | simpa [y555A11Generators, y555A11Path, y555NortonPointVertex] using
        typeAClosingReflection_commute_interior hChain 9
          (by omega) (by omega)
    | rw [← y555A11ClosingRoot_eq_reflection]
      apply y555A11ClosingRoot_commute_external
      intro i
      apply closing_point_generators_commute
      all_goals fin_cases i <;> decide +kernel

/-- The three exact abstract closing-root witnesses commute with all six original point vertices. -/
theorem monsterWreathClosingRoot_commute_point (i : Fin 3) (p : Fin 6) :
    Commute (monsterWreathClosingRoot i) (PresentedGroup.of (y555NortonPointVertex p)) := by
  apply y555A11ClosingRoot_commute_point
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
