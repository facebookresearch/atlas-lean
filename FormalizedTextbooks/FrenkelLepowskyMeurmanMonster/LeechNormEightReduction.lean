/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Constructive transitivity on actual norm-eight Leech vectors. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightTransition

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A vector of square sum 64 with first coordinate 8 is exactly the positive coordinate axis. -/
theorem leechNormEight_eq_axis_of_first (u : Fin 24 → ℤ)
    (hs : leechSquareSum u = 64) (h0 : u 0 = 8) : u = Pi.single 0 8 := by
  have hr : ∑ i ∈ (Finset.univ : Finset (Fin 24)).erase 0, u i ^ 2 = 0 := by
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin 24))
      (fun i => u i ^ 2) (Finset.mem_univ (0 : Fin 24))
    change _ + u 0 ^ 2 = leechSquareSum u at he
    rw [h0, hs] at he
    linarith
  funext i
  by_cases hi : i = 0
  · subst i
    simpa using h0
  · have hb : u i ^ 2 ≤ ∑ j ∈ (Finset.univ : Finset (Fin 24)).erase 0, u j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j))
        (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    rw [hr] at hb
    have hz : u i = 0 := by nlinarith
    simp [hi, hz]

/-- The terminal shape is normalized by the actual monomial subgroup. -/
theorem leechNormEight_shape_zero_reduction (u : leechIntegral)
    (hs : leechSquareSum u.val = 64)
    (hshape : leechNormEightMultiplicity u.val = leechNormEightShapeCounts 0) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      (leechIntegralAction e u).val = Pi.single 0 8 := by
  obtain ⟨e, he, hr⟩ := leechNormEight_monomial_preparation u 0 hshape
  refine ⟨e, he, leechNormEight_eq_axis_of_first _
    (by rw [leechIntegralAction_squareSum, hs]) ?_⟩
  exact hr 0

/-- Strong induction on the explicit shape rank completes the actual generator reduction. -/
theorem leechNormEight_concrete_reduction_of_shape (u : leechIntegral) (s : Fin 8)
    (hs : leechSquareSum u.val = 64)
    (hshape : leechNormEightMultiplicity u.val = leechNormEightShapeCounts s) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      (leechIntegralAction e u).val = Pi.single 0 8 := by
  have hmain : ∀ n : ℕ, ∀ s : Fin 8, leechNormEightShapeRank s = n →
      ∀ u : leechIntegral, leechSquareSum u.val = 64 →
        leechNormEightMultiplicity u.val = leechNormEightShapeCounts s →
        ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
          (leechIntegralAction e u).val = Pi.single 0 8 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn u hs hshape
      by_cases hz : s = 0
      · subst s
        exact leechNormEight_shape_zero_reduction u hs hshape
      · obtain ⟨e, he, t, ht, hlt⟩ :=
          leechNormEight_concrete_rank_step u s hs hshape hz
        obtain ⟨f, hf, haxis⟩ := ih (leechNormEightShapeRank t) (by omega) t rfl
          (leechIntegralAction e u) (by rw [leechIntegralAction_squareSum, hs]) ht
        refine ⟨f * e, leechConcreteGeneratorSubgroup.mul_mem hf he, ?_⟩
        simpa only [map_mul, LinearEquiv.mul_apply] using haxis
  exact hmain (leechNormEightShapeRank s) s rfl u hs hshape

/-- Every actual norm-eight vector is sent to +8e₀ by the concrete Golay and ξ generators. -/
theorem leechNormEight_concrete_transitive (u : leechIntegral)
    (hs : leechSquareSum u.val = 64) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      (leechIntegralAction e u).val = Pi.single 0 8 := by
  obtain ⟨s, hshape⟩ := leechNormEight_catalog u hs
  exact leechNormEight_concrete_reduction_of_shape u s hs hshape

/-- The same transitivity statement as an equality inside the actual integral lattice. -/
theorem leechNormEight_concrete_transitive_lattice (u : leechIntegral)
    (hs : leechSquareSum u.val = 64) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      leechIntegralAction e u = leechEightEmbedding (Pi.single (0 : Fin 24) 1) := by
  obtain ⟨e, he, haxis⟩ := leechNormEight_concrete_transitive u hs
  refine ⟨e, he, Subtype.ext ?_⟩
  rw [haxis]
  ext i
  simp [leechEightEmbedding, Pi.single_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
