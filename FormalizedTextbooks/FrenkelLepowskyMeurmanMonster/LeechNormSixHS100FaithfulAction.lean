/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100Catalog

/-! The original canonical root, pair, and twenty-two odd points determine every ambient coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The entire original integer lattice vector in unscaled real coordinates. -/
def leechNormSixHS100RawVector (z : leechIntegral) : Fin 24 → ℝ :=
  Real.sqrt 8 • leechCoordinateEmbedding z.val

/-- Removing the common physical normalization retains every original integer coordinate. -/
theorem leechNormSixHS100RawVector_coordinate (z : leechIntegral) (i : Fin 24) :
    leechNormSixHS100RawVector z i = (z.val i : ℝ) := by
  change Real.sqrt 8 * ((z.val i : ℝ) / Real.sqrt 8) = _
  have hs : Real.sqrt 8 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp

/-- Fixation by the original integral action fixes the entire unscaled physical vector. -/
theorem leechNormSixHS100RawVector_fixed (g : leechIsomSubgroup) (z : leechIntegral)
    (hz : leechIntegralAction g z = z) :
    g.val (leechNormSixHS100RawVector z) = leechNormSixHS100RawVector z := by
  rw [leechNormSixHS100RawVector, map_smul, ← leechIntegralAction_embedding, hz]

/-- The sum of the twenty-two original odd points minus the positive pair is eighteen times all-one. -/
theorem leechNormSixHS100RawVector_sum_odd :
    (∑ j : Fin 24, if j = 0 ∨ j = 1 then 0 else
      leechNormSixHS100RawVector (leechNormSixHS100Odd j)) -
        leechNormSixHS100RawVector leechNormSixHS100Pair =
      (18 : ℝ) • (fun _ : Fin 24 => (1 : ℝ)) := by
  funext i
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      leechNormSixHS100RawVector_coordinate, leechNormSixHS100Odd_coordinate,
      leechNormSixHS100Pair, leechNormSixHS100PairIntegral]

/-- The complete original root, positive pair, and outside odd vectors determine every ambient isometry. -/
theorem leechNormSixHS100CanonicalVectors_determine (g : leechIsomSubgroup)
    (hx : leechIntegralAction g leechNormSixHS100Root = leechNormSixHS100Root)
    (hp : leechIntegralAction g leechNormSixHS100Pair = leechNormSixHS100Pair)
    (ho : ∀ j : Fin 24, j ≠ 0 → j ≠ 1 →
      leechIntegralAction g (leechNormSixHS100Odd j) = leechNormSixHS100Odd j) : g = 1 := by
  have hxr := leechNormSixHS100RawVector_fixed g leechNormSixHS100Root hx
  have hpr := leechNormSixHS100RawVector_fixed g leechNormSixHS100Pair hp
  have hor (j : Fin 24) (h0 : j ≠ 0) (h1 : j ≠ 1) :=
    leechNormSixHS100RawVector_fixed g (leechNormSixHS100Odd j) (ho j h0 h1)
  have hsum : g.val (∑ j : Fin 24, if j = 0 ∨ j = 1 then 0 else
      leechNormSixHS100RawVector (leechNormSixHS100Odd j)) =
    ∑ j : Fin 24, if j = 0 ∨ j = 1 then 0 else
      leechNormSixHS100RawVector (leechNormSixHS100Odd j) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = 0 ∨ j = 1
    · simp [hj]
    · have h0 : j ≠ 0 := fun h => hj (Or.inl h)
      have h1 : j ≠ 1 := fun h => hj (Or.inr h)
      simpa only [hj, ↓reduceIte] using hor j h0 h1
  have hone : g.val (fun _ : Fin 24 => (1 : ℝ)) = fun _ : Fin 24 => (1 : ℝ) := by
    have h := congrArg g.val leechNormSixHS100RawVector_sum_odd
    rw [map_sub, hsum, hpr, leechNormSixHS100RawVector_sum_odd, map_smul] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    linarith
  have haxis (j : Fin 24) : g.val (Pi.single j 1) = (Pi.single j 1 : Fin 24 → ℝ) := by
    by_cases h0 : j = 0
    · subst j
      have he : leechNormSixHS100RawVector leechNormSixHS100Root +
          leechNormSixHS100RawVector leechNormSixHS100Pair =
            (8 : ℝ) • (Pi.single 0 1 : Fin 24 → ℝ) := by
        ext i
        by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
          norm_num [Pi.add_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul,
            leechNormSixHS100RawVector_coordinate, leechNormSixHS100Root,
            leechNormSixHS100RootIntegral, leechNormSixHS100Pair,
            leechNormSixHS100PairIntegral, h0, h1]
      have h := congrArg g.val he
      rw [map_add, hxr, hpr, he, map_smul] at h
      ext i
      have hi := congrFun h i
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      linarith
    · by_cases h1 : j = 1
      · subst j
        have he : leechNormSixHS100RawVector leechNormSixHS100Pair -
            leechNormSixHS100RawVector leechNormSixHS100Root =
              (8 : ℝ) • (Pi.single 1 1 : Fin 24 → ℝ) := by
          ext i
          by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
            norm_num [Pi.sub_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul,
              leechNormSixHS100RawVector_coordinate, leechNormSixHS100Root,
              leechNormSixHS100RootIntegral, leechNormSixHS100Pair,
              leechNormSixHS100PairIntegral, h0, h1]
        have h := congrArg g.val he
        rw [map_sub, hpr, hxr, he, map_smul] at h
        ext i
        have hi := congrFun h i
        simp only [Pi.smul_apply, smul_eq_mul] at hi
        linarith
      · have he : (fun _ : Fin 24 => (1 : ℝ)) -
            leechNormSixHS100RawVector (leechNormSixHS100Odd j) =
              (4 : ℝ) • (Pi.single j 1 : Fin 24 → ℝ) := by
          ext i
          by_cases hi : i = j <;>
            norm_num [Pi.sub_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul,
              leechNormSixHS100RawVector_coordinate, leechNormSixHS100Odd_coordinate, hi]
        have h := congrArg g.val he
        rw [map_sub, hone, hor j h0 h1, he, map_smul] at h
        ext i
        have hi := congrFun h i
        simp only [Pi.smul_apply, smul_eq_mul] at hi
        linarith
  apply Subtype.ext
  apply LinearEquiv.ext
  intro u
  have hu : u = ∑ i, u i • (Pi.single i 1 : Fin 24 → ℝ) := by
    ext i
    simp [Pi.single_apply]
  rw [hu, map_sum]
  simp only [map_smul, haxis]
  rfl

/-- Fixing every actual canonical point fixes the whole original Conway isometry. -/
theorem leechNormSixHS100Points_fix_all
    (g : leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion)
    (hg : ∀ z : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion,
      g • z = z) : g = 1 := by
  apply Subtype.ext
  apply leechNormSixHS100CanonicalVectors_determine
  · exact ((leechNormSixActualPairStabilizer_mem _ _ g.val).mp g.property).1
  · exact congrArg Subtype.val (hg ⟨leechNormSixHS100Pair, leechNormSixHS100Pair_point⟩)
  · intro j h0 h1
    exact congrArg Subtype.val (hg ⟨leechNormSixHS100Odd j, leechNormSixHS100Odd_point j h0 h1⟩)

/-- The original group embeds faithfully into permutations of its complete one-hundred-point geometry. -/
theorem leechNormSixHS100Points_permutation_injective : Function.Injective
    (MulAction.toPermHom
      (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion)
      (LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply leechNormSixHS100Points_fix_all g
  intro z
  exact congrArg (fun p => p z) hg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
