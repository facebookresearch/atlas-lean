/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.PathCoupling

@[expose] public section

/-!
# Tests for path coupling

A concrete two-state chain on `Fin 2` with the metric induced by
`Fin.val`: the deterministic swap kernel `K x = pure (1 - x)` with
adjacency `x ≠ y`. The only adjacent pairs are `(0, 1)` and
`(1, 0)`, coupled by the point mass on the swapped pair. At time
`t = 1` the chains started at `0` and `1` are the point masses at
`1` and `0`, at total variation distance `1`, which equals the
bound `β^t * dist 0 1 / δ = 1` with `β = δ = 1`. The equal-start
case has distance `0` on both sides.
-/

open Finset

namespace MathlibExtTest.Probability.PathCoupling

open MathlibExt.Probability.PathCoupling

/-- The metric on `Fin 2` induced by `Fin.val`: `dist x y = |x - y|`. -/
noncomputable local instance : PseudoMetricSpace (Fin 2) :=
  PseudoMetricSpace.induced (fun i : Fin 2 => (i.val : ℝ)) inferInstance

/-- The deterministic swap kernel: `K x` is the point mass at the
other point of `Fin 2`. -/
noncomputable def flipKernel : Fin 2 → PMF (Fin 2) :=
  fun x => PMF.pure (if x = 0 then 1 else 0)

/-- Adjacency on `Fin 2`: distinct points are adjacent. -/
def swapAdj : Fin 2 → Fin 2 → Prop := fun x y => x ≠ y

/-- The adjacent coupling: the point mass on the swapped pair. -/
noncomputable def swapCoupling : ∀ x y : Fin 2, swapAdj x y → PMF (Fin 2 × Fin 2) :=
  fun x y _ => PMF.pure ((if x = 0 then 1 else 0), (if y = 0 then 1 else 0))

theorem dist_zero_one : dist (0 : Fin 2) (1 : Fin 2) = 1 := by
  have h : dist (0 : Fin 2) (1 : Fin 2)
      = dist ((0 : Fin 2).val : ℝ) ((1 : Fin 2).val : ℝ) := rfl
  rw [h]
  norm_num [Real.dist_eq]

theorem dist_one_zero : dist (1 : Fin 2) (0 : Fin 2) = 1 := by
  rw [dist_comm]
  exact dist_zero_one

theorem one_le_dist_of_ne (x y : Fin 2) (h : x ≠ y) :
    (1 : ℝ) ≤ dist x y := by
  fin_cases x <;> fin_cases y
  · exact absurd rfl h
  · simp [dist_zero_one]
  · simp [dist_one_zero]
  · exact absurd rfl h

theorem swapCoupling_fst (x y : Fin 2) (h : swapAdj x y) :
    (swapCoupling x y h).map Prod.fst = flipKernel x := by
  simp [swapCoupling, flipKernel, PMF.pure_map]

theorem swapCoupling_snd (x y : Fin 2) (h : swapAdj x y) :
    (swapCoupling x y h).map Prod.snd = flipKernel y := by
  simp [swapCoupling, flipKernel, PMF.pure_map]

theorem pure_pair_expected_dist (p : Fin 2 × Fin 2) :
    ∑ z, ((PMF.pure p) z).toReal * dist z.1 z.2 = dist p.1 p.2 := by
  have hterm : ∀ z : Fin 2 × Fin 2, ((PMF.pure p) z).toReal * dist z.1 z.2
      = if z = p then dist p.1 p.2 else 0 := by
    intro z
    by_cases h : z = p
    · subst h
      rw [PMF.pure_apply_self, ENNReal.toReal_one, one_mul, ite_eq_left rfl]
    · simp [h, PMF.pure_apply_of_ne _ _ h]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  simp

theorem contraction_swap (x y : Fin 2) (h : swapAdj x y) :
    ∑ z, ((swapCoupling x y h) z).toReal * dist z.1 z.2
      ≤ 1 * dist x y := by
  fin_cases x <;> fin_cases y
  · exact absurd rfl h
  · simp only [swapCoupling, pure_pair_expected_dist]
    simp [dist_one_zero, dist_zero_one]
  · simp only [swapCoupling, pure_pair_expected_dist]
    simp [dist_one_zero, dist_zero_one]
  · exact absurd rfl h

theorem path_swap (x y : Fin 2) :
    MathlibExt.Probability.PathCoupling.Path swapAdj dist x y := by
  fin_cases x <;> fin_cases y
  · exact MathlibExt.Probability.PathCoupling.Path.refl 0
  · exact MathlibExt.Probability.PathCoupling.Path.step (by simp [swapAdj])
      (by simp) (MathlibExt.Probability.PathCoupling.Path.refl 1)
  · exact MathlibExt.Probability.PathCoupling.Path.step (by simp [swapAdj])
      (by simp) (MathlibExt.Probability.PathCoupling.Path.refl 0)
  · exact MathlibExt.Probability.PathCoupling.Path.refl 1

/-- At time `1` the chain started at `0` is the point mass at `1`. -/
example : chainDist flipKernel 0 1 = PMF.pure 1 := by
  simp [chainDist, flipKernel]

/-- At time `1` the chain started at `1` is the point mass at `0`. -/
example : chainDist flipKernel 1 1 = PMF.pure 0 := by
  simp [chainDist, flipKernel]

/-- At time `1` the total variation between the chains started at
`0` and `1` is exactly `1`. -/
example : tvDist (chainDist flipKernel 0 1) (chainDist flipKernel 1 1) = 1 := by
  rw [show chainDist flipKernel 0 1 = PMF.pure 1 by simp [chainDist, flipKernel],
    show chainDist flipKernel 1 1 = PMF.pure 0 by simp [chainDist, flipKernel]]
  show (1 / 2) * (∑ a, |((PMF.pure (1 : Fin 2)) a).toReal
      - ((PMF.pure (0 : Fin 2)) a).toReal|) = 1
  have h0 : |((PMF.pure (1 : Fin 2)) 0).toReal
      - ((PMF.pure (0 : Fin 2)) 0).toReal| = 1 := by
    rw [PMF.pure_apply_of_ne (1 : Fin 2) (0 : Fin 2)
      (by decide : (0 : Fin 2) ≠ 1), PMF.pure_apply_self,
      ENNReal.toReal_zero, ENNReal.toReal_one]
    norm_num
  have h1 : |((PMF.pure (1 : Fin 2)) 1).toReal
      - ((PMF.pure (0 : Fin 2)) 1).toReal| = 1 := by
    rw [PMF.pure_apply_self, PMF.pure_apply_of_ne (0 : Fin 2) (1 : Fin 2)
      (by decide : (1 : Fin 2) ≠ 0),
      ENNReal.toReal_zero, ENNReal.toReal_one]
    norm_num
  rw [Fin.sum_univ_two, h0, h1]
  norm_num

/-- The path-coupling bound at time `1` for the two distinct starts:
`tvDist ≤ 1 ^ 1 * dist 0 1 / 1`. -/
example : tvDist (chainDist flipKernel 0 1) (chainDist flipKernel 1 1)
    ≤ (1 : ℝ) ^ 1 * dist (0 : Fin 2) (1 : Fin 2) / 1 :=
  path_coupling_tv flipKernel swapAdj swapCoupling swapCoupling_fst
    swapCoupling_snd (by norm_num) (by norm_num) one_le_dist_of_ne
    contraction_swap path_swap 0 1 1

/-- Equal starts: the bound is `0`, and so is the total variation. -/
example : tvDist (chainDist flipKernel 0 1) (chainDist flipKernel 0 1) = 0 := by
  show (1 / 2) * (∑ a, |((chainDist flipKernel 0 1) a).toReal
      - ((chainDist flipKernel 0 1) a).toReal|) = 0
  simp

end MathlibExtTest.Probability.PathCoupling
