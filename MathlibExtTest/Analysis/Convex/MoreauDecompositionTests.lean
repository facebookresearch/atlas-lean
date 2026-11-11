/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.MoreauDecomposition

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for Moreau decomposition for closed convex cones

The tests use the canonical `convexProjection` map together with the
cone-specific Moreau API. The cone fixtures are Mathlib `ProperCone` values.

* The nonnegative orthant in `ℝ²` is a closed convex cone, and its
  projection is coordinatewise `max (·) 0`.
* The polar cone of the orthant is the nonpositive orthant.
* Moreau decomposition at the concrete point `(-1, 2)`: the projections
  are `(0, 2)` and `(-1, 0)`.
* The whole space and the singleton `{0}` are closed convex cones, with
  projections the identity and `0` respectively.
* `#print axioms` for the orthant projection formula: standard triple only.
-/

noncomputable section

@[expose]
public section

namespace MathlibExtTest.Analysis.Convex.MoreauDecompositionTests

open Set Filter Topology
open scoped InnerProductSpace
open MathlibExt.Analysis.Convex.MoreauDecomposition
open MathlibExt.Analysis.InnerProductSpace.ConvexProjection

/-- The nonnegative orthant in `ℝ²`. -/
def orthant : Set (EuclideanSpace ℝ (Fin 2)) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1}

/-- The nonnegative orthant is closed. -/
theorem isClosed_orthant : IsClosed orthant := by
  have hset : orthant =
      (fun x : EuclideanSpace ℝ (Fin 2) => x 0) ⁻¹' Set.Ici 0 ∩
        (fun x : EuclideanSpace ℝ (Fin 2) => x 1) ⁻¹' Set.Ici 0 := by
    ext x
    simp [orthant]
  rw [hset]
  exact (isClosed_Ici.preimage (PiLp.continuous_apply (p := 2)
    (β := fun _ : Fin 2 => ℝ) 0)).inter
    (isClosed_Ici.preimage (PiLp.continuous_apply (p := 2)
      (β := fun _ : Fin 2 => ℝ) 1))

/-- The nonnegative orthant as a Mathlib proper cone. -/
def isClosedConvexCone_orthant : ProperCone ℝ (EuclideanSpace ℝ (Fin 2)) where
  toSubmodule :=
    { carrier := orthant
      zero_mem' := by simp [orthant]
      add_mem' := by
        intro x y hx hy
        exact ⟨add_nonneg hx.1 hy.1, add_nonneg hx.2 hy.2⟩
      smul_mem' := by
        intro c x hx
        change 0 ≤ (c : ℝ) * x 0 ∧ 0 ≤ (c : ℝ) * x 1
        exact ⟨mul_nonneg c.2 hx.1, mul_nonneg c.2 hx.2⟩ }
  isClosed' := isClosed_orthant
/-- Projection onto the nonnegative orthant is coordinatewise `max (·) 0`. -/
theorem convexProjection_orthant (x : EuclideanSpace ℝ (Fin 2)) :
    convexProjection orthant x =
      WithLp.toLp 2 fun i => max (x i) 0 := by
  apply convexProjection_eq_of_forall_inner_le_zero isClosedConvexCone_orthant.toPointedCone
    isClosed_orthant.isComplete
  · refine ⟨?_, ?_⟩ <;> exact le_max_right _ _
  · intro y hy
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp only [PiLp.sub_apply, Real.inner_apply]
    exact add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_max_left _ _)) hy.1)
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_max_left _ _)) hy.2)
  · rw [PiLp.inner_apply, Fin.sum_univ_two]
    have hterm : ∀ i : Fin 2, (x i - max (x i) 0) * max (x i) 0 = 0 := by
      intro i
      rcases le_total (x i) 0 with h | h
      · rw [max_eq_right h]; simp
      · rw [max_eq_left h]; simp
    simp only [PiLp.sub_apply, Real.inner_apply, hterm 0, hterm 1, add_zero]

/-- The polar cone of the nonnegative orthant is the nonpositive orthant. -/
theorem polarCone_orthant :
    (polarCone orthant : Set _) = {x : EuclideanSpace ℝ (Fin 2) | x 0 ≤ 0 ∧ x 1 ≤ 0} := by
  ext y
  constructor
  · intro hy
    have h0 : (WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2)) ∈ orthant := by
      refine ⟨?_, ?_⟩ <;> simp
    have h1 : (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2)) ∈ orthant := by
      refine ⟨?_, ?_⟩ <;> simp
    have e0 := (mem_polarCone.1 hy) _ h0
    have e1 := (mem_polarCone.1 hy) _ h1
    rw [PiLp.inner_apply, Fin.sum_univ_two] at e0 e1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.inner_apply] at e0 e1
    refine ⟨by linarith, by linarith⟩
  · intro hy
    refine mem_polarCone.2 fun x hx => ?_
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp only [Real.inner_apply]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hx.1 hy.1)
      (mul_nonpos_of_nonneg_of_nonpos hx.2 hy.2)

/-- Moreau decomposition at `(-1, 2)`: the orthant projection is `(0, 2)`. -/
example : convexProjection orthant
    (WithLp.toLp 2 ![-1, 2] : EuclideanSpace ℝ (Fin 2)) =
      WithLp.toLp 2 ![0, 2] := by
  rw [convexProjection_orthant]
  apply PiLp.ext
  intro i
  fin_cases i <;> norm_num

/-- Moreau decomposition at `(-1, 2)`: the polar projection is `(-1, 0)`. -/
example : convexProjection (polarCone orthant)
    (WithLp.toLp 2 ![-1, 2] : EuclideanSpace ℝ (Fin 2)) =
      WithLp.toLp 2 ![-1, 0] := by
  have h : ∀ x : EuclideanSpace ℝ (Fin 2),
      convexProjection (polarCone orthant) x = x - convexProjection orthant x :=
    convexProjection_polarCone isClosedConvexCone_orthant
  rw [h, convexProjection_orthant]
  apply PiLp.ext
  intro i
  fin_cases i <;> norm_num [PiLp.sub_apply]

/-- The whole space as a Mathlib proper cone. -/
def isClosedConvexCone_univ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ProperCone ℝ E := ⊤

/-- Projection onto the whole space is the identity. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (x : E) :
    convexProjection Set.univ x = x :=
  convexProjection_eq_self_of_mem isClosedConvexCone_univ.nonempty
    isClosedConvexCone_univ.isClosed.isComplete isClosedConvexCone_univ.convex (Set.mem_univ x)
/-- The singleton `{0}` as a Mathlib proper cone. -/
def isClosedConvexCone_singleton_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : ProperCone ℝ E := ⊥

/-- Projection onto `{0}` is `0`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (x : E) :
    convexProjection ({0} : Set E) x = 0 := by
  apply convexProjection_eq_of_forall_inner_le_zero isClosedConvexCone_singleton_zero.toPointedCone
    isClosedConvexCone_singleton_zero.isClosed.isComplete (Set.mem_singleton 0)
  · intro y hy
    change y = 0 at hy
    rw [hy]
    simp
  · simp

#print axioms convexProjection_orthant
#print axioms polarCone_orthant
#print axioms moreau_decomposition
#print axioms polarCone_polarCone
#print axioms lipschitzWith_convexProjection

end MathlibExtTest.Analysis.Convex.MoreauDecompositionTests
