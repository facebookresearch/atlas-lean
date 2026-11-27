/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Mazur's Problem 91

The real plane with the sup norm is linearly isometric to its continuous dual and violates
the parallelogram law. It gives a negative answer to the Banach-space form of Mazur's problem.
-/

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook91Wanted

@[expose] public section

/-- **Mazur's Problem 91 (Scottish Book), Banach-space form.** This is the proposition that
every finite-dimensional real normed space $E$ that is linearly isometric to its dual
space $E^*$ (the continuous linear functionals on $E$ with the operator norm) is an inner
product space, that is, its norm is induced by some inner product on $E$.

Mazur's original formulation asks whether, for every $n$, a convex body in $\mathbb{R}^n$
that is affinely equivalent to its conjugate (polar) body is necessarily an ellipsoid. -/
def ScottishBookProblem91Claim : Prop :=
  ∀ (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E],
    Module.finrank ℝ E = n →
    (∃ _ : E ≃ₗᵢ[ℝ] StrongDual ℝ E, True) →
    ∃ _ : InnerProductSpace ℝ E, True

end

universe u

-- The universe lift lets the same counterexample work in every universe.
private abbrev Plane := ULift.{u} (ℝ × ℝ)

private abbrev cornerPlus : Plane.{u} := ULift.up (1, 1)
private abbrev cornerMinus : Plane.{u} := ULift.up (1, -1)

-- These two corners of the unit square form a basis.
private theorem corner_expansion (y : Plane.{u}) :
    ((y.down.1 + y.down.2) / 2) • (cornerPlus : Plane.{u}) +
      ((y.down.1 - y.down.2) / 2) • cornerMinus = y := by
  apply ULift.ext
  apply Prod.ext
  · change (y.down.1 + y.down.2) / 2 * 1 + (y.down.1 - y.down.2) / 2 * 1 = _
    ring
  · change (y.down.1 + y.down.2) / 2 * 1 + (y.down.1 - y.down.2) / 2 * (-1) = _
    ring

-- The sum of the absolute values of the two coefficients is bounded by the sup norm.
private theorem abs_halves_le (y : Plane.{u}) :
    |(y.down.1 + y.down.2) / 2| + |(y.down.1 - y.down.2) / 2| ≤ ‖y‖ := by
  have h₁ : |y.down.1| ≤ ‖y‖ := norm_fst_le y.down
  have h₂ : |y.down.2| ≤ ‖y‖ := norm_snd_le y.down
  obtain ⟨hy₁, hy₁'⟩ := abs_le.mp h₁
  obtain ⟨hy₂, hy₂'⟩ := abs_le.mp h₂
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

private theorem norm_eval_corners (f : StrongDual ℝ (Plane.{u})) :
    ‖(ULift.up (f cornerPlus, f cornerMinus) : Plane.{u})‖ = ‖f‖ := by
  apply le_antisymm
  · change max ‖f cornerPlus‖ ‖f cornerMinus‖ ≤ _
    exact max_le
      (by simpa [cornerPlus, Prod.norm_def] using f.le_opNorm cornerPlus)
      (by simpa [cornerMinus, Prod.norm_def] using f.le_opNorm cornerMinus)
  · let x := (f cornerPlus, f cornerMinus)
    apply f.opNorm_le_bound (norm_nonneg x)
    intro y
    let a := (y.down.1 + y.down.2) / 2
    let b := (y.down.1 - y.down.2) / 2
    have h : f y = a • x.1 + b • x.2 := by
      conv_lhs => rw [← corner_expansion y]
      rw [map_add, map_smul, map_smul]
    rw [h]
    calc
      ‖a • x.1 + b • x.2‖ ≤ ‖a • x.1‖ + ‖b • x.2‖ := norm_add_le _ _
      _ ≤ (|a| + |b|) * ‖x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs a, Real.norm_eq_abs b, add_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (norm_fst_le x) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (norm_snd_le x) (abs_nonneg _))
      _ ≤ ‖y‖ * ‖x‖ := mul_le_mul_of_nonneg_right (abs_halves_le y) (norm_nonneg x)
      _ = _ := mul_comm _ _

private noncomputable def dualToPlane : StrongDual ℝ (Plane.{u}) ≃ₗᵢ[ℝ] Plane.{u} := by
  let eval : StrongDual ℝ (Plane.{u}) →ₗᵢ[ℝ] Plane.{u} :=
    { toFun := fun f => ULift.up (f cornerPlus, f cornerMinus)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      norm_map' := norm_eval_corners }
  refine LinearIsometryEquiv.ofSurjective (F := StrongDual ℝ (Plane.{u})) eval ?_
  intro x
  let e : Plane.{u} ≃ₗᵢ[ℝ] ℝ × ℝ := LinearIsometryEquiv.ulift ℝ (ℝ × ℝ)
  let f : StrongDual ℝ (Plane.{u}) :=
    (((x.down.1 + x.down.2) / 2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ((x.down.1 - x.down.2) / 2) • ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (e : Plane.{u} →L[ℝ] ℝ × ℝ)
  refine ⟨f, ?_⟩
  exact corner_expansion x

/--
**Mazur's Problem 91 has a negative answer.** There is a finite-dimensional real normed
space $E$ that is linearly isometric to its dual space $E^*$ (the continuous linear
functionals on $E$ with the operator norm) but whose norm is not induced by any inner
product on $E$. Thus the Banach-space form of Mazur's Problem 91 is false.

Source: S. Mazur, Problem 91 of the Scottish Book. The typescript itself
records the negative answer when `n` is even (for example, `ℓ¹ 2`, whose unit
ball is a diamond, is linearly isometric to its dual `ℓ^∞ 2` but is not a
Hilbert space, since its norm does not satisfy the parallelogram law); the
odd-dimensional case is not needed to refute the universal claim.
-/
public theorem mazur91_refuted : ¬ ScottishBookProblem91Claim := by
  intro h
  let E := Plane
  have hdim : Module.finrank ℝ E = 2 := by
    simp [E, Plane, Module.finrank_prod]
  obtain ⟨inner, -⟩ := h 2 E hdim ⟨dualToPlane.symm, trivial⟩
  let : InnerProductSpace ℝ E := inner
  have hpar := parallelogram_law_with_norm ℝ (ULift.up (1, 0) : E) (ULift.up (0, 1))
  change (max ‖(1 : ℝ) + 0‖ ‖(0 : ℝ) + 1‖) ^ 2 +
    (max ‖(1 : ℝ) - 0‖ ‖(0 : ℝ) - 1‖) ^ 2 =
    2 * ((max ‖(1 : ℝ)‖ ‖(0 : ℝ)‖) ^ 2 + (max ‖(0 : ℝ)‖ ‖(1 : ℝ)‖) ^ 2) at hpar
  norm_num at hpar

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook91Wanted
