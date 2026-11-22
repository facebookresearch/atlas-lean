/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.LinearProgrammingWeakDuality
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum.Ineq

/-!
# Clients of weak linear programming duality

Concrete dual points bound every feasible primal objective. The examples
include nonzero tight and loose bounds, empty dimensions, and countermodels
to dropping each of the four hypotheses independently.
-/

namespace LinearProgrammingWeakDualityTest

open MathlibExt.Analysis.Convex.LPWeakDuality
open scoped Matrix

/-- A nonoptimal primal-dual pair has objectives `4` and `15`. -/
private theorem oneDim_loose : (4 : ℝ) ≤ 15 := by
  have h := weak_linear_programming_duality
    (1 : Matrix (Fin 1) (Fin 1) ℝ) ![5] ![2]
    (x := ![2]) (by norm_num [Fin.forall_fin_one])
    (by norm_num [Fin.forall_fin_one, Matrix.mulVec, dotProduct])
    (y := ![3]) (by norm_num [Fin.forall_fin_one])
    (by norm_num [Fin.forall_fin_one, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply])
  convert h using 1 <;> norm_num [dotProduct]

/-- The concrete dual point `y = 2` bounds every feasible scalar primal. -/
private theorem oneDim_bound (x : Fin 1 → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hAx : ∀ j, (1 : Matrix (Fin 1) (Fin 1) ℝ).mulVec x j ≤ ![5] j) :
    ![2] ⬝ᵥ x ≤ 10 := by
  have h := weak_linear_programming_duality
    (1 : Matrix (Fin 1) (Fin 1) ℝ) ![5] ![2] hx hAx
    (y := ![2]) (by norm_num [Fin.forall_fin_one])
    (by norm_num [Fin.forall_fin_one, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply])
  convert h using 1
  norm_num [dotProduct]

/-- `x = 5`, `y = 2` attain the scalar bound with equal value `10`. -/
private theorem oneDim_tight :
    (∀ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) →
      (∀ j, (1 : Matrix (Fin 1) (Fin 1) ℝ).mulVec x j ≤ ![5] j) →
      ![2] ⬝ᵥ x ≤ ![2] ⬝ᵥ ![5]) ∧
    (∀ i : Fin 1, 0 ≤ (![5] : Fin 1 → ℝ) i) ∧
    (∀ j, (1 : Matrix (Fin 1) (Fin 1) ℝ).mulVec ![5] j ≤ ![5] j) ∧
    (![2] : Fin 1 → ℝ) ⬝ᵥ ![5] = ![5] ⬝ᵥ ![2] ∧
    (![2] : Fin 1 → ℝ) ⬝ᵥ ![5] = 10 := by
  refine ⟨fun x hx hAx => ?_, ?_⟩
  · convert oneDim_bound x hx hAx using 1
    norm_num [dotProduct]
  · norm_num [Fin.forall_fin_one, Matrix.mulVec, dotProduct]

/-- `y = 2` bounds `2*x₀ + x₁` under `x₀ + x₁ ≤ 3`. -/
private theorem twoVar_bound (x : Fin 2 → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hAx : ∀ j,
      (Matrix.of ![![1, 1]] : Matrix (Fin 1) (Fin 2) ℝ).mulVec x j ≤
        ![3] j) :
    ![2, 1] ⬝ᵥ x ≤ 6 := by
  have h := weak_linear_programming_duality
    (Matrix.of ![![1, 1]] : Matrix (Fin 1) (Fin 2) ℝ)
    ![3] ![2, 1] hx hAx (y := ![2])
    (by norm_num [Fin.forall_fin_one])
    (by norm_num [Fin.forall_fin_two, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply])
  convert h using 1
  norm_num [dotProduct]

/-- `(3, 0)` attains the two-variable bound, equal to the dual value. -/
private theorem twoVar_tight :
    (∀ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i) →
      (∀ j, (Matrix.of ![![1, 1]] : Matrix (Fin 1) (Fin 2) ℝ).mulVec
        x j ≤ ![3] j) → ![2, 1] ⬝ᵥ x ≤ ![2, 1] ⬝ᵥ ![3, 0]) ∧
    (∀ i : Fin 2, 0 ≤ (![3, 0] : Fin 2 → ℝ) i) ∧
    (∀ j, (Matrix.of ![![1, 1]] : Matrix (Fin 1) (Fin 2) ℝ).mulVec
      ![3, 0] j ≤ ![3] j) ∧
    (![2, 1] : Fin 2 → ℝ) ⬝ᵥ ![3, 0] = ![3] ⬝ᵥ ![2] ∧
    (![2, 1] : Fin 2 → ℝ) ⬝ᵥ ![3, 0] = 6 := by
  refine ⟨fun x hx hAx => ?_, ?_⟩
  · convert twoVar_bound x hx hAx using 1
    norm_num [dotProduct, Fin.sum_univ_two]
  · norm_num [Fin.forall_fin_one, Fin.forall_fin_two, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- With no variables, the nonzero dual point gives the bound `0 ≤ 21`. -/
private theorem noVariables : (0 : ℝ) ≤ 21 := by
  calc
    (0 : ℝ) = (![] : Fin 0 → ℝ) ⬝ᵥ ![] := by simp [dotProduct]
    _ ≤ (![7] : Fin 1 → ℝ) ⬝ᵥ ![3] :=
      weak_linear_programming_duality
        (0 : Matrix (Fin 1) (Fin 0) ℝ) ![7] ![]
        (fun i => i.elim0) (by norm_num [Fin.forall_fin_one])
        (by norm_num [Fin.forall_fin_one]) (fun i => i.elim0)
    _ = 21 := by norm_num [dotProduct]

/-- With no constraints, a negative objective is bounded above by zero. -/
private theorem noConstraints : (-6 : ℝ) ≤ 0 := by
  calc
    (-6 : ℝ) = (![-2] : Fin 1 → ℝ) ⬝ᵥ ![3] := by
      norm_num [dotProduct]
    _ ≤ (![] : Fin 0 → ℝ) ⬝ᵥ ![] :=
      weak_linear_programming_duality
        (0 : Matrix (Fin 0) (Fin 1) ℝ) ![] ![-2]
        (by norm_num [Fin.forall_fin_one]) (fun j => j.elim0)
        (fun j => j.elim0) (by norm_num [Fin.forall_fin_one])
    _ = 0 := by simp [dotProduct]

/-- The theorem also accepts both index types empty. -/
private theorem bothEmpty :
    (![] : Fin 0 → ℝ) ⬝ᵥ ![] ≤ (![] : Fin 0 → ℝ) ⬝ᵥ ![] := by
  exact weak_linear_programming_duality
    (0 : Matrix (Fin 0) (Fin 0) ℝ) ![] ![]
    (fun i => i.elim0) (fun j => j.elim0)
    (fun j => j.elim0) (fun i => i.elim0)

/-- Without `x ≥ 0`, the other hypotheses can give the false bound `0 ≤ -1`. -/
private theorem needs_primal_nonneg :
    ∃ (A : Matrix (Fin 1) (Fin 1) ℝ) (b c x y : Fin 1 → ℝ),
      ¬ (∀ i, 0 ≤ x i) ∧ (∀ j, A.mulVec x j ≤ b j) ∧
      (∀ j, 0 ≤ y j) ∧ (∀ i, c i ≤ Aᵀ.mulVec y i) ∧
      ¬ (c ⬝ᵥ x ≤ b ⬝ᵥ y) := by
  refine ⟨1, ![-1], ![0], ![-1], ![1], ?_⟩
  norm_num [Fin.forall_fin_one, Matrix.mulVec, dotProduct]

/-- Without `y ≥ 0`, the other hypotheses can give the false bound `0 ≤ -1`. -/
private theorem needs_dual_nonneg :
    ∃ (A : Matrix (Fin 1) (Fin 1) ℝ) (b c x y : Fin 1 → ℝ),
      (∀ i, 0 ≤ x i) ∧ (∀ j, A.mulVec x j ≤ b j) ∧
      ¬ (∀ j, 0 ≤ y j) ∧ (∀ i, c i ≤ Aᵀ.mulVec y i) ∧
      ¬ (c ⬝ᵥ x ≤ b ⬝ᵥ y) := by
  refine ⟨1, ![1], ![-1], ![0], ![-1], ?_⟩
  norm_num [Fin.forall_fin_one, Matrix.mulVec, dotProduct]

/-- Without `Ax ≤ b`, the other hypotheses can give the false bound `1 ≤ 0`. -/
private theorem needs_primal_feasibility :
    ∃ (A : Matrix (Fin 1) (Fin 1) ℝ) (b c x y : Fin 1 → ℝ),
      (∀ i, 0 ≤ x i) ∧ ¬ (∀ j, A.mulVec x j ≤ b j) ∧
      (∀ j, 0 ≤ y j) ∧ (∀ i, c i ≤ Aᵀ.mulVec y i) ∧
      ¬ (c ⬝ᵥ x ≤ b ⬝ᵥ y) := by
  refine ⟨1, ![0], ![1], ![1], ![1], ?_⟩
  norm_num [Fin.forall_fin_one, Matrix.mulVec, dotProduct]

/-- Without `c ≤ Aᵀy`, the other hypotheses can give the false bound `2 ≤ 1`. -/
private theorem needs_dual_feasibility :
    ∃ (A : Matrix (Fin 1) (Fin 1) ℝ) (b c x y : Fin 1 → ℝ),
      (∀ i, 0 ≤ x i) ∧ (∀ j, A.mulVec x j ≤ b j) ∧
      (∀ j, 0 ≤ y j) ∧ ¬ (∀ i, c i ≤ Aᵀ.mulVec y i) ∧
      ¬ (c ⬝ᵥ x ≤ b ⬝ᵥ y) := by
  refine ⟨1, ![1], ![2], ![1], ![1], ?_⟩
  norm_num [Fin.forall_fin_one, Matrix.mulVec, dotProduct]

end LinearProgrammingWeakDualityTest
