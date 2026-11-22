/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Total dual integrality

A system `A x ≤ b` is *totally dual integral* (TDI) if for every integral objective `c` for which
`max {cᵀ x : A x ≤ b}` is finite, the dual `min {bᵀ y : y ≥ 0, Aᵀ y = c}` has an integral optimal
solution. TDI is a property of the system, not of the polyhedron. Edmonds and Giles proved that a
TDI system with integral right-hand side defines an integral polyhedron; that theorem is recorded
in `WantedExt`. Here we give the definition and the simplest example: upper-bound systems `x ≤ b`
(the identity matrix; the feasible region is a translated orthant, not a two-sided box).

Source: M. X. Goemans, MIT 18.438 Advanced Combinatorial Optimization, Lecture 6 (2009),
Definition 1 (TDI) and Theorem 2 (Edmonds-Giles); J. Edmonds and R. Giles, "A min-max relation
for submodular functions on graphs", Ann. Discrete Math. 1 (1977), 185-204.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.TotalDualIntegrality

open Matrix

/-- **Totally dual integral system.** The system `A x ≤ b` is TDI if for every integral `c` such
that `max {cᵀ x : A x ≤ b}` is finite (the system is feasible and `cᵀ x` is bounded above on it),
some integral `y ≥ 0` with `Aᵀ y = c` has `bᵀ y = cᵀ x` for a feasible `x`; by weak duality such a
`y` is an optimal dual solution and `x` an optimal primal one (Goemans, MIT 18.438, Lecture 6,
2009, Definition 1). -/
def IsTDI {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∀ c : Fin n → ℤ,
    (∃ x : Fin n → ℝ, A *ᵥ x ≤ b) →
    BddAbove ((fun x : Fin n → ℝ => (fun j => (c j : ℝ)) ⬝ᵥ x) '' {x | A *ᵥ x ≤ b}) →
    ∃ y : Fin m → ℤ, 0 ≤ y ∧ Aᵀ *ᵥ (fun i => (y i : ℝ)) = (fun j => (c j : ℝ)) ∧
      ∃ x : Fin n → ℝ, A *ᵥ x ≤ b ∧ b ⬝ᵥ (fun i => (y i : ℝ)) = (fun j => (c j : ℝ)) ⬝ᵥ x

/-- **Upper-bound systems are totally dual integral.** For every `b`, the system `x ≤ b` (with `A`
the identity matrix) is TDI: a bounded integral objective `c` must be nonnegative, and `y = c` is an
integral optimal dual solution, attained at `x = b`. The feasible region is the translated orthant
`b - ℝⁿ₊`, not a two-sided box `l ≤ x ≤ u`. -/
theorem isTDI_upperBound {n : ℕ} (b : Fin n → ℝ) : IsTDI (1 : Matrix (Fin n) (Fin n) ℝ) b := by
  intro c _ hbdd
  obtain ⟨M, hM⟩ := hbdd
  set cr : Fin n → ℝ := fun j => (c j : ℝ) with hcr
  have hc : 0 ≤ c := by
    intro j
    change (0 : ℤ) ≤ c j
    by_contra hneg'
    have hneg : c j < 0 := lt_of_not_ge hneg'
    have hcj : cr j < 0 := by
      have : ((c j : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
      exact this
    set t : ℝ := (|M| + |cr ⬝ᵥ b| + 1) / (-cr j) with ht
    have htpos : 0 ≤ t := by
      apply div_nonneg (by positivity) (by linarith)
    let x : Fin n → ℝ := b - t • Pi.single j 1
    have hx : (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x ≤ b := by
      rw [one_mulVec]
      intro i
      simp only [x, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have : 0 ≤ t * (Pi.single j (1 : ℝ) : Fin n → ℝ) i := by
        apply mul_nonneg htpos
        by_cases h : i = j
        · subst h; simp
        · simp [h]
      linarith
    have hval : cr ⬝ᵥ x = cr ⬝ᵥ b - t * cr j := by
      simp only [x, dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
    have hle : cr ⬝ᵥ x ≤ M := hM ⟨x, hx, rfl⟩
    have htc : t * (-cr j) = |M| + |cr ⬝ᵥ b| + 1 := by
      rw [ht]; field_simp [hcj.ne]
    have h1 : -|cr ⬝ᵥ b| ≤ cr ⬝ᵥ b := neg_abs_le _
    have h2 : M ≤ |M| := le_abs_self M
    nlinarith
  refine ⟨c, hc, ?_, b, by rw [one_mulVec], dotProduct_comm _ _⟩
  rw [transpose_one, one_mulVec]

end MathlibExt.Analysis.Convex.TotalDualIntegrality
