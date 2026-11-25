/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.EllipsoidConvergence

@[expose] public section

open MathlibExt.Analysis.Convex.EllipsoidMethod MeasureTheory Matrix

/-! The hypotheses of `ellipsoidRun_finds_point` are jointly satisfiable: the constant run on the
unit disc with `P` the disc itself, where the first centre already lies in `P`. -/

example : ∃ k ≤ 0, (fun _ : ℕ => (0 : Fin 2 → ℝ)) k ∈ ellipsoid (0 : Fin 2 → ℝ) 1 :=
  ellipsoidRun_finds_point (n := 2) (P := ellipsoid 0 1) (c := fun _ => 0)
    (A := fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) le_rfl Matrix.PosDef.one subset_rfl
    (fun k hk => absurd (by simp [ellipsoid]) hk) (N := 0) (by simp)

example : volume (ellipsoid (0 : Fin 3 → ℝ) (1 : Matrix (Fin 3) (Fin 3) ℝ)) ≠ ⊤ :=
  volume_ellipsoid_ne_top Matrix.PosDef.one 0

/-! A run that starts outside `P` and makes one central cut. `E₀` is the unit disc, `P` is the
single point `a₁ = (-1/3, 0)`, the first centre `a₀ = 0` misses `P`, and the cut `x₀ ≤ 0` through
`a₀` is valid on `P`. The invariant at `k = 1` then gives a positive definite `A₁`, `P ⊆ E₁` and the
volume bound `vol E₁ ≤ e^{-1/6} vol E₀`. -/

/- The centre after one cut of the unit disc by `x₀ ≤ 0`. -/
noncomputable def cutRunA1 : Fin 2 → ℝ := nextCenter 0 1 (Pi.single 0 1)

/- The one-cut run: centres `0, a₁, a₁, …`, matrices `I, A₁, A₁, …`, cut vector `e₀`. -/
noncomputable def cutRunCentre (k : ℕ) : Fin 2 → ℝ := if k = 0 then 0 else cutRunA1

/- Matrices of the one-cut run. -/
noncomputable def cutRunMatrix (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if k = 0 then 1 else nextMatrix 1 (Pi.single 0 1)

theorem cutRunA1_eq : cutRunA1 = ![-(1 / 3), 0] := by
  ext i
  fin_cases i <;> norm_num [cutRunA1, nextCenter, cutDirection]

example : (nextMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) (Pi.single 0 1)).PosDef ∧
    ({cutRunA1} : Set (Fin 2 → ℝ)) ⊆ ellipsoid cutRunA1 (nextMatrix 1 (Pi.single 0 1)) ∧
    volume (ellipsoid cutRunA1 (nextMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) (Pi.single 0 1))) ≤
      ENNReal.ofReal (Real.exp (-((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) + 1 : ℝ)))) *
        volume (ellipsoid (0 : Fin 2 → ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have h := ellipsoidRun_invariant (n := 2) (P := {cutRunA1}) (a := cutRunCentre)
    (c := fun _ => Pi.single 0 1) (A := cutRunMatrix) le_rfl
    (by simpa [cutRunMatrix] using Matrix.PosDef.one)
    (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simp only [cutRunCentre, cutRunMatrix, ite_true, ellipsoid, Set.mem_ofPred_eq, sub_zero,
        inv_one, Matrix.one_mulVec, cutRunA1_eq]
      simp [dotProduct, Fin.sum_univ_two]
      norm_num)
    (by
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · refine ⟨by simp, ?_, by simp [cutRunCentre, cutRunMatrix, cutRunA1], by simp [cutRunMatrix]⟩
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp [cutRunCentre, cutRunA1_eq, dotProduct, Fin.sum_univ_two]
      · exact absurd (by simp [cutRunCentre, hpos.ne']) hk)
    1 (by
      intro j hj
      have : j = 0 := by omega
      subst this
      simp only [cutRunCentre, ite_true, Set.mem_singleton_iff, cutRunA1_eq]
      intro h0
      have := congrFun h0 0
      simp at this)
  simpa [cutRunCentre, cutRunMatrix] using h
