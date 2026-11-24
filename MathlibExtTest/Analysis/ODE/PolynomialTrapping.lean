/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.Analysis.ODE.PolynomialTrapping
import MathlibExt.AlgebraicGeometry.BernsteinBoxes
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set MvPolynomial

-- The radial field has weak boundary tangency and positive radial growth
-- when 0 < x²+y² < 1; the damped field below has a nonzero SOS remainder.
private noncomputable def energy : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2
private noncomputable def diskLevel : MvPolynomial (Fin 2) ℝ := energy - 1
private noncomputable def radialField : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![(1 - energy) * X 0 - X 1, X 0 + (1 - energy) * X 1]

private theorem identity_radial :
    -mkDerivation ℝ radialField diskLevel = 0 + (2 * energy) * diskLevel := by
  rw [mkDerivation_eq_sum_pderiv]
  simp [radialField, diskLevel, energy, Fin.sum_univ_two]
  ring

private theorem regular (x : Fin 2 → ℝ) (hx : eval x diskLevel = 0) :
    ∃ i, eval x (pderiv i diskLevel) ≠ 0 := by
  simp only [diskLevel, energy, map_sub, map_add, eval_pow, eval_X, map_one] at hx
  by_cases h : x 0 = 0
  · refine ⟨1, ?_⟩
    simp [diskLevel, energy]
    intro hz
    simp [h, hz] at hx
  · exact ⟨0, by simpa [diskLevel, energy] using h⟩

private theorem compact : IsCompact {x | eval x diskLevel ≤ 0} := by
  apply (isCompact_Icc :
    IsCompact (Icc (fun _ : Fin 2 => (-1 : ℝ)) (fun _ => 1))).of_isClosed_subset
  · apply isClosed_le
    · exact continuous_iff_continuousAt.mpr (fun x => (hasFDerivAt_eval diskLevel x).continuousAt)
    · exact continuous_const
  · intro x hx
    simp [diskLevel, energy] at hx
    constructor <;> intro i <;> fin_cases i <;> dsimp <;>
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 0 + 1),
        sq_nonneg (x 0 - 1), sq_nonneg (x 1 + 1), sq_nonneg (x 1 - 1)]

example (a : ℝ) (z : Fin 2 → ℝ) (hz : eval z diskLevel ≤ 0) :
    ∃ x : ℝ → Fin 2 → ℝ, x a = z ∧ (∀ t ∈ Ici a, eval (x t) diskLevel ≤ 0) ∧
      ∀ t ∈ Ici a, HasDerivAt x (fun i => eval (x t) (radialField i)) t :=
  exists_forward_solution_of_sos_boundary_identity radialField diskLevel 0 (2 * energy)
    (by simp) identity_radial compact regular a hz

private noncomputable def diskSlack : MvPolynomial (Fin 2) ℝ := 1 - X 0 ^ 2 - X 1 ^ 2

private theorem disk_degree (v : Fin 2) : diskSlack.degreeOf v ≤ 2 := by
  apply (degreeOf_sub_le _ _ _).trans
  apply max_le
  · apply (degreeOf_sub_le _ _ _).trans
    exact max_le (by simp) ((degreeOf_pow_le _ _ _).trans (by fin_cases v <;> simp [degreeOf_X]))
  · exact (degreeOf_pow_le _ _ _).trans (by fin_cases v <;> simp [degreeOf_X])

-- All nine degree-(2,2) coefficients on the initial box have margin at least 1/2.
private theorem disk_small_coeff (k : Fin 2 → Fin 3) :
    1 / 2 ≤ bernsteinCoeff (fun _ => 2) (boxPullback ![-1/2, -1/2] ![1/2, 1/2] diskSlack)
      (fun v => k v) := by
  have hp : boxPullback ![-1/2, -1/2] ![1/2, 1/2] diskSlack =
      C (1/2) + X 0 + X 1 - X 0 ^ 2 - X 1 ^ 2 := by
    apply MvPolynomial.funext
    intro x
    norm_num [eval_boxPullback, diskSlack]
    ring
  rw [hp]
  generalize h0 : k 0 = i
  generalize h1 : k 1 = j
  fin_cases i <;> fin_cases j <;>
    norm_num [sub_eq_add_neg, bernsteinCoeff_add, bernsteinCoeff_neg, bernsteinCoeff_C, X, pow_two,
      monomial_mul_monomial, bernsteinCoeff_monomial, Fin.prod_univ_two,
      Finsupp.single_apply, h0, h1, Nat.choose]

private theorem box_in_disk : Icc (![-1/2, -1/2] : Fin 2 → ℝ) ![1/2, 1/2] ⊆
    basicClosedSet ({()} : Finset Unit) (∅ : Finset Unit) (fun _ => diskSlack) (fun _ => 0) := by
  apply Icc_subset_basicClosedSet_of_bernsteinCoeff
    (ng := fun _ _ => 2) (nh := fun _ _ => 0)
  · intro v; fin_cases v <;> norm_num
  · exact fun _ _ => disk_degree
  · simp
  · intro i hi k
    exact le_trans (by norm_num) (disk_small_coeff k)
  · simp

-- This theorem discharges every geometric, coefficient and identity premise
-- for every initial point in the certified box.
private theorem radial_from_box (a : ℝ) (z : Fin 2 → ℝ) (hz : z ∈ Icc ![-1/2, -1/2] ![1/2, 1/2]) :
    ∃ x : ℝ → Fin 2 → ℝ, x a = z ∧ (∀ t ∈ Ici a, eval (x t) diskLevel ≤ 0) ∧
      ∀ t ∈ Ici a, HasDerivAt x (fun i => eval (x t) (radialField i)) t := by
  apply exists_forward_solution_of_sos_boundary_identity radialField diskLevel 0 (2 * energy)
    (by simp) identity_radial compact regular a
  have h := (box_in_disk hz).1 () (by simp)
  simp [diskSlack, diskLevel, energy] at h ⊢
  linarith

private noncomputable def dampedField : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![-energy * X 0 - X 1, X 0 - energy * X 1]

private theorem identity_damped :
    -mkDerivation ℝ dampedField diskLevel = (energy * energy + energy * energy) + 0 * diskLevel := by
  rw [mkDerivation_eq_sum_pderiv]
  simp [dampedField, diskLevel, energy, Fin.sum_univ_two]
  ring

example : IsSumSq (energy * energy + energy * energy) :=
  (IsSumSq.mul_self energy).add (IsSumSq.mul_self energy)

example (a : ℝ) (z : Fin 2 → ℝ) (hz : z ∈ Icc ![-1/2, -1/2] ![1/2, 1/2]) :
    ∃ x : ℝ → Fin 2 → ℝ, x a = z ∧ (∀ t ∈ Ici a, eval (x t) diskLevel ≤ 0) ∧
      ∀ t ∈ Ici a, HasDerivAt x (fun i => eval (x t) (dampedField i)) t := by
  apply exists_forward_solution_of_sos_boundary_identity dampedField diskLevel
    (energy * energy + energy * energy) 0
    ((IsSumSq.mul_self energy).add (IsSumSq.mul_self energy)) identity_damped compact regular a
  have h := (box_in_disk hz).1 () (by simp)
  simp [diskSlack, diskLevel, energy] at h ⊢
  linarith

example : ∃ x : ℝ → Fin 2 → ℝ, x 7 = ![1/2, 0] ∧
    (∀ t ∈ Ici 7, eval (x t) diskLevel ≤ 0) ∧
    HasDerivAt x ![3/8, 1/2] 7 ∧ (![3/8, 1/2] : Fin 2 → ℝ) ≠ 0 := by
  have hz : (![1/2, 0] : Fin 2 → ℝ) ∈ Icc ![-1/2, -1/2] ![1/2, 1/2] := by
    constructor <;> intro i <;> fin_cases i <;> norm_num
  obtain ⟨x, hx, hb, hd⟩ := radial_from_box 7 ![1/2, 0] hz
  refine ⟨x, hx, hb, ?_, ?_⟩
  · convert! hd 7 (by simp) using 1
    ext i
    fin_cases i <;> norm_num [hx, radialField, energy]
  · intro h
    have := congrFun h 0
    norm_num at this

example : eval (![1/2, 0] : Fin 2 → ℝ) (mkDerivation ℝ radialField diskLevel) = 3 / 8 := by
  norm_num [mkDerivation_eq_sum_pderiv, Fin.sum_univ_two, radialField, diskLevel, energy]

example (x : Fin 2 → ℝ) (hx : eval x diskLevel = 0) :
    eval x (mkDerivation ℝ radialField diskLevel) = 0 := by
  have h := congrArg (eval x) identity_radial
  simpa [hx] using h

example : energy * energy + energy * energy ≠ 0 := by
  intro h
  have := congrArg (eval (![1, 0] : Fin 2 → ℝ)) h
  norm_num [energy] at this

-- The first witness also supplies global trajectories for every certified-box
-- initial state, with no assumed solution or confinement hypothesis.
example (a : ℝ) (z : Fin 2 → ℝ) (hz : z ∈ Icc ![-1/2, -1/2] ![1/2, 1/2]) :
    ∃ x : ℝ → Fin 2 → ℝ, x a = z ∧ (∀ t ∈ Ici a, eval (x t) diskLevel ≤ 0) ∧
      ∀ t ∈ Ici a, HasDerivAt x (fun i => eval (x t) (radialField i)) t :=
  radial_from_box a z hz

-- The initial box is inhabited by a nonzero point.
example : (![1/2, 0] : Fin 2 → ℝ) ∈ Icc ![-1/2, -1/2] ![1/2, 1/2] ∧
    (![1/2, 0] : Fin 2 → ℝ) ≠ 0 := by
  constructor
  · constructor <;> intro i <;> fin_cases i <;> norm_num
  · intro h
    have := congrFun h 0
    norm_num at this
