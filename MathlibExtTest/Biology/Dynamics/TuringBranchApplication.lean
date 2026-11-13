/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.TuringBranchApplication
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Tests for `turing_patternBranch_of_reduction` on a two-dimensional instance: the Jacobian
`J₀ = [[4/5, 1], [-9/5, -1]]` with `d_u = 1`, critical wavenumber `k = 1/2` and neutral diffusion
`d₀ = 100/11`; the state space `E = ℝ × ℝ` with critical mode `φ = (1, 0)`, kernel coordinate
`κ = fst` and a nonzero correction `W(a, d) = (0, a²)`; and the map
`F((x, y), d) = (x G(x, d), y - x²)` with `G(a, d) = leadingEigenvalue (J₀ - (1/2)² D(d)) - a²`.
The reduction hypotheses are proved from the definitions; the theorem then yields nonzero steady
states `(a, a²)` of `F`. Boundary values of the critical eigenvalue (zero at `d₀`, positive at
`d = 10`) are computed directly from `leadingEigenvalue`. The `J₀` fixtures (`J₀_trace`,
`J₀_det`, `J₀_00`, `J₀_11`, `J₀_neutral`, `J₀_admissible`) and `G₀_contDiffAt`
(= `J₀_G_contDiffAt`) are copied from the private fixtures of
`MathlibExtTest/Biology/Dynamics/TuringBranches.lean`, which cannot be imported. -/

open Matrix Filter Topology

namespace MathlibExtTest.Biology.Dynamics.TuringBranchApplication

open MathlibExt.Biology.Dynamics.TuringPatterns MathlibExt.Biology.Dynamics.TuringBranches
  MathlibExt.Biology.Dynamics.TuringBranchApplication

/-- The Jacobian `[[4/5, 1], [-9/5, -1]]` (Schnakenberg at `a = 1/10`, `b = 9/10`). -/
local notation "J₀" => !![(4 / 5 : ℝ), 1; -9 / 5, -1]

lemma J₀_trace : (J₀).trace = -1 / 5 := by norm_num [Matrix.trace_fin_two]

lemma J₀_det : (J₀).det = 1 := by norm_num [Matrix.det_fin_two]

lemma J₀_00 : (J₀) 0 0 = 4 / 5 := by simp

lemma J₀_11 : (J₀) 1 1 = -1 := by simp

lemma J₀_neutral : neutralDiffusion J₀ 1 ((1 / 2) ^ 2) = 100 / 11 := by
  rw [neutralDiffusion, J₀_det, J₀_00, J₀_11]
  norm_num

lemma J₀_admissible : 0 < (J₀) 0 0 * (1 / 2 : ℝ) ^ 2 - 1 * ((1 / 2 : ℝ) ^ 2) ^ 2 := by
  rw [J₀_00]
  norm_num

lemma J₀_trace_neg : (J₀).trace - (1 / 2 : ℝ) ^ 2 * (1 + 100 / 11) < 0 := by
  rw [J₀_trace]
  norm_num

/-- The reduced map `G(a, d) = leadingEigenvalue (J₀ - (1/2)² D(d)) - a²`. -/
noncomputable def G₀ (p : ℝ × ℝ) : ℝ := leadingEigenvalue (modeMatrix J₀ 1 p.2 (1 / 2)) - p.1 ^ 2

/-- The steady-state map `F((x, y), d) = (x G₀(x, d), y - x²)`. -/
noncomputable def F₀ (q : (ℝ × ℝ) × ℝ) : ℝ × ℝ := (q.1.1 * G₀ (q.1.1, q.2), q.1.2 - q.1.1 ^ 2)

/-- The correction `W(a, d) = (0, a²)`. -/
def W₀ (p : ℝ × ℝ) : ℝ × ℝ := (0, p.1 ^ 2)

/-- `G₀` is `C¹` at `(0, 100/11)`. -/
lemma G₀_contDiffAt : ContDiffAt ℝ 1 G₀ ((0 : ℝ), (100 / 11 : ℝ)) := by
  have hfun : G₀ = fun p : ℝ × ℝ => ((J₀).trace - (1 / 2) ^ 2 * (1 + p.2) +
      Real.sqrt (((J₀).trace - (1 / 2) ^ 2 * (1 + p.2)) ^ 2 -
        4 * (1 * p.2 * ((1 / 2) ^ 2) ^ 2 - (p.2 * (J₀) 0 0 + 1 * (J₀) 1 1) * (1 / 2) ^ 2 +
          (J₀).det))) / 2 - p.1 ^ 2 := by
    funext p
    rw [G₀, leadingEigenvalue, trace_modeMatrix, det_modeMatrix, dispersionDet]
  rw [hfun]
  have hD : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => ((J₀).trace - (1 / 2) ^ 2 * (1 + p.2)) ^ 2 -
      4 * (1 * p.2 * ((1 / 2) ^ 2) ^ 2 - (p.2 * (J₀) 0 0 + 1 * (J₀) 1 1) * (1 / 2) ^ 2 +
        (J₀).det)) ((0 : ℝ), (100 / 11 : ℝ)) := by
    fun_prop
  have hne : ((J₀).trace - (1 / 2) ^ 2 * (1 + (100 / 11 : ℝ))) ^ 2 -
      4 * (1 * (100 / 11 : ℝ) * ((1 / 2) ^ 2) ^ 2 -
        ((100 / 11 : ℝ) * (J₀) 0 0 + 1 * (J₀) 1 1) * (1 / 2) ^ 2 + (J₀).det) ≠ 0 := by
    rw [J₀_trace, J₀_00, J₀_11, J₀_det]
    norm_num
  have hT : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (J₀).trace - (1 / 2) ^ 2 * (1 + p.2))
      ((0 : ℝ), (100 / 11 : ℝ)) := by
    fun_prop
  exact ((hT.add (hD.sqrt hne)).div_const 2).sub (by fun_prop)

/-! ### The reduction hypotheses hold for the instance, from the definitions -/

lemma W₀_coord (p : ℝ × ℝ) : ContinuousLinearMap.fst ℝ ℝ ℝ (W₀ p) = 0 := rfl

lemma W₀_continuous : Continuous W₀ := by
  unfold W₀
  fun_prop

/-- The zeros of `F₀` are the points `a φ + W₀(a, d)` with `a G₀(a, d) = 0`. -/
lemma F₀_eq_zero_iff (q : (ℝ × ℝ) × ℝ) :
    F₀ q = 0 ↔ ∃ a : ℝ, q.1 = a • ((1 : ℝ), (0 : ℝ)) + W₀ (a, q.2) ∧ a * G₀ (a, q.2) = 0 := by
  obtain ⟨⟨x, y⟩, d⟩ := q
  simp only [F₀, W₀, Prod.mk_eq_zero, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
    Prod.mk_add_mk, zero_add, add_zero, Prod.mk.injEq, sub_eq_zero]
  constructor
  · rintro ⟨hG, hy⟩
    exact ⟨x, ⟨rfl, hy⟩, hG⟩
  · rintro ⟨a, ⟨rfl, hy⟩, hG⟩
    exact ⟨hG, hy⟩

/-! ### Non-vacuity: the theorem yields nonzero steady states -/

/-- **Non-vacuity of `turing_patternBranch_of_reduction`.** For the instance, the critical
eigenvalue crosses zero transversally at `d₀ = 100/11`, and for small `a ≠ 0` the point
`(a, a²)` is a nonzero steady state of `F₀` at `d = β(a)`. -/
example : ∃ β : ℝ → ℝ, β 0 = 100 / 11 ∧
    ∀ᶠ a in 𝓝[≠] (0 : ℝ), F₀ ((a, a ^ 2), β a) = 0 ∧ ((a, a ^ 2) : ℝ × ℝ) ≠ 0 := by
  obtain ⟨-, β, hβ0, -, -, hbr, -, -⟩ :=
    turing_patternBranch_of_reduction (F := F₀) (φ := ((1 : ℝ), (0 : ℝ)))
      (κ := ContinuousLinearMap.fst ℝ ℝ ℝ) (W := W₀) (g := fun p => p.1 * G₀ p) (J := J₀)
      (du := 1) (k := 1 / 2) (d₀ := 100 / 11) (G := G₀) rfl W₀_coord
      (Eventually.of_forall fun d => by simp [W₀]) W₀_continuous.continuousAt
      (Eventually.of_forall F₀_eq_zero_iff) (Eventually.of_forall fun p => rfl)
      J₀_trace_neg J₀_admissible J₀_neutral.symm
      (G₀_contDiffAt.hasStrictFDerivAt one_ne_zero)
      (Eventually.of_forall fun d => by simp [G₀])
  refine ⟨β, hβ0, ?_⟩
  filter_upwards [hbr] with a ⟨hF, hne⟩
  have hpt : a • ((1 : ℝ), (0 : ℝ)) + W₀ (a, β a) = (a, a ^ 2) := by simp [W₀]
  rw [hpt] at hF hne
  exact ⟨hF, hne⟩

/-! ### Boundary values computed from the definitions -/

/-- The branch state `(a, a²)` is a zero of the second component of `F₀` for every `d`, and it is
nonzero exactly when `a ≠ 0`. -/
example (a d : ℝ) : (F₀ ((a, a ^ 2), d)).2 = 0 := by simp [F₀]

example {a : ℝ} (ha : a ≠ 0) : ((a, a ^ 2) : ℝ × ℝ) ≠ 0 := by
  intro h
  exact ha (congrArg Prod.fst h)

/-- The homogeneous state is a steady state for every `d`. -/
example (d : ℝ) : F₀ (0, d) = 0 := by simp [F₀]

/-- At `d₀ = 100/11` the critical eigenvalue of mode `k = 1/2` is `0`. -/
example : leadingEigenvalue (modeMatrix J₀ 1 (100 / 11) (1 / 2)) = 0 := by
  rw [leadingEigenvalue, trace_modeMatrix, det_modeMatrix, dispersionDet, J₀_trace, J₀_00,
    J₀_11, J₀_det]
  have h : Real.sqrt ((-1 / 5 - (1 / 2 : ℝ) ^ 2 * (1 + 100 / 11)) ^ 2 -
      4 * (1 * (100 / 11) * ((1 / 2) ^ 2) ^ 2 - (100 / 11 * (4 / 5) + 1 * -1) * (1 / 2) ^ 2 +
        1)) = 1 / 5 + (1 / 2 : ℝ) ^ 2 * (1 + 100 / 11) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num
  rw [h]
  ring

/-- At `d = 10 > d₀` the critical eigenvalue of mode `k = 1/2` is positive: the determinant of
`J₀ - (1/2)² D(10)` is `-1/8 < 0`. -/
example : 0 < leadingEigenvalue (modeMatrix J₀ 1 10 (1 / 2)) := by
  rw [leadingEigenvalue, trace_modeMatrix, det_modeMatrix, dispersionDet, J₀_trace, J₀_00,
    J₀_11, J₀_det]
  have h : 59 / 20 < Real.sqrt ((-1 / 5 - (1 / 2 : ℝ) ^ 2 * (1 + 10)) ^ 2 -
      4 * (1 * 10 * ((1 / 2) ^ 2) ^ 2 - (10 * (4 / 5) + 1 * -1) * (1 / 2) ^ 2 + 1)) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

end MathlibExtTest.Biology.Dynamics.TuringBranchApplication
