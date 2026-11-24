/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperator
import MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

/-! # Scottish Book Problem 167 via the unilateral shift

On real `ℓ²`, the unilateral shift is an isometry. The norm of the sequence with coordinates
weighted by successive powers of `1/2` is positive on the unit sphere and is halved by the shift.
This gives a direct counterexample with one observable, without using Klee's homeomorphism.
-/

@[expose] public section

open scoped ENNReal

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook167Wanted

open MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperator
  MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

/-- **Scottish Book Problem 167.** Ulam's claim that for every infinite-dimensional real Hilbert
space $H$ with unit sphere $S = \{p \in H : \|p\| = 1\}$, every $n \in \mathbb{N}$, all
continuous functions $f_1, \dots, f_n : S \to \mathbb{R}$ and every continuous map
$T : S \to S$, there is a point $p_0 \in S$ with $f_i(T(p_0)) = f_i(p_0)$ for every $i$. -/
def ScottishBookProblem167Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
    ¬ Module.Finite ℝ E →
    ∀ (n : ℕ) (f : Fin n → ↥(Metric.sphere (0 : E) 1) → ℝ)
      (T : ↥(Metric.sphere (0 : E) 1) → ↥(Metric.sphere (0 : E) 1)),
      Continuous T → (∀ i, Continuous (f i)) →
      ∃ p0 : ↥(Metric.sphere (0 : E) 1), ∀ i, f i (T p0) = f i p0

private abbrev H := ↥(lp (fun _ : ℕ => ℝ) 2)

private theorem weights_bounded : ∃ C : ℝ, ∀ n : ℕ, ‖(1 / 2 : ℝ) ^ n‖ ≤ C := by
  refine ⟨1, fun n => ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_one₀ (by norm_num) (by norm_num)

private noncomputable def weighted : H →L[ℝ] H :=
  diagonalCLM (fun n => (1 / 2 : ℝ) ^ n) weights_bounded

private theorem weighted_shift (x : H) :
    weighted (shiftCLM x) = (1 / 2 : ℝ) • shiftCLM (weighted x) := by
  apply lp.ext
  funext n
  rw [lp_smul_apply]
  cases n with
  | zero =>
    simp only [weighted, diagonalCLM_apply, shiftCLM_apply, shiftFun_zero, mul_zero]
  | succ n =>
    simp only [weighted, diagonalCLM_apply, shiftCLM_apply, shiftFun_succ, pow_succ]
    ring

private theorem weighted_ne_zero {x : H} (hx : x ≠ 0) : weighted x ≠ 0 := by
  intro h
  apply hx
  apply lp.ext
  funext n
  have hn : (1 / 2 : ℝ) ^ n * x n = 0 := by
    have hcoord := congrArg (fun z : H => z n) h
    simpa only [weighted, diagonalCLM_apply, lp.coeFn_zero, Pi.zero_apply] using hcoord
  exact (mul_eq_zero.mp hn).resolve_left (pow_ne_zero _ (by norm_num))

private theorem H_infinite : ¬ Module.Finite ℝ H := by
  intro h
  let : Module.Finite ℝ H := h
  let v (n : ℕ) : H := lp.single 2 n 1
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [lp.inner_eq_tsum, tsum_eq_single i]
    · by_cases hij : i = j
      · subst j
        simp [v, lp.single_apply]
      · simp [v, hij]
    · intro n hn
      simp [v, hn]
  let : Finite ℕ := hv.linearIndependent.finite
  exact not_finite ℕ

-- The first coordinate unit vector has weighted norm one and shifts to weighted norm one half.
example : ‖weighted (shiftCLM (lp.single 2 0 1 : H))‖ = 1 / 2 := by
  have hw : weighted (lp.single 2 0 1 : H) = lp.single 2 0 1 := by
    rw [weighted, diagonalCLM_single, pow_zero, one_smul]
  rw [weighted_shift, norm_smul, norm_shiftCLM_apply, hw,
    lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞)), norm_one,
    Real.norm_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)), mul_one]

/--
**Negative answer to Scottish Book Problem 167.** Ulam's claim in Problem 167 is false: there
are an infinite-dimensional real Hilbert space $H$ with unit sphere $S$, a number
$n \in \mathbb{N}$, continuous functions $f_1, \dots, f_n : S \to \mathbb{R}$ and a continuous map
$T : S \to S$ such that no point $p_0 \in S$ satisfies $f_i(T(p_0)) = f_i(p_0)$ for every $i$.

The claim fails already for one function.

Source: S. Ulam, Problem 167 of the Scottish Book; refuted via V. Klee's
homeomorphism of the Hilbert sphere onto the whole Hilbert space: composing
that homeomorphism with a translation gives a continuous `T` and a continuous
`f` with no point `p0` satisfying `f (T p0) = f p0`. See the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem ulam167_refuted : ¬ ScottishBookProblem167Claim := by
  intro C
  let S := ↥(Metric.sphere (0 : H) 1)
  have hT (x : S) : shiftCLM (x : H) ∈ Metric.sphere (0 : H) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_shiftCLM_apply] using x.property
  let T (x : S) : S := ⟨shiftCLM (x : H), hT x⟩
  let f (_ : Fin 1) (x : S) : ℝ := ‖weighted (x : H)‖
  have hf (i : Fin 1) : Continuous (f i) :=
    (weighted.continuous.comp continuous_subtype_val).norm
  have hc : Continuous T :=
    ((shiftCLM (𝕜 := ℝ)).continuous.comp continuous_subtype_val).subtype_mk hT
  obtain ⟨x, heq⟩ := C H H_infinite 1 f T hc hf
  have hxnorm : ‖(x : H)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hx0 : (x : H) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxnorm
    exact zero_ne_one hxnorm
  have hxpos : 0 < ‖weighted (x : H)‖ := norm_pos_iff.mpr (weighted_ne_zero hx0)
  have h := heq 0
  change ‖weighted (shiftCLM (x : H))‖ = ‖weighted (x : H)‖ at h
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  rw [weighted_shift, norm_smul, norm_shiftCLM_apply, Real.norm_of_nonneg hhalf] at h
  linarith

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook167Wanted
