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
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Scottish Book Problem 167 via the unilateral shift

On real `ℓ²`, the unilateral shift is an isometry. The norm of the sequence with coordinates
weighted by successive powers of `1/2` is positive on the unit sphere and is halved by the shift.
This gives a direct counterexample with one observable, without using Klee's homeomorphism.
-/

@[expose] public section

open scoped ENNReal

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook167Wanted

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

private theorem summable_sq (x : H) : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℕ)) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

private theorem norm_sq (x : H) : ‖x‖ ^ (2 : ℕ) = ∑' n : ℕ, ‖x n‖ ^ (2 : ℕ) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x

private def shiftSeq (x : H) : ℕ → ℝ
  | 0 => 0
  | n + 1 => x n

private theorem shiftMem (x : H) : Memℓp (shiftSeq x) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply (summable_nat_add_iff 1).1
  simpa only [shiftSeq] using summable_sq x

private def shift (x : H) : H := ⟨shiftSeq x, shiftMem x⟩

private theorem shift_norm (x : H) : ‖shift x‖ = ‖x‖ := by
  have hs := (summable_sq (shift x)).tsum_eq_zero_add
  rw [← norm_sq (shift x)] at hs
  change ‖shift x‖ ^ (2 : ℕ) = ‖(0 : ℝ)‖ ^ (2 : ℕ) + (∑' n : ℕ, ‖x n‖ ^ (2 : ℕ)) at hs
  rw [← norm_sq x, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] at hs
  simpa only [Real.sqrt_sq (norm_nonneg (shift x)), Real.sqrt_sq (norm_nonneg x)] using
    congrArg Real.sqrt hs

private noncomputable def shiftIso : H →ₗᵢ[ℝ] H where
  toFun := shift
  map_add' x y := by
    apply lp.ext
    funext n
    rw [lp.coeFn_add, Pi.add_apply]
    cases n with
    | zero => change (0 : ℝ) = 0 + 0; rw [zero_add]
    | succ n => rfl
  map_smul' c x := by
    apply lp.ext
    funext n
    cases n with
    | zero => change (0 : ℝ) = c • 0; rw [smul_zero]
    | succ n => rfl
  norm_map' := shift_norm

private noncomputable def weighted (x : H) : H :=
  ⟨fun n => (1 / 2 : ℝ) ^ n * x n, (lp.memℓp x).mono' (fun n => by
    rw [norm_mul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num)))⟩

private theorem weighted_continuous : Continuous weighted := by
  apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  simp only [lp.coeFn_sub, Pi.sub_apply]
  change ‖(1 / 2 : ℝ) ^ n * x n - (1 / 2 : ℝ) ^ n * y n‖ ≤ ‖x n - y n‖
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))

private theorem weighted_shift (x : H) : weighted (shift x) = (1 / 2 : ℝ) • shift (weighted x) := by
  apply lp.ext
  funext n
  rw [lp.coeFn_smul, Pi.smul_apply]
  cases n with
  | zero =>
    change (1 / 2 : ℝ) ^ (0 : ℕ) * 0 = (1 / 2 : ℝ) • 0
    simp
  | succ n =>
    change (1 / 2 : ℝ) ^ (n + 1) * x n = (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * x n)
    rw [pow_succ]; ring

private theorem weighted_ne_zero {x : H} (hx : x ≠ 0) : weighted x ≠ 0 := by
  intro h
  apply hx
  apply lp.ext
  funext n
  have hn : (1 / 2 : ℝ) ^ n * x n = 0 := by
    exact congrArg (fun z : H => z n) h
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
example : ‖weighted (shift (lp.single 2 0 1 : H))‖ = 1 / 2 := by
  have hw : weighted (lp.single 2 0 1 : H) = lp.single 2 0 1 := by
    apply lp.ext
    funext n
    change (1 / 2 : ℝ) ^ n * (lp.single 2 0 1 : H) n = (lp.single 2 0 1 : H) n
    cases n with
    | zero => simp only [pow_zero, one_mul]
    | succ n => rw [lp.single_apply_ne 2 0 _ (Nat.succ_ne_zero n), mul_zero]
  rw [weighted_shift, norm_smul, shift_norm, hw,
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
  have hT (x : S) : shiftIso (x : H) ∈ Metric.sphere (0 : H) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right, shiftIso.norm_map] using x.property
  let T (x : S) : S := ⟨shiftIso (x : H), hT x⟩
  let f (_ : Fin 1) (x : S) : ℝ := ‖weighted (x : H)‖
  have hf (i : Fin 1) : Continuous (f i) :=
    (weighted_continuous.comp continuous_subtype_val).norm
  have hc : Continuous T :=
    (shiftIso.continuous.comp continuous_subtype_val).subtype_mk hT
  obtain ⟨x, heq⟩ := C H H_infinite 1 f T hc hf
  have hxnorm : ‖(x : H)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hx0 : (x : H) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxnorm
    exact zero_ne_one hxnorm
  have hxpos : 0 < ‖weighted (x : H)‖ := norm_pos_iff.mpr (weighted_ne_zero hx0)
  have h := heq 0
  change ‖weighted (shift (x : H))‖ = ‖weighted (x : H)‖ at h
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  rw [weighted_shift, norm_smul, shift_norm, Real.norm_of_nonneg hhalf] at h
  linarith

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook167Wanted
