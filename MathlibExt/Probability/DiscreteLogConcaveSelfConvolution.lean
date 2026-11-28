/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Self-convolution of log-concave probability mass functions on ℤᵈ (Oberwolfach Report 58/2024)

M. Fradelizi (with L. Gavalakis and M. Rapaport), On the monotonicity of discrete entropy for
log-concave random vectors in `ℤᵈ`, Oberwolfach Report 58/2024, p. 3360: a probability mass function
on `ℤᵈ` is log-concave if it is the restriction of a log-concave function on `ℝᵈ`; does
self-convolution preserve this property?
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.Probability.DiscreteLogConcaveSelfConvolutionOWR14298808Problem013Wanted

/-!
Source: M. Fradelizi (with L. Gavalakis and M. Rapaport), On the monotonicity of discrete entropy
for log-concave random vectors in Z^d, in Convex Geometry and its Applications, Oberwolfach Reports
21 (2024), no. 58, p. 3360, DOI 10.4171/OWR/2024/58. UnsolvedMath record UM-30006136
(`OWR-14298808-013`), dataset ulamai/UnsolvedMath v1.8.0.

The report calls a probability mass function `p` on `ℤᵈ` log-concave if some log-concave `f : ℝᵈ →
ℝ` (`f ≥ 0` and `f((1 - t) x + t y) ≥ f(x)^{1 - t} f(y)^t` for `t ∈ [0, 1]`, the standard
definition) restricts to `p` on `ℤᵈ`, and states "This is an open question to know if
self-convolution preserves this definition"; the self-convolution is `(p * p)(z) = ∑ₓ p(x) p(z -
x)`. The statement is the positive answer in every dimension `d`, refuted. MathlibExt's
`ThinShell.IsLogConcaveDensity` also requires Borel measurability, which the report's definition
does not, so the property is written out here.
-/

/-- `f : ℝᵈ → ℝ` is log-concave: `f ≥ 0` and `f((1 - t) x + t y) ≥ f(x)^{1 - t} f(y)^t` for
`t ∈ [0, 1]`. -/
def IsLogConcaveFunction {d : ℕ} (f : (Fin d → ℝ) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ∀ x y : Fin d → ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f x ^ (1 - t) * f y ^ t ≤ f ((1 - t) • x + t • y)

/-- `p` is a probability mass function on `ℤᵈ`: nonnegative, summable, total mass `1`. -/
def IsProbabilityMassFunction {d : ℕ} (p : (Fin d → ℤ) → ℝ) : Prop :=
  (∀ z, 0 ≤ p z) ∧ Summable p ∧ ∑' z, p z = 1

/-- `p` is the restriction to `ℤᵈ` of a log-concave function on `ℝᵈ` (the report's definition of a
log-concave probability mass function on `ℤᵈ`). -/
def IsLogConcaveRestriction {d : ℕ} (p : (Fin d → ℤ) → ℝ) : Prop :=
  ∃ f : (Fin d → ℝ) → ℝ, IsLogConcaveFunction f ∧ ∀ z, p z = f fun i => (z i : ℝ)

/-- The self-convolution `(p * p)(z) = ∑_x p(x) p(z - x)`. -/
noncomputable def selfConvolution {d : ℕ} (p : (Fin d → ℤ) → ℝ) : (Fin d → ℤ) → ℝ :=
  DiscreteConvolution.addRingConvolution p p

/-- **Self-convolution as a sum over the lattice.** Reindex the additive convolution at `z`
by its first summand `x`, with second summand `z - x`. This equality of totalized sums does
not require summability. -/
theorem selfConvolution_eq_tsum {d : ℕ} (p : (Fin d → ℤ) → ℝ) (z : Fin d → ℤ) :
    selfConvolution p z = ∑' x, p x * p (z - x) := by
  let e : (Fin d → ℤ) ≃ DiscreteConvolution.addFiber z :=
    { toFun := fun x => ⟨(x, z - x), DiscreteConvolution.mem_addFiber.mpr (by simp)⟩
      invFun := fun ab => ab.val.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨a, b⟩, hab⟩
        have h : a + b = z := DiscreteConvolution.mem_addFiber.mp hab
        apply Subtype.ext
        change (a, z - a) = (a, b)
        rw [← h, add_comm a b, add_sub_cancel_right] }
  rw [selfConvolution, DiscreteConvolution.addRingConvolution_apply]
  exact (e.tsum_eq (fun ab => p ab.val.1 * p ab.val.2)).symm

/-- The open question of Fradelizi's abstract (Oberwolfach Report 58/2024, p. 3360), positive
answer: for every `d`, the self-convolution of a probability mass function on `ℤᵈ` that is the
restriction of a log-concave function on `ℝᵈ` is again such a restriction. -/
def selfConvolutionPreservesLogConcavity : Prop :=
  ∀ (d : ℕ) (p : (Fin d → ℤ) → ℝ), IsProbabilityMassFunction p → IsLogConcaveRestriction p →
    IsLogConcaveRestriction (selfConvolution p)

private def reeveVertices : Finset (Fin 3 → ℤ) :=
  {![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 2]}

private def reeveRegion (x : Fin 3 → ℝ) : Prop :=
  0 ≤ x 2 ∧ x 2 / 2 ≤ x 0 ∧ x 2 / 2 ≤ x 1 ∧ x 0 + x 1 ≤ 1 + x 2 / 2

private def realPoint (v : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => v i

private lemma reeveRegion_mix {x y : Fin 3 → ℝ} (hx : reeveRegion x) (hy : reeveRegion y)
    {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) : reeveRegion ((1 - t) • x + t • y) := by
  rcases hx with ⟨hx₀, hx₁, hx₂, hx₃⟩
  rcases hy with ⟨hy₀, hy₁, hy₂, hy₃⟩
  have ht₀ := sub_nonneg.mpr ht₁
  simp only [reeveRegion, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨add_nonneg (mul_nonneg ht₀ hx₀) (mul_nonneg ht hy₀), ?_, ?_, ?_⟩
  · nlinarith only [mul_nonneg ht₀ (sub_nonneg.mpr hx₁), mul_nonneg ht (sub_nonneg.mpr hy₁)]
  · nlinarith only [mul_nonneg ht₀ (sub_nonneg.mpr hx₂), mul_nonneg ht (sub_nonneg.mpr hy₂)]
  · nlinarith only [mul_nonneg ht₀ (sub_nonneg.mpr hx₃), mul_nonneg ht (sub_nonneg.mpr hy₃)]

private lemma reeveRegion_realPoint_iff (v : Fin 3 → ℤ) :
    reeveRegion (realPoint v) ↔ v ∈ reeveVertices := by
  constructor
  · rintro ⟨h₀, h₁, h₂, h₃⟩
    change (0 : ℝ) ≤ (v 2 : ℝ) at h₀
    change (v 2 : ℝ) / 2 ≤ (v 0 : ℝ) at h₁
    change (v 2 : ℝ) / 2 ≤ (v 1 : ℝ) at h₂
    change (v 0 : ℝ) + (v 1 : ℝ) ≤ 1 + (v 2 : ℝ) / 2 at h₃
    have hz : 0 ≤ v 2 := by exact_mod_cast h₀
    have hx : v 2 ≤ 2 * v 0 := by
      exact_mod_cast (show (v 2 : ℝ) ≤ 2 * (v 0 : ℝ) by linarith only [h₁])
    have hy : v 2 ≤ 2 * v 1 := by
      exact_mod_cast (show (v 2 : ℝ) ≤ 2 * (v 1 : ℝ) by linarith only [h₂])
    have hxy : 2 * (v 0 + v 1) ≤ 2 + v 2 := by
      exact_mod_cast (show 2 * ((v 0 : ℝ) + (v 1 : ℝ)) ≤ 2 + (v 2 : ℝ) by linarith only [h₃])
    have hcases : (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) ∨ (v 0 = 1 ∧ v 1 = 0 ∧ v 2 = 0) ∨
        (v 0 = 0 ∧ v 1 = 1 ∧ v 2 = 0) ∨ (v 0 = 1 ∧ v 1 = 1 ∧ v 2 = 2) := by omega
    have heq (a b c : ℤ) (ha : v 0 = a) (hb : v 1 = b) (hc : v 2 = c) : v = ![a, b, c] := by
      funext i
      fin_cases i <;> assumption
    rcases hcases with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩ <;>
      rw [heq _ _ _ h₀ h₁ h₂] <;> simp [reeveVertices]
  · intro hv
    simp only [reeveVertices, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> norm_num [reeveRegion, realPoint, Matrix.cons_val]

private noncomputable def reeveMass (v : Fin 3 → ℤ) : ℝ := if v ∈ reeveVertices then 1 / 4 else 0

private noncomputable def reeveExtension (x : Fin 3 → ℝ) : ℝ :=
  open Classical in if reeveRegion x then 1 / 4 else 0

private lemma reeveMass_nonneg (v : Fin 3 → ℤ) : 0 ≤ reeveMass v := by
  unfold reeveMass
  split <;> norm_num

private lemma reeveMass_isPMF : IsProbabilityMassFunction reeveMass := by
  have hz (v : Fin 3 → ℤ) (hv : v ∉ reeveVertices) : reeveMass v = 0 := by simp [reeveMass, hv]
  refine ⟨reeveMass_nonneg, summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  have hc : reeveVertices.card = 4 := by decide
  calc
    _ = ∑ _v ∈ reeveVertices, (1 / 4 : ℝ) :=
      Finset.sum_congr rfl fun v hv => by simp [reeveMass, hv]
    _ = 1 := by norm_num [Finset.sum_const, hc, nsmul_eq_mul]

private lemma reeveMass_isRestriction : IsLogConcaveRestriction reeveMass := by
  classical
  refine ⟨reeveExtension, ⟨fun x => ?_, ?_⟩, fun v => ?_⟩
  · unfold reeveExtension
    split <;> norm_num
  · intro x y t ht ht₁
    rcases ht.eq_or_lt with rfl | ht
    · simp [Real.rpow_zero, Real.rpow_one]
    rcases ht₁.eq_or_lt with rfl | ht₁
    · simp [Real.rpow_zero, Real.rpow_one]
    have hnonneg (v : Fin 3 → ℝ) : 0 ≤ reeveExtension v := by
      unfold reeveExtension
      split <;> norm_num
    by_cases hx : reeveRegion x <;> by_cases hy : reeveRegion y
    · simp only [reeveExtension, ite_eq_left hx, ite_eq_left hy,
        ite_eq_left (reeveRegion_mix hx hy ht.le ht₁.le)]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 4), sub_add_cancel, Real.rpow_one]
    · rw [show reeveExtension y = 0 by simp [reeveExtension, hy], Real.zero_rpow ht.ne', mul_zero]
      exact hnonneg _
    · rw [show reeveExtension x = 0 by simp [reeveExtension, hx],
        Real.zero_rpow (sub_ne_zero.mpr ht₁.ne'), zero_mul]
      exact hnonneg _
    · rw [show reeveExtension y = 0 by simp [reeveExtension, hy], Real.zero_rpow ht.ne', mul_zero]
      exact hnonneg _
  · change reeveMass v = reeveExtension (realPoint v)
    simp [reeveMass, reeveExtension, reeveRegion_realPoint_iff]

private lemma reeveConvolution_pos (x y : Fin 3 → ℤ)
    (hx : x ∈ reeveVertices) (hy : y ∈ reeveVertices) :
    0 < selfConvolution reeveMass (x + y) := by
  rw [selfConvolution_eq_tsum]
  rw [tsum_eq_sum (s := reeveVertices) (fun v hv => by simp [reeveMass, hv])]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum
    (fun v _ => mul_nonneg (reeveMass_nonneg v) (reeveMass_nonneg (x + y - v))) hx)
  have heq : x + y - x = y := by simp [add_comm x y]
  norm_num [heq, reeveMass, hx, hy]

private lemma reeveVertex_height (v : Fin 3 → ℤ) (hv : v ∈ reeveVertices) : v 2 = 0 ∨ v 2 = 2 := by
  simp only [reeveVertices, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide

private lemma reeveConvolution_midpoint_zero : selfConvolution reeveMass ![1, 1, 1] = 0 := by
  rw [selfConvolution_eq_tsum]
  have hz (v : Fin 3 → ℤ) : reeveMass v * reeveMass (![1, 1, 1] - v) = 0 := by
    by_cases hv : v ∈ reeveVertices
    · have hn : ![1, 1, 1] - v ∉ reeveVertices := by
        intro hv'
        have hh := reeveVertex_height _ hv'
        change 1 - v 2 = 0 ∨ 1 - v 2 = 2 at hh
        have hv₂ := reeveVertex_height _ hv
        omega
      rw [show reeveMass (![1, 1, 1] - v) = 0 from ite_eq_right hn]
      exact mul_zero _
    · rw [show reeveMass v = 0 from ite_eq_right hv]
      exact zero_mul _
  simp only [hz, tsum_zero]

/--
Resolved false: Fradelizi, Gavalakis and Rapaport answer the question in their paper with a
counterexample in dimension `3` (Remark 12): the support of a log-concave probability mass function
on `ℤᵈ` is `ℤᵈ`-convex (the lattice points of its convex hull), the Reeve tetrahedron `S = {(0,0,0),
(1,0,0), (0,1,0), (1,1,2)}` is `ℤ³`-convex, and `S + S` misses `(1,1,1)`, the midpoint of `(1,1,0)`
and `(1,1,2)`, so it is not `ℤ³`-convex; the uniform distribution on `S` is log-concave and its
self-convolution, supported on `S + S`, is not. The same remark records that convolution preserves
log-concavity in dimension `1` and that `S + S` is `ℤ²`-convex for every `ℤ²`-convex `S`, so
dimension `2` is not settled by this argument. Source: M. Fradelizi (with L. Gavalakis and M.
Rapaport), On the monotonicity of discrete entropy for log-concave random vectors in Z^d, in Convex
Geometry and its Applications, Oberwolfach Reports 21 (2024), no. 58, p. 3360, DOI
10.4171/OWR/2024/58; resolution: M. Fradelizi, L. Gavalakis and M. Rapaport, On the monotonicity of
discrete entropy for log-concave random vectors on Z^d, Discrete Comput. Geom. (2026), DOI
10.1007/s00454-025-00813-7, arXiv:2401.15462, Remark 12, with Definitions 10-11 (A ⊂ Z^d is
Z^d-convex iff its indicator is log-concave extensible; the support of a log-concave function on Z^d
is Z^d-convex): the Reeve tetrahedron S = {(0,0,0),(1,0,0),(0,1,0),(1,1,2)} is Z^3-convex, but S + S
does not contain (1,1,1) and is thus not Z^3-convex; arXiv v4 comments: 'A counterexample was added
to Remark 12 answering a question from the previous version',
https://doi.org/10.1007/s00454-025-00813-7.
-/
public theorem selfConvolutionPreservesLogConcavity_refuted :
    ¬ selfConvolutionPreservesLogConcavity := by
  intro h
  obtain ⟨f, hf, hrestrict⟩ := h 3 reeveMass reeveMass_isPMF reeveMass_isRestriction
  change ∀ z, selfConvolution reeveMass z = f (realPoint z) at hrestrict
  let a : Fin 3 → ℤ := ![1, 0, 0] + ![0, 1, 0]
  let b : Fin 3 → ℤ := ![0, 0, 0] + ![1, 1, 2]
  let c : Fin 3 → ℤ := ![1, 1, 1]
  have ha : 0 < selfConvolution reeveMass a :=
    reeveConvolution_pos ![1, 0, 0] ![0, 1, 0] (by decide) (by decide)
  have hb : 0 < selfConvolution reeveMass b :=
    reeveConvolution_pos ![0, 0, 0] ![1, 1, 2] (by decide) (by decide)
  have hmid : (1 - (1 / 2 : ℝ)) • realPoint a + (1 / 2 : ℝ) • realPoint b = realPoint c := by
    funext i
    fin_cases i <;> norm_num [a, b, c, realPoint, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val]
  have hlog := hf.2 (realPoint a) (realPoint b) (1 / 2) (by norm_num) (by norm_num)
  rw [hmid, ← hrestrict a, ← hrestrict b, ← hrestrict c,
    show selfConvolution reeveMass c = 0 from reeveConvolution_midpoint_zero] at hlog
  exact (not_lt_of_ge hlog) (mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _))

end MathlibExt.Probability.DiscreteLogConcaveSelfConvolutionOWR14298808Problem013Wanted
