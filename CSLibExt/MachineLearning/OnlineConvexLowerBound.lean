/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Analysis.Fourier.BooleanCubeInfluence
public import MathlibExt.Probability.BooleanCubeMoments
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lower bound for online convex optimization

One-dimensional scaled form of the `Ω(D * G * √T)` regret lower bound for
online convex optimization (Hazan, "Introduction to online convex
optimization", Section 3.2, Theorem 3.2).

Hazan phrases the result on the `n`-dimensional hypercube
`K = {x : ‖x‖∞ ≤ 1}` with linear losses `f_v(x) = v ⬝ x` over vertices
`v ∈ {±1}^n`. The one-dimensional scaled instance here already forces the
bound for every `D` and `G`: the domain is `K = [-D / 2, D / 2]` and the
losses are `x ↦ σ_t * G * x` with signs `σ_t ∈ {±1}`.

Everything is finite counting over sign sequences `σ : Fin T → Bool` with
the counting measure; no probability library is used beyond `Finset` sums
and real moments. The moment route: for `S = ∑ σ_t` (as reals), the second
moment `E[S ^ 2] = T` is the constant-coefficient specialization of the
checked Rademacher second moment, `E[S ^ 4] ≤ 3 * T ^ 2`, and
Cauchy-Schwarz applied twice gives `(∑ S ^ 2) ^ 3 ≤ (∑ |S|) ^ 2 * ∑ S ^ 4`,
hence `E|S| ≥ √(T / 3)`.

A randomized online strategy is a distribution over the deterministic
adaptive strategies modeled here, and the same expectation bound applies
to its mean; this remark is not formalized.
-/

open scoped BigOperators

@[expose] public section

namespace Cslib.MachineLearning.OnlineConvexLowerBound

/-- Round-`t` play of a deterministic online algorithm: the algorithm sees
only the first `t` signs of the length-`T` sequence. -/
def playAt (T : ℕ) (A : ∀ t : ℕ, (Fin t → Bool) → ℝ)
    (σ : Fin T → Bool) (t : Fin T) : ℝ :=
  A t.val fun i : Fin t.val => σ (Fin.castLE (le_of_lt (Fin.isLt t)) i)

/-- Regret of a deterministic online algorithm against a sign sequence at
gradient scale `G` on `[-D / 2, D / 2]`, with the comparator minimum
already evaluated (`comparator_lower_bound`, `comparator_attained`). -/
noncomputable def regret (T : ℕ) (A : ∀ t : ℕ, (Fin t → Bool) → ℝ) (D G : ℝ)
    (σ : Fin T → Bool) : ℝ :=
  (∑ t : Fin T, BooleanCube.cubeVal (σ t) * G * playAt T A σ t) +
    G * (D / 2) * |∑ t : Fin T, BooleanCube.cubeVal (σ t)|

/-- The constant-one sum over sign sequences. -/
private theorem sum_one_sign (T : ℕ) :
    ∑ _σ : Fin T → Bool, (1 : ℝ) = (2 : ℝ) ^ T := by
  simp

/-- The comparator minimum over `|x| ≤ D / 2`: no feasible `x` beats
`-(D / 2) * G * |S|`. This evaluates the comparator term in `regret`. -/
theorem comparator_lower_bound (D G S x : ℝ) (_hD : 0 ≤ D) (hG : 0 ≤ G)
    (hx : |x| ≤ D / 2) : -(D / 2) * G * |S| ≤ S * G * x := by
  have h1 : -(|S| * G * |x|) ≤ S * G * x := by
    have h := neg_abs_le (S * G * x)
    rwa [abs_mul, abs_mul, abs_of_nonneg hG] at h
  have h2 : |S| * G * |x| ≤ |S| * G * (D / 2) :=
    mul_le_mul_of_nonneg_left hx (mul_nonneg (abs_nonneg S) hG)
  have h3 : -(D / 2) * G * |S| = -(|S| * G * (D / 2)) := by ring
  rw [h3]
  exact (neg_le_neg h2).trans h1

/-- The comparator bound is attained: some feasible `x` achieves
`-(D / 2) * G * |S|`. -/
theorem comparator_attained (D G S : ℝ) (hD : 0 ≤ D) (_hG : 0 ≤ G) :
    ∃ x : ℝ, |x| ≤ D / 2 ∧ S * G * x = -(D / 2) * G * |S| := by
  by_cases hS : 0 ≤ S
  · refine ⟨-(D / 2), ?_, ?_⟩
    · rw [abs_neg, abs_of_nonneg (div_nonneg hD zero_le_two)]
    · rw [abs_of_nonneg hS]
      ring
  · refine ⟨D / 2, ?_, ?_⟩
    · rw [abs_of_nonneg (div_nonneg hD zero_le_two)]
    · rw [abs_of_neg (lt_of_not_ge hS)]
      ring

/-- The online play is unchanged by flipping the current coordinate. -/
theorem playAt_flip (T : ℕ) (A : ∀ t : ℕ, (Fin t → Bool) → ℝ)
    (σ : Fin T → Bool) (t : Fin T) :
    playAt T A (BooleanCube.flipCoord σ t) t = playAt T A σ t := by
  simp only [playAt]
  congr 1
  funext i
  have hne : Fin.castLE (le_of_lt (Fin.isLt t)) i ≠ t := by
    intro hcon
    have hval : (Fin.castLE (le_of_lt (Fin.isLt t)) i).val = t.val :=
      congrArg Fin.val hcon
    have h2 : (Fin.castLE (le_of_lt (Fin.isLt t)) i).val = i.val := rfl
    rw [h2] at hval
    exact absurd hval (ne_of_lt (Fin.isLt i))
  exact BooleanCube.flipCoord_apply_of_ne σ hne

/-- A sum that changes sign under the coordinate flip is zero; reindexing
is by `BooleanCube.sum_comp_flipCoord`. -/
private theorem sum_eq_zero_of_flip (T : ℕ) (t : Fin T)
    (f : (Fin T → Bool) → ℝ)
    (hterm : ∀ σ : Fin T → Bool, f (BooleanCube.flipCoord σ t) = -f σ) :
    ∑ σ : Fin T → Bool, f σ = 0 := by
  have hreindex : (∑ σ : Fin T → Bool, f (BooleanCube.flipCoord σ t))
      = ∑ σ : Fin T → Bool, f σ :=
    BooleanCube.sum_comp_flipCoord f t
  have hLHS : (∑ σ : Fin T → Bool, f (BooleanCube.flipCoord σ t))
      = -∑ σ : Fin T → Bool, f σ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun σ _ => hterm σ)
  have hneg : -(∑ σ : Fin T → Bool, f σ)
      = ∑ σ : Fin T → Bool, f σ := hLHS.symm.trans hreindex
  exact eq_zero_of_neg_eq hneg

/-- The algorithm's own play has mean zero against the signs: for each
round, reindexing by the coordinate-`t` flip (`BooleanCube.flipCoord`,
via `BooleanCube.sum_comp_flipCoord`) changes the sign of
`BooleanCube.cubeVal (σ t)` while `playAt` is unchanged, since the
restriction reads only earlier coordinates; the sum equals its negation. -/
theorem online_play_expectation_zero (T : ℕ)
    (A : ∀ t : ℕ, (Fin t → Bool) → ℝ) (t : Fin T) :
    ∑ σ : Fin T → Bool, BooleanCube.cubeVal (σ t) * playAt T A σ t = 0 := by
  apply sum_eq_zero_of_flip T t
  intro σ
  show BooleanCube.cubeVal ((BooleanCube.flipCoord σ t) t)
      * playAt T A (BooleanCube.flipCoord σ t) t =
    -(BooleanCube.cubeVal (σ t) * playAt T A σ t)
  rw [BooleanCube.flipCoord_apply_self, playAt_flip, BooleanCube.cubeVal_not]
  ring

/-- Main lower bound: every deterministic online algorithm on
`[-D / 2, D / 2]` suffers regret at least
`(D * G / 2) * √(T / 3)` against some sign sequence. The comparator term is
already evaluated inside `regret`, with `comparator_lower_bound` and
`comparator_attained` justifying that evaluated form; by averaging,
`online_play_expectation_zero` kills the play term, so mean regret is
`(D * G / 2)` times the mean absolute sign sum, bounded below by
`khintchine_lower`; some sequence attains at least the mean
(`Finset.exists_le_of_sum_le`). -/
theorem oco_lower_bound (T : ℕ) (A : ∀ t : ℕ, (Fin t → Bool) → ℝ)
    (D G : ℝ) (_hT : 0 < T) (hD : 0 < D) (hG : 0 < G)
    (_hA : ∀ (t : ℕ) (s : Fin t → Bool), |A t s| ≤ D / 2) :
    ∃ σ : Fin T → Bool,
      (D * G / 2) * Real.sqrt ((T : ℝ) / 3)
        ≤ regret T A D G σ := by
  have hPreg : ∀ σ : Fin T → Bool, regret T A D G σ
      = (∑ t : Fin T, BooleanCube.cubeVal (σ t) * G * playAt T A σ t) +
        G * (D / 2) * |∑ t : Fin T, BooleanCube.cubeVal (σ t)| :=
    fun σ => rfl
  have hsumP : (∑ σ : Fin T → Bool, ∑ t : Fin T,
      BooleanCube.cubeVal (σ t) * G * playAt T A σ t) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun t _ => ?_)
    have hfactor : (∑ σ : Fin T → Bool,
          BooleanCube.cubeVal (σ t) * G * playAt T A σ t)
        = G * (∑ σ : Fin T → Bool,
          BooleanCube.cubeVal (σ t) * playAt T A σ t) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun σ _ => by ring)
    rw [hfactor, online_play_expectation_zero T A t, mul_zero]
  have hsumC : (∑ σ : Fin T → Bool,
        G * (D / 2) * |∑ t : Fin T, BooleanCube.cubeVal (σ t)|)
      = G * (D / 2)
        * (∑ σ : Fin T → Bool, |∑ t : Fin T, BooleanCube.cubeVal (σ t)|) := by
    rw [← Finset.mul_sum]
  have hnonneg : 0 ≤ G * (D / 2) :=
    mul_nonneg (le_of_lt hG) (div_nonneg (le_of_lt hD) zero_le_two)
  have htot : (∑ σ : Fin T → Bool, regret T A D G σ)
      = G * (D / 2)
        * (∑ σ : Fin T → Bool, |∑ t : Fin T, BooleanCube.cubeVal (σ t)|) := by
    simp only [hPreg, Finset.sum_add_distrib, hsumP, zero_add, hsumC]
  have hmean : (2 : ℝ) ^ T * ((D * G / 2) * Real.sqrt ((T : ℝ) / 3))
      ≤ ∑ σ : Fin T → Bool, regret T A D G σ := by
    rw [htot]
    have hmul := mul_le_mul_of_nonneg_left (MetaMathlibExt.khintchine_lower T) hnonneg
    have heq : (2 : ℝ) ^ T * ((D * G / 2) * Real.sqrt ((T : ℝ) / 3))
        = G * (D / 2) * ((2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3)) := by
      ring
    rw [heq]
    exact hmul
  have hcard : (∑ _σ : Fin T → Bool, (D * G / 2) * Real.sqrt ((T : ℝ) / 3))
      = (2 : ℝ) ^ T * ((D * G / 2) * Real.sqrt ((T : ℝ) / 3)) := by
    have h1 : (∑ _σ : Fin T → Bool, (D * G / 2) * Real.sqrt ((T : ℝ) / 3))
        = ((D * G / 2) * Real.sqrt ((T : ℝ) / 3))
          * ∑ _σ : Fin T → Bool, (1 : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun σ _ => (mul_one _).symm)
    rw [h1, sum_one_sign, mul_comm]
  have hle : (∑ _σ : Fin T → Bool, (D * G / 2) * Real.sqrt ((T : ℝ) / 3))
      ≤ ∑ σ : Fin T → Bool, regret T A D G σ := by
    rw [hcard]
    exact hmean
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_sum_le
    ⟨fun _ => true, Finset.mem_univ _⟩ hle
  exact ⟨σ, hσ⟩

end Cslib.MachineLearning.OnlineConvexLowerBound
