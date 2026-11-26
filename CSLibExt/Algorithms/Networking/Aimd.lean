/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AIMD convergence to fairness (Chiu--Jain)
-/
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Chiu--Jain AIMD convergence (pinned statements)

Source: D.-M. Chiu and R. Jain, "Analysis of the Increase and Decrease
Algorithms for Congestion Avoidance in Computer Networks", Computer
Networks and ISDN Systems 17 (1989) 1--14.

Model (Section 1.3): `n` users with real loads `x i`, synchronous binary
feedback. The system is overloaded exactly when the total load exceeds a
fixed positive goal. Linear controls update each load by
`x i := a_I + b_I * x i` on increase and `x i := a_D + b_D * x i` on
decrease. AIMD is the instance `b_I = 1`, `a_I > 0`, `a_D = 0`,
`0 < b_D < 1` (paper example (3)). AIAD is the instance `b_I = b_D = 1`,
`a_I > 0`, `a_D < 0` (paper example (2)), with negative results truncated
at zero (page 4, footnote 1). Jain's fairness index (Section 1.4) is
`F(x) = (∑ i, x i)^2 / (n * ∑ i, (x i)^2)`.

Main claims (abstract; Section 2.3): under AIMD from nonnegative loads
with positive total, the fairness index never decreases, tends to `1`,
and the total load is eventually confined to `[b * goal, goal + n * a]`
(it keeps oscillating; the load vector itself need not converge).
Boundary: an explicit AIAD two-cycle whose fairness alternates between
`9/10` and `25/26`, so AIAD fairness does not tend to `1` there.
-/

@[expose] public section
namespace Cslib.Algorithms.Networking.Aimd

open Finset Filter Topology

/-- Total load `X(t) = ∑ i, x i` (Chiu--Jain Section 1.4). -/
noncomputable def total {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i

/-- Jain's fairness index `F(x) = (∑ i, x i)^2 / (n * ∑ i, (x i)^2)`, with `x / 0 = 0`
(Chiu--Jain Section 1.4, fairness display). -/
noncomputable def fairness {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, x i) ^ 2 / ((n : ℝ) * ∑ i, (x i) ^ 2)

/-- The raw synchronous linear control of Chiu--Jain Section 1.3:
`x i := aI + bI * x i` on increase and `x i := aD + bD * x i` on decrease,
with overload exactly when the total exceeds `goal`. There is no clipping
in the raw law. Increasing at equality (`total x = goal` takes the
increase branch) is a declared convention: the paper distinguishes strict
overload and strict underload without assigning equality. -/
noncomputable def linearStep {n : ℕ} (aI bI aD bD goal : ℝ) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  if goal < total x then fun i => aD + bD * x i else fun i => aI + bI * x i

/-- One synchronous AIMD step: if the total exceeds `goal`, every load is
multiplied by `b`; otherwise every load increases by `a`. This is the
linear control of Chiu--Jain Section 1.3 with `a_I = a`, `b_I = 1`,
`a_D = 0`, `b_D = b` (paper example (3)). -/
noncomputable def aimdStep {n : ℕ} (a b goal : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  if goal < total x then fun i => b * x i else fun i => x i + a

/-- One synchronous AIAD step: if the total exceeds `goal`, every load
changes by the (negative) constant `aD`, truncated at zero; otherwise
every load increases by `aI`. This is Chiu--Jain example (2) with the
truncation convention of page 4, footnote 1. -/
noncomputable def aiadStep {n : ℕ} (aI aD goal : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  if goal < total x then fun i => max (x i + aD) 0 else fun i => x i + aI

/-- AIMD is the raw linear control with parameters `a_I = a`, `b_I = 1`,
`a_D = 0`, `b_D = b` (Chiu--Jain example (3)). -/
theorem aimdStep_eq_linearStep {n : ℕ} (a b goal : ℝ) (x : Fin n → ℝ) :
    aimdStep a b goal x = linearStep a 1 0 b goal x := by
  unfold aimdStep linearStep
  split_ifs with h <;> funext i <;> ring

/-- On states where the additive decrease would not clip, AIAD agrees
with the raw linear control with parameters `b_I = b_D = 1`. Without
such a hypothesis the two differ exactly by the page-4 footnote-1
truncation, so no unconditional equality is claimed. -/
theorem aiadStep_eq_linearStep_of_nonneg {n : ℕ} (aI aD goal : ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i + aD) :
    aiadStep aI aD goal x = linearStep aI 1 aD 1 goal x := by
  unfold aiadStep linearStep
  split_ifs with h
  · funext i
    rw [max_eq_left (hx i)]
    ring
  · funext i
    ring

/-- Pure positive multiplicative scaling preserves the fairness index on
the nonzero domain (sufficient condition of Chiu--Jain equation (7) with
`c = 0`; scale independence, Section 1.4 property (b)). -/
theorem fairness_scale {n : ℕ} (x : Fin n → ℝ) {c : ℝ} (hc : 0 < c)
    (hx : (∑ i, (x i) ^ 2) ≠ 0) :
    fairness (fun i => c * x i) = fairness x := by
  unfold fairness
  have hc0 : c ≠ 0 := ne_of_gt hc
  have h1 : (∑ i, c * x i) = c * ∑ i, x i := by
    rw [Finset.mul_sum]
  have h2 : (∑ i, (c * x i) ^ 2) = c ^ 2 * ∑ i, (x i) ^ 2 := by
    simp_rw [mul_pow]
    rw [Finset.mul_sum]
  simp only [] at h1 h2 ⊢
  rw [h1, h2]
  field_simp

/-- The fairness index of nonnegative loads with positive total lies in
`[0, 1]` (Chiu--Jain Section 1.4, property (a)). -/
theorem fairness_mem_Icc {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hxt : 0 < total x) :
    fairness x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold total fairness at *
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hxt' : 0 < ∑ i ∈ (Finset.univ : Finset (Fin n)), x i := by simpa using hxt
  have hex' : ∃ i ∈ (Finset.univ : Finset (Fin n)), 0 < x i :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ => hx i)).mp hxt'
  obtain ⟨j, _, hj⟩ := hex'
  have hQpos' : 0 < ∑ i ∈ (Finset.univ : Finset (Fin n)), (x i) ^ 2 := by
    apply Finset.sum_pos' (fun i _ => sq_nonneg _)
    exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (ne_of_gt hj)⟩
  have hQpos : 0 < ∑ i, (x i) ^ 2 := by simpa using hQpos'
  have hden : 0 < (n : ℝ) * ∑ i, (x i) ^ 2 := mul_pos hnR hQpos
  have hcs : (∑ i, x i) ^ 2 ≤ (n : ℝ) * ∑ i, (x i) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    simpa using h
  constructor
  · exact div_nonneg (sq_nonneg _) (le_of_lt hden)
  · rw [div_le_one hden]
    exact hcs

private theorem sq_sum_pos {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hxt : 0 < total x) : 0 < ∑ i, (x i) ^ 2 := by
  unfold total at hxt
  have hxt' : 0 < ∑ i ∈ (Finset.univ : Finset (Fin n)), x i := by simpa using hxt
  have hex' : ∃ i ∈ (Finset.univ : Finset (Fin n)), 0 < x i :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ => hx i)).mp hxt'
  obtain ⟨j, _, hj⟩ := hex'
  have hQpos' : 0 < ∑ i ∈ (Finset.univ : Finset (Fin n)), (x i) ^ 2 := by
    apply Finset.sum_pos' (fun i _ => sq_nonneg _)
    exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (ne_of_gt hj)⟩
  simpa using hQpos'

private theorem total_scale {n : ℕ} (b : ℝ) (x : Fin n → ℝ) :
    total (fun i => b * x i) = b * total x := by
  unfold total
  rw [Finset.mul_sum]

private theorem total_shift {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    total (fun i => x i + a) = total x + (n : ℝ) * a := by
  unfold total
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem total_aimdStep {n : ℕ} (a b goal : ℝ) (x : Fin n → ℝ) :
    total (aimdStep a b goal x)
      = if goal < total x then b * total x else total x + (n : ℝ) * a := by
  unfold aimdStep
  split_ifs with h
  · exact total_scale b x
  · exact total_shift a x

private theorem sum_sq_shift {n : ℕ} (x : Fin n → ℝ) (a : ℝ) :
    (∑ i, (x i + a) ^ 2)
      = (∑ i, (x i) ^ 2) + 2 * a * (∑ i, x i) + (n : ℝ) * a ^ 2 := by
  have hexp : ∀ i : Fin n, (x i + a) ^ 2 = (x i) ^ 2 + 2 * a * x i + a ^ 2 := by
    intro i
    ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · congr 1
    rw [← Finset.mul_sum]
  · simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- One AIMD step never decreases the fairness index
(Chiu--Jain Section 2.3: the increase has `c = a > 0` and the decrease is
a pure scaling). -/
theorem aimd_fairness_mono_step {n : ℕ} (hn : 0 < n) {a b goal : ℝ}
    (ha : 0 < a) (hb0 : 0 < b) (hb1 : b < 1) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hxt : 0 < total x) :
    fairness x ≤ fairness (aimdStep a b goal x) := by
  have _hb1 := hb1
  unfold aimdStep
  split_ifs with h
  · have hQne : (∑ i, (x i) ^ 2) ≠ 0 := ne_of_gt (sq_sum_pos x hx hxt)
    rw [fairness_scale x hb0 hQne]
  · unfold total fairness at *
    simp only [] at h ⊢
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hQpos : 0 < ∑ i, (x i) ^ 2 := sq_sum_pos x hx hxt
    have hx' : ∀ i, (0 : ℝ) ≤ (fun i => x i + a) i :=
      fun i => add_nonneg (hx i) (le_of_lt ha)
    have hxt' : 0 < total (fun i => x i + a) := by
      rw [total_shift]
      have hna : (0 : ℝ) ≤ (n : ℝ) * a :=
        mul_nonneg (Nat.cast_nonneg _) (le_of_lt ha)
      unfold total at ⊢
      linarith
    have hQ'pos : 0 < ∑ i, (x i + a) ^ 2 := by
      have := sq_sum_pos (fun i => x i + a) hx' hxt'
      simpa using this
    have hden : 0 < (n : ℝ) * ∑ i, (x i) ^ 2 := mul_pos hnR hQpos
    have hden' : 0 < (n : ℝ) * ∑ i, (x i + a) ^ 2 := mul_pos hnR hQ'pos
    have hS' : (∑ i, (x i + a)) = (∑ i, x i) + (n : ℝ) * a := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hQ' := sum_sq_shift x a
    have hcs : (∑ i, x i) ^ 2 ≤ (n : ℝ) * ∑ i, (x i) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
      simp only [Finset.card_univ, Fintype.card_fin] at h
      simpa using h
    rw [div_le_div_iff₀ hden hden', hS', hQ']
    have hD : (0 : ℝ) ≤ (n : ℝ) * (∑ i, (x i) ^ 2) - (∑ i, x i) ^ 2 := by
      linarith
    have hP : (0 : ℝ) ≤ 2 * a * (∑ i, x i) + (n : ℝ) * a ^ 2 := by
      have h1 : (0 : ℝ) < 2 * a * (∑ i, x i) := by positivity
      have h2 : (0 : ℝ) ≤ (n : ℝ) * a ^ 2 := by positivity
      linarith
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnR
    have hfac : ((∑ i, x i) + (n : ℝ) * a) ^ 2 * ((n : ℝ) * (∑ i, (x i) ^ 2))
        - (∑ i, x i) ^ 2
          * ((n : ℝ) * ((∑ i, (x i) ^ 2) + 2 * a * (∑ i, x i) + (n : ℝ) * a ^ 2))
        = (n : ℝ) * ((n : ℝ) * (∑ i, (x i) ^ 2) - (∑ i, x i) ^ 2)
          * (2 * a * (∑ i, x i) + (n : ℝ) * a ^ 2) := by
      ring
    have hnn : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) * (∑ i, (x i) ^ 2) - (∑ i, x i) ^ 2)
        * (2 * a * (∑ i, x i) + (n : ℝ) * a ^ 2) :=
      mul_nonneg (mul_nonneg hn_nonneg hD) hP
    linarith

/-- Nonnegativity is preserved along the AIMD orbit. -/
theorem aimd_orbit_nonneg {n : ℕ} {a b goal : ℝ}
    (ha : 0 < a) (hb0 : 0 < b) (x0 : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x0 i) :
    ∀ (t : ℕ) (i : Fin n), 0 ≤ ((aimdStep a b goal)^[t] x0) i := by
  intro t
  induction t with
  | zero => simpa using hx0
  | succ t ih =>
    intro i
    have hstep : (aimdStep a b goal)^[t + 1] x0
        = aimdStep a b goal ((aimdStep a b goal)^[t] x0) := by
      rw [Function.iterate_succ_apply']
    rw [hstep]
    unfold aimdStep
    split_ifs with h
    · exact mul_nonneg (le_of_lt hb0) (ih i)
    · exact add_nonneg (ih i) (le_of_lt ha)

/-- A positive total stays positive along the AIMD orbit, so the fairness
denominator never degenerates from such a start. -/
theorem aimd_orbit_total_pos {n : ℕ} {a b goal : ℝ}
    (ha : 0 < a) (hb0 : 0 < b) (x0 : Fin n → ℝ) (hxt : 0 < total x0) :
    ∀ t : ℕ, 0 < total ((aimdStep a b goal)^[t] x0) := by
  intro t
  induction t with
  | zero => exact hxt
  | succ t ih =>
    have hstep : (aimdStep a b goal)^[t + 1] x0
        = aimdStep a b goal ((aimdStep a b goal)^[t] x0) := by
      rw [Function.iterate_succ_apply']
    rw [hstep, total_aimdStep]
    split_ifs with h
    · exact mul_pos hb0 ih
    · have hna : (0 : ℝ) ≤ (n : ℝ) * a :=
        mul_nonneg (Nat.cast_nonneg _) (le_of_lt ha)
      linarith

/-- Fairness is nondecreasing along the whole AIMD orbit
(orbit-level form of Chiu--Jain Section 2.3). -/
theorem aimd_fairness_mono_orbit {n : ℕ} (hn : 0 < n) {a b goal : ℝ}
    (ha : 0 < a) (hb0 : 0 < b) (hb1 : b < 1)
    (x0 : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x0 i) (hxt : 0 < total x0) :
    Monotone (fun t : ℕ => fairness ((aimdStep a b goal)^[t] x0)) := by
  apply monotone_nat_of_le_succ
  intro t
  have hnonneg : ∀ i, 0 ≤ ((aimdStep a b goal)^[t] x0) i :=
    fun i => aimd_orbit_nonneg ha hb0 x0 hx0 t i
  have hpos : 0 < total ((aimdStep a b goal)^[t] x0) :=
    aimd_orbit_total_pos ha hb0 x0 hxt t
  have hstep : (aimdStep a b goal)^[t + 1] x0
      = aimdStep a b goal ((aimdStep a b goal)^[t] x0) := by
    rw [Function.iterate_succ_apply']
  rw [hstep]
  exact aimd_fairness_mono_step hn ha hb0 hb1 _ hnonneg hpos

private theorem total_increase_run {n : ℕ} {a b goal : ℝ} (x0 : Fin n → ℝ) (N k : ℕ)
    (h : ∀ j, j < k → total ((aimdStep a b goal)^[N + j] x0) ≤ goal) :
    total ((aimdStep a b goal)^[N + k] x0)
      = total ((aimdStep a b goal)^[N] x0) + (k : ℝ) * ((n : ℝ) * a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : ∀ j, j < k → total ((aimdStep a b goal)^[N + j] x0) ≤ goal :=
      fun j hj => h j (lt_of_lt_of_le hj (Nat.le_succ k))
    have ih' := ih hk
    have hstep : N + (k + 1) = (N + k) + 1 := by ring
    have hiter : (aimdStep a b goal)^[N + (k + 1)] x0
        = aimdStep a b goal ((aimdStep a b goal)^[N + k] x0) := by
      rw [hstep, Function.iterate_succ_apply']
    have hle : total ((aimdStep a b goal)^[N + k] x0) ≤ goal :=
      h k (Nat.lt_succ_self k)
    have hneg : ¬ goal < total ((aimdStep a b goal)^[N + k] x0) :=
      not_lt.mpr hle
    rw [hiter, total_aimdStep, ite_eq_right hneg, ih']
    push_cast
    ring

private theorem total_decrease_run {n : ℕ} {a b goal : ℝ} (x0 : Fin n → ℝ) (N k : ℕ)
    (h : ∀ j, j < k → goal < total ((aimdStep a b goal)^[N + j] x0)) :
    total ((aimdStep a b goal)^[N + k] x0)
      = b ^ k * total ((aimdStep a b goal)^[N] x0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : ∀ j, j < k → goal < total ((aimdStep a b goal)^[N + j] x0) :=
      fun j hj => h j (lt_of_lt_of_le hj (Nat.le_succ k))
    have ih' := ih hk
    have hstep : N + (k + 1) = (N + k) + 1 := by ring
    have hiter : (aimdStep a b goal)^[N + (k + 1)] x0
        = aimdStep a b goal ((aimdStep a b goal)^[N + k] x0) := by
      rw [hstep, Function.iterate_succ_apply']
    have hgt : goal < total ((aimdStep a b goal)^[N + k] x0) :=
      h k (Nat.lt_succ_self k)
    rw [hiter, total_aimdStep, ite_eq_left hgt, ih']
    ring

private theorem lower_step {n : ℕ} {a b goal : ℝ} (ha : 0 < a) (hb0 : 0 < b)
    (x : Fin n → ℝ) (h : b * goal ≤ total x) :
    b * goal ≤ total (aimdStep a b goal x) := by
  rw [total_aimdStep]
  split_ifs with hov
  · exact mul_le_mul_of_nonneg_left (le_of_lt hov) (le_of_lt hb0)
  · have hna : (0 : ℝ) ≤ (n : ℝ) * a :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt ha)
    linarith

private theorem upper_step {n : ℕ} {a b goal : ℝ} (hb1 : b < 1)
    (x : Fin n → ℝ) (hpos : 0 ≤ total x)
    (h : total x ≤ goal + (n : ℝ) * a) :
    total (aimdStep a b goal x) ≤ goal + (n : ℝ) * a := by
  rw [total_aimdStep]
  split_ifs with hov
  · have hb1' : b * total x ≤ 1 * total x :=
      mul_le_mul_of_nonneg_right (le_of_lt hb1) hpos
    linarith
  · have hle : total x ≤ goal := le_of_not_gt hov
    linarith

/-- Eventual confinement of the AIMD total load: a derived precise form
of the oscillation-around-the-goal claim (Chiu--Jain abstract and
Section 2), not a verbatim theorem of the paper. The total eventually
stays in `[b * goal, goal + n * a]`. -/
theorem aimd_eventual_confined {n : ℕ} (hn : 0 < n) {a b goal : ℝ}
    (ha : 0 < a) (hb0 : 0 < b) (hb1 : b < 1) (hg : 0 < goal)
    (x0 : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x0 i) (hxt : 0 < total x0) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      b * goal ≤ total ((aimdStep a b goal)^[t] x0) ∧
      total ((aimdStep a b goal)^[t] x0) ≤ goal + (n : ℝ) * a := by
  have _hx0 := hx0
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hc : (0 : ℝ) < (n : ℝ) * a := mul_pos hnR ha
  have hna : (0 : ℝ) ≤ (n : ℝ) * a := le_of_lt hc
  have hgoal_le : goal ≤ goal + (n : ℝ) * a := le_add_of_nonneg_right hna
  have hbgoal : b * goal < goal := by
    have h := mul_lt_mul_of_pos_right hb1 hg
    simpa using h
  obtain ⟨k, hk⟩ := exists_nat_gt ((b * goal - total x0) / ((n : ℝ) * a))
  have hk' : b * goal ≤ total x0 + (k : ℝ) * ((n : ℝ) * a) := by
    have h1 : (b * goal - total x0) / ((n : ℝ) * a) < (k : ℝ) := hk
    have h2 : (b * goal - total x0) < (k : ℝ) * ((n : ℝ) * a) :=
      (div_lt_iff₀ hc).mp h1
    linarith
  have hex_low : ∃ T, b * goal ≤ total ((aimdStep a b goal)^[T] x0) := by
    by_cases hex : ∃ j, j < k ∧ b * goal ≤ total ((aimdStep a b goal)^[j] x0)
    · obtain ⟨j, _, hj⟩ := hex
      exact ⟨j, hj⟩
    · push Not at hex
      have hall : ∀ j, j < k → total ((aimdStep a b goal)^[0 + j] x0) ≤ goal := by
        intro j hj
        have hlt := hex j hj
        have e : (0 : ℕ) + j = j := Nat.zero_add j
        rw [e]
        exact le_of_lt (lt_trans hlt hbgoal)
      have hrun := total_increase_run (x0 := x0) (N := 0) (k := k) hall
      simp only [Nat.zero_add, Function.iterate_zero_apply] at hrun
      rw [← hrun] at hk'
      exact ⟨k, hk'⟩
  have hxdiv : (0 : ℝ) < goal / total x0 := div_pos hg hxt
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one hxdiv hb1
  have ht' : b ^ t * total x0 ≤ goal := by
    have hlt : b ^ t * total x0 < goal := (lt_div_iff₀ hxt).mp ht
    exact le_of_lt hlt
  have hex_up : ∃ T, total ((aimdStep a b goal)^[T] x0) ≤ goal + (n : ℝ) * a := by
    by_cases hex : ∃ j, j < t ∧ total ((aimdStep a b goal)^[j] x0) ≤ goal
    · obtain ⟨j, _, hj⟩ := hex
      exact ⟨j, le_trans hj hgoal_le⟩
    · push Not at hex
      have hall : ∀ j, j < t → goal < total ((aimdStep a b goal)^[0 + j] x0) := by
        intro j hj
        have hgt := hex j hj
        have e : (0 : ℕ) + j = j := Nat.zero_add j
        rw [e]
        exact hgt
      have hrun := total_decrease_run (x0 := x0) (N := 0) (k := t) hall
      simp only [Nat.zero_add, Function.iterate_zero_apply] at hrun
      rw [← hrun] at ht'
      exact ⟨t, le_trans ht' hgoal_le⟩
  obtain ⟨T1, hT1⟩ := hex_low
  obtain ⟨T2, hT2⟩ := hex_up
  have hlow : ∀ t, T1 ≤ t → b * goal ≤ total ((aimdStep a b goal)^[t] x0) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hT1
    | succ t ht ih =>
      have hstep : (aimdStep a b goal)^[t + 1] x0
          = aimdStep a b goal ((aimdStep a b goal)^[t] x0) := by
        rw [Function.iterate_succ_apply']
      rw [hstep]
      exact lower_step ha hb0 _ ih
  have hup : ∀ t, T2 ≤ t → total ((aimdStep a b goal)^[t] x0) ≤ goal + (n : ℝ) * a := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hT2
    | succ t ht ih =>
      have hstep : (aimdStep a b goal)^[t + 1] x0
          = aimdStep a b goal ((aimdStep a b goal)^[t] x0) := by
        rw [Function.iterate_succ_apply']
      rw [hstep]
      have hpos : 0 ≤ total ((aimdStep a b goal)^[t] x0) :=
        le_of_lt (aimd_orbit_total_pos ha hb0 x0 hxt t)
      exact upper_step hb1 _ hpos ih
  exact ⟨max T1 T2, fun t ht => ⟨hlow t (le_trans (Nat.le_max_left _ _) ht),
    hup t (le_trans (Nat.le_max_right _ _) ht)⟩⟩

/-- Overload steps recur infinitely often along the AIMD orbit (derived
precise oscillation claim; see `aimd_eventual_confined`). -/
theorem aimd_overload_frequently {n : ℕ} (hn : 0 < n) {a b goal : ℝ}
    (ha : 0 < a) (hb0 : 0 < b) (hb1 : b < 1) (hg : 0 < goal)
    (x0 : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x0 i) (hxt : 0 < total x0) :
    ∃ᶠ t in atTop, goal < total ((aimdStep a b goal)^[t] x0) := by
  have _hx0 := hx0
  have _hb0 := hb0
  have _hb1 := hb1
  have _hg := hg
  have _hxt := hxt
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hc : (0 : ℝ) < (n : ℝ) * a := mul_pos hnR ha
  rw [frequently_atTop]
  intro N
  obtain ⟨k, hk⟩ := exists_nat_gt
    ((goal - total ((aimdStep a b goal)^[N] x0)) / ((n : ℝ) * a))
  have hk' : goal < total ((aimdStep a b goal)^[N] x0) + (k : ℝ) * ((n : ℝ) * a) := by
    have h1 : (goal - total ((aimdStep a b goal)^[N] x0)) / ((n : ℝ) * a) < (k : ℝ) :=
      hk
    have h2 : (goal - total ((aimdStep a b goal)^[N] x0))
        < (k : ℝ) * ((n : ℝ) * a) := (div_lt_iff₀ hc).mp h1
    linarith
  by_cases hex : ∃ j, j < k ∧ goal < total ((aimdStep a b goal)^[N + j] x0)
  · obtain ⟨j, _, hj⟩ := hex
    exact ⟨N + j, Nat.le_add_right N j, hj⟩
  · push Not at hex
    have hall : ∀ j, j < k → total ((aimdStep a b goal)^[N + j] x0) ≤ goal := by
      intro j hj
      exact hex j hj
    have hrun := total_increase_run (x0 := x0) (N := N) (k := k) hall
    rw [← hrun] at hk'
    exact ⟨N + k, Nat.le_add_right N k, hk'⟩

/-- Non-overload steps also recur infinitely often along the AIMD orbit,
so the system keeps crossing the goal in both directions and the load
vector need not converge to a fixed point. -/
theorem aimd_nonoverload_frequently {n : ℕ} (hn : 0 < n) {a b goal : ℝ}
    (ha : 0 < a) (hb0 : 0 < b) (hb1 : b < 1) (hg : 0 < goal)
    (x0 : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x0 i) (hxt : 0 < total x0) :
    ∃ᶠ t in atTop, total ((aimdStep a b goal)^[t] x0) ≤ goal := by
  have _hx0 := hx0
  have _hn := hn
  have _ha := ha
  rw [frequently_atTop]
  intro N
  have hNpos : 0 < total ((aimdStep a b goal)^[N] x0) :=
    aimd_orbit_total_pos ha hb0 x0 hxt N
  have hxdiv : (0 : ℝ) < goal / total ((aimdStep a b goal)^[N] x0) :=
    div_pos hg hNpos
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hxdiv hb1
  have hk' : b ^ k * total ((aimdStep a b goal)^[N] x0) ≤ goal := by
    have hlt : b ^ k * total ((aimdStep a b goal)^[N] x0) < goal :=
      (lt_div_iff₀ hNpos).mp hk
    exact le_of_lt hlt
  by_cases hex : ∃ j, j < k ∧ total ((aimdStep a b goal)^[N + j] x0) ≤ goal
  · obtain ⟨j, _, hj⟩ := hex
    exact ⟨N + j, Nat.le_add_right N j, hj⟩
  · push Not at hex
    have hall : ∀ j, j < k → goal < total ((aimdStep a b goal)^[N + j] x0) := by
      intro j hj
      exact hex j hj
    have hrun := total_decrease_run (x0 := x0) (N := N) (k := k) hall
    rw [← hrun] at hk'
    exact ⟨N + k, Nat.le_add_right N k, hk'⟩

private theorem diff_step {n : ℕ} (a b goal : ℝ) (x : Fin n → ℝ) (i j : Fin n) :
    (aimdStep a b goal x) i - (aimdStep a b goal x) j
      = if goal < total x then b * (x i - x j) else (x i - x j) := by
  unfold aimdStep
  split_ifs with h
  · simp only []
    ring
  · simp only []
    ring

private theorem diff_tendsto {n : ℕ} {a b goal : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hb0 : 0 < b) (hb1 : b < 1) (hg : 0 < goal)
    (x0 : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x0 i) (hxt : 0 < total x0)
    (i j : Fin n) :
    Tendsto (fun t : ℕ => ((aimdStep a b goal)^[t] x0) i - ((aimdStep a b goal)^[t] x0) j)
      atTop (𝓝 0) := by
  have hoverload := aimd_overload_frequently hn ha hb0 hb1 hg x0 hx0 hxt
  obtain ⟨φ, hmono, hφ⟩ := extraction_of_frequently_atTop hoverload
  have hstep_le : ∀ t : ℕ,
      abs (((aimdStep a b goal)^[t + 1] x0) i - ((aimdStep a b goal)^[t + 1] x0) j)
        ≤ abs (((aimdStep a b goal)^[t] x0) i - ((aimdStep a b goal)^[t] x0) j) := by
    intro t
    have hiter : (aimdStep a b goal)^[t + 1] x0
        = aimdStep a b goal ((aimdStep a b goal)^[t] x0) := by
      rw [Function.iterate_succ_apply']
    have hdiff := diff_step a b goal ((aimdStep a b goal)^[t] x0) i j
    rw [hiter]
    rw [hdiff]
    split_ifs with h
    · rw [abs_mul, abs_of_pos hb0]
      have hb1' : b * abs (((aimdStep a b goal)^[t] x0) i - ((aimdStep a b goal)^[t] x0) j)
          ≤ 1 * abs (((aimdStep a b goal)^[t] x0) i - ((aimdStep a b goal)^[t] x0) j) :=
        mul_le_mul_of_nonneg_right (le_of_lt hb1) (abs_nonneg _)
      simpa using hb1'
    · rfl
  have hanti : ∀ p q : ℕ, p ≤ q →
      abs (((aimdStep a b goal)^[q] x0) i - ((aimdStep a b goal)^[q] x0) j)
        ≤ abs (((aimdStep a b goal)^[p] x0) i - ((aimdStep a b goal)^[p] x0) j) := by
    intro p q hpq
    induction q, hpq using Nat.le_induction with
    | base => exact le_rfl
    | succ q hq ih =>
      exact le_trans (hstep_le q) ih
  have hsub : ∀ k : ℕ,
      abs (((aimdStep a b goal)^[φ k] x0) i - ((aimdStep a b goal)^[φ k] x0) j)
        ≤ b ^ k * abs (x0 i - x0 j) := by
    intro k
    induction k with
    | zero =>
      have h0 : (0 : ℕ) ≤ φ 0 := Nat.zero_le _
      have hle := hanti 0 (φ 0) h0
      simp only [Function.iterate_zero_apply] at hle
      simpa using hle
    | succ k ih =>
      have hlt : φ k < φ (k + 1) := hmono (Nat.lt_succ_self k)
      have hle1 : abs (((aimdStep a b goal)^[φ (k + 1)] x0) i - ((aimdStep a b goal)^[φ (k + 1)] x0) j)
          ≤ abs (((aimdStep a b goal)^[φ k + 1] x0) i - ((aimdStep a b goal)^[φ k + 1] x0) j) := by
        apply hanti
        exact Nat.succ_le_of_lt hlt
      have hiter : (aimdStep a b goal)^[φ k + 1] x0
          = aimdStep a b goal ((aimdStep a b goal)^[φ k] x0) := by
        rw [Function.iterate_succ_apply']
      have hdiff := diff_step a b goal ((aimdStep a b goal)^[φ k] x0) i j
      have hov : goal < total ((aimdStep a b goal)^[φ k] x0) := hφ k
      have heq : (((aimdStep a b goal)^[φ k + 1] x0) i - ((aimdStep a b goal)^[φ k + 1] x0) j)
          = b * ((((aimdStep a b goal)^[φ k] x0) i - ((aimdStep a b goal)^[φ k] x0) j)) := by
        rw [hiter, hdiff, ite_eq_left hov]
      rw [heq] at hle1
      rw [abs_mul, abs_of_pos hb0] at hle1
      have hb_nonneg : (0 : ℝ) ≤ b := le_of_lt hb0
      calc abs (((aimdStep a b goal)^[φ (k + 1)] x0) i - ((aimdStep a b goal)^[φ (k + 1)] x0) j)
          ≤ b * abs (((aimdStep a b goal)^[φ k] x0) i - ((aimdStep a b goal)^[φ k] x0) j) := hle1
        _ ≤ b * (b ^ k * abs (x0 i - x0 j)) :=
          mul_le_mul_of_nonneg_left ih hb_nonneg
        _ = b ^ (k + 1) * abs (x0 i - x0 j) := by ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h0abs : (0 : ℝ) ≤ abs (x0 i - x0 j) := abs_nonneg _
  obtain ⟨K, hK⟩ : ∃ K : ℕ, b ^ K * abs (x0 i - x0 j) < ε := by
    by_cases hzero : abs (x0 i - x0 j) = 0
    · exact ⟨0, by simp [hzero, hε]⟩
    · have hpos : (0 : ℝ) < abs (x0 i - x0 j) :=
        lt_of_le_of_ne h0abs (Ne.symm hzero)
      obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (div_pos hε hpos) hb1
      exact ⟨K, (lt_div_iff₀ hpos).mp hK⟩
  exact ⟨φ K, fun t ht => by
    have hle : abs (((aimdStep a b goal)^[t] x0) i - ((aimdStep a b goal)^[t] x0) j)
        ≤ b ^ K * abs (x0 i - x0 j) :=
      le_trans (hanti (φ K) t ht) (hsub K)
    have hlt : abs (((aimdStep a b goal)^[t] x0) i - ((aimdStep a b goal)^[t] x0) j) < ε :=
      lt_of_le_of_lt hle hK
    simpa [Real.dist_eq] using hlt⟩

private theorem double_sum_identity {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, ∑ j, (x i - x j) ^ 2)
      = 2 * ((n : ℝ) * (∑ i, (x i) ^ 2) - (∑ i, x i) ^ 2) := by
  have hexp : ∀ i j : Fin n, (x i - x j) ^ 2
      = (x i) ^ 2 + (x j) ^ 2 - 2 * x i * x j := by
    intro i j
    ring
  simp_rw [hexp]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA : (∑ i : Fin n, ∑ j : Fin n, (x i) ^ 2)
      = (n : ℝ) * (∑ i, (x i) ^ 2) := by
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hB : (∑ i : Fin n, ∑ j : Fin n, (x j) ^ 2)
      = (n : ℝ) * (∑ i, (x i) ^ 2) := by
    rw [Finset.sum_comm]
    exact hA
  have hC : (∑ i : Fin n, ∑ j : Fin n, 2 * x i * x j)
      = 2 * (∑ i, x i) ^ 2 := by
    have hfactor : ∀ i : Fin n, (∑ j : Fin n, 2 * x i * x j)
        = 2 * x i * (∑ j, x j) := by
      intro i
      exact (Finset.mul_sum _ _ _).symm
    simp_rw [hfactor]
    have h2 : (∑ i : Fin n, 2 * x i * (∑ j, x j))
        = 2 * (∑ i, x i) * (∑ j, x j) := by
      have e : ∀ i : Fin n, (2 : ℝ) * x i * (∑ j, x j)
          = (2 * (∑ j, x j)) * x i := by
        intro i
        ring
      simp_rw [e]
      have hmul : (∑ i : Fin n, (2 * (∑ j, x j)) * x i)
          = (2 * (∑ j, x j)) * (∑ i, x i) :=
        (Finset.mul_sum _ _ _).symm
      calc (∑ i : Fin n, (2 * (∑ j, x j)) * x i)
          = (2 * (∑ j, x j)) * (∑ i, x i) := hmul
        _ = 2 * (∑ i, x i) * (∑ j, x j) := by ring
    rw [h2]
    ring
  rw [hA, hB, hC]
  ring

/-- AIMD convergence to fairness: the fairness index tends to `1` from
any nonnegative start with positive total (Chiu--Jain abstract:
"convergence to an efficient and fair state regardless of the starting
state", restricted here to the positive-total scope; Section 2.3 defines
convergence to fairness as `F(x(t)) → 1`). -/
theorem aimd_fairness_tendsto_one {n : ℕ} (hn : 0 < n) {a b goal : ℝ}
    (ha : 0 < a) (hb0 : 0 < b) (hb1 : b < 1) (hg : 0 < goal)
    (x0 : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x0 i) (hxt : 0 < total x0) :
    Tendsto (fun t : ℕ => fairness ((aimdStep a b goal)^[t] x0)) atTop (𝓝 1) := by
  have hdiff : ∀ i j : Fin n, Tendsto
      (fun t : ℕ => ((aimdStep a b goal)^[t] x0) i - ((aimdStep a b goal)^[t] x0) j)
      atTop (𝓝 0) :=
    fun i j => diff_tendsto hn ha hb0 hb1 hg x0 hx0 hxt i j
  have hsq : ∀ i j : Fin n, Tendsto
      (fun t : ℕ => (((aimdStep a b goal)^[t] x0) i - ((aimdStep a b goal)^[t] x0) j) ^ 2)
      atTop (𝓝 0) := by
    intro i j
    simpa using (hdiff i j).pow 2
  have hinner : ∀ i : Fin n, Tendsto
      (fun t : ℕ => ∑ j, (((aimdStep a b goal)^[t] x0) i - ((aimdStep a b goal)^[t] x0) j) ^ 2)
      atTop (𝓝 0) := by
    intro i
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun j _ => hsq i j)
    simpa using h
  have hdouble : Tendsto
      (fun t : ℕ => ∑ i, ∑ j, (((aimdStep a b goal)^[t] x0) i - ((aimdStep a b goal)^[t] x0) j) ^ 2)
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ => hinner i)
    simpa using h
  have hD : Tendsto
      (fun t : ℕ => (n : ℝ) * (∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2)
        - (∑ i, ((aimdStep a b goal)^[t] x0) i) ^ 2)
      atTop (𝓝 0) := by
    have hdiv := hdouble.div_const 2
    simp only [zero_div] at hdiv
    have heq : (fun t : ℕ => (n : ℝ) * (∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2)
          - (∑ i, ((aimdStep a b goal)^[t] x0) i) ^ 2)
        = (fun t : ℕ => (∑ i, ∑ j,
          (((aimdStep a b goal)^[t] x0) i - ((aimdStep a b goal)^[t] x0) j) ^ 2) / 2) := by
      funext t
      have hid := double_sum_identity ((aimdStep a b goal)^[t] x0)
      linarith
    rw [heq]
    exact hdiv
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hbg : (0 : ℝ) < b * goal := mul_pos hb0 hg
  have hc : (0 : ℝ) < (b * goal) ^ 2 := sq_pos_of_ne_zero (ne_of_gt hbg)
  obtain ⟨T, hT⟩ := aimd_eventual_confined hn ha hb0 hb1 hg x0 hx0 hxt
  have hden_ge : ∀ᶠ t in atTop, (b * goal) ^ 2 ≤ (n : ℝ) * ∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2 := by
    rw [eventually_atTop]
    exact ⟨T, fun t ht => by
      have hlow := (hT t ht).1
      have hsq_le : ((∑ i, ((aimdStep a b goal)^[t] x0) i)) ^ 2
          ≤ (n : ℝ) * ∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2 := by
        have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := (aimdStep a b goal)^[t] x0)
        simp only [Finset.card_univ, Fintype.card_fin] at h
        simpa using h
      have hpow : (b * goal) ^ 2 ≤ ((∑ i, ((aimdStep a b goal)^[t] x0) i)) ^ 2 := by
        have hSt : total ((aimdStep a b goal)^[t] x0) = ∑ i, ((aimdStep a b goal)^[t] x0) i := rfl
        rw [← hSt]
        exact pow_le_pow_left₀ (le_of_lt hbg) hlow 2
      linarith⟩
  have hDnonneg : ∀ t : ℕ, 0 ≤ (n : ℝ) * (∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2)
      - (∑ i, ((aimdStep a b goal)^[t] x0) i) ^ 2 := by
    intro t
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := (aimdStep a b goal)^[t] x0)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    have h' : (∑ i, ((aimdStep a b goal)^[t] x0) i) ^ 2
        ≤ (n : ℝ) * ∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2 := by
      simpa using h
    linarith
  have hQpos : ∀ t : ℕ, 0 < (n : ℝ) * ∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2 := by
    intro t
    have hx : ∀ i, 0 ≤ ((aimdStep a b goal)^[t] x0) i :=
      fun i => aimd_orbit_nonneg ha hb0 x0 hx0 t i
    have ht : 0 < total ((aimdStep a b goal)^[t] x0) :=
      aimd_orbit_total_pos ha hb0 x0 hxt t
    exact mul_pos hnR (sq_sum_pos _ hx ht)
  have hRatio : Tendsto
      (fun t : ℕ => ((n : ℝ) * (∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2)
        - (∑ i, ((aimdStep a b goal)^[t] x0) i) ^ 2)
        / ((n : ℝ) * ∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2))
      atTop (𝓝 0) := by
    have hdiv := hD.div_const ((b * goal) ^ 2)
    simp only [zero_div] at hdiv
    apply squeeze_zero' _ _ hdiv
    · apply Eventually.of_forall
      intro t
      exact div_nonneg (hDnonneg t) (le_of_lt (hQpos t))
    · apply hden_ge.mono
      intro t ht
      exact div_le_div_of_nonneg_left (hDnonneg t) hc ht
  have heq : (fun t : ℕ => 1 - fairness ((aimdStep a b goal)^[t] x0))
      = (fun t : ℕ => ((n : ℝ) * (∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2)
        - (∑ i, ((aimdStep a b goal)^[t] x0) i) ^ 2)
        / ((n : ℝ) * ∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2)) := by
    funext t
    unfold fairness
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hx : ∀ i, 0 ≤ ((aimdStep a b goal)^[t] x0) i :=
      fun i => aimd_orbit_nonneg ha hb0 x0 hx0 t i
    have ht : 0 < total ((aimdStep a b goal)^[t] x0) :=
      aimd_orbit_total_pos ha hb0 x0 hxt t
    have hQ : (0 : ℝ) < ∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2 :=
      sq_sum_pos _ hx ht
    have hQ_ne : (∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2) ≠ 0 := ne_of_gt hQ
    have hne : (n : ℝ) * ∑ i, (((aimdStep a b goal)^[t] x0) i) ^ 2 ≠ 0 :=
      ne_of_gt (hQpos t)
    field_simp
  have h1 : Tendsto (fun t : ℕ => 1 - fairness ((aimdStep a b goal)^[t] x0)) atTop (𝓝 0) := by
    rw [heq]
    exact hRatio
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsub := Filter.Tendsto.sub hconst h1
  simp only [sub_zero] at hsub
  have heq2 : (fun t : ℕ => (1 : ℝ) - (1 - fairness ((aimdStep a b goal)^[t] x0)))
      = (fun t : ℕ => fairness ((aimdStep a b goal)^[t] x0)) := by
    funext t
    ring
  rw [heq2] at hsub
  exact hsub

/-- AIAD boundary witness, first step: with two users, goal `4`,
additive increase `1` and additive decrease `-1`, the load vector
`(1, 2)` (total `3 ≤ 4`) increases to `(2, 3)`. -/
theorem aiad_cycle_step_one :
    aiadStep (1 : ℝ) (-1) 4 ![1, 2] = ![2, 3] := by
  have htot : total (![1, 2] : Fin 2 → ℝ) = 3 := by
    unfold total
    norm_num [Fin.sum_univ_two]
  have hcond : ¬ (4 : ℝ) < total (![1, 2] : Fin 2 → ℝ) := by
    rw [htot]
    norm_num
  unfold aiadStep
  simp [hcond]
  funext i
  fin_cases i <;> simp <;> norm_num

/-- AIAD boundary witness, second step: the load vector `(2, 3)`
(total `5 > 4`) decreases back to `(1, 2)`. -/
theorem aiad_cycle_step_two :
    aiadStep (1 : ℝ) (-1) 4 ![2, 3] = ![1, 2] := by
  have htot : total (![2, 3] : Fin 2 → ℝ) = 5 := by
    unfold total
    norm_num [Fin.sum_univ_two]
  have hcond : (4 : ℝ) < total (![2, 3] : Fin 2 → ℝ) := by
    rw [htot]
    norm_num
  unfold aiadStep
  simp [hcond]
  funext i
  fin_cases i <;> simp <;> norm_num

/-- Fairness values on the AIAD two-cycle: `F(1, 2) = 9/10` and
`F(2, 3) = 25/26`. In particular AIAD does not preserve the fairness
index in general (contrast Chiu--Jain Figure 6: AIAD converges to
efficiency but not to fairness). -/
theorem aiad_cycle_fairness :
    fairness ![1, 2] = 9 / 10 ∧ fairness ![2, 3] = 25 / 26 := by
  constructor
  · unfold fairness
    norm_num [Fin.sum_univ_two]
  · unfold fairness
    norm_num [Fin.sum_univ_two]

private theorem aiad_even (k : ℕ) :
    ((aiadStep (1 : ℝ) (-1) 4)^[2 * k] ![1, 2]) = ![1, 2] := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : ((aiadStep (1 : ℝ) (-1) 4)^[2] ![1, 2]) = ![1, 2] := by
      have e1 := aiad_cycle_step_one
      have e2 := aiad_cycle_step_two
      have hcomp : ((aiadStep (1 : ℝ) (-1) 4)^[2] ![1, 2])
        = aiadStep (1 : ℝ) (-1) 4 (aiadStep (1 : ℝ) (-1) 4 ![1, 2]) := by
        simp [Function.iterate_succ_apply']
      rw [hcomp, e1, e2]
    have hadd : 2 * (k + 1) = 2 + 2 * k := by ring
    rw [hadd, Function.iterate_add_apply, ih, h2]

/-- The AIAD two-cycle is an unfair non-convergent orbit: its fairness
does not tend to `1`. -/
theorem aiad_cycle_not_tendsto_one :
    ¬ Tendsto (fun t : ℕ => fairness ((aiadStep (1 : ℝ) (-1) 4)^[t] ![1, 2]))
      atTop (𝓝 1) := by
  intro h
  have h2k : Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
    apply tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by norm_num : 0 < 2))
    exact tendsto_id
  have hcomp := h.comp h2k
  simp only [Function.comp_def] at hcomp
  have heq : (fun k : ℕ => fairness ((aiadStep (1 : ℝ) (-1) 4)^[2 * k] ![1, 2]))
      = fun _ => (9 / 10 : ℝ) := by
    funext k
    rw [aiad_even k, aiad_cycle_fairness.1]
  rw [heq] at hcomp
  have hconst : Tendsto (fun _ : ℕ => (9 / 10 : ℝ)) atTop (𝓝 (9 / 10)) :=
    tendsto_const_nhds
  have hun := tendsto_nhds_unique hcomp hconst
  norm_num at hun

end Cslib.Algorithms.Networking.Aimd
