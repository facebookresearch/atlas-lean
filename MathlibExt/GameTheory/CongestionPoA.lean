/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic

import Mathlib.Tactic

@[expose] public section

/-! # Price of anarchy in singleton congestion games

For singleton atomic congestion games with affine delays with
nonnegative coefficients, every pure Nash equilibrium has social
cost at most `5 / 2` times the optimum, by the `(5/3, 1/3)`
smoothness argument. This file covers roadmap package DPA-38 of the
Atlas TCS canon roadmap.

Source: Roughgarden, "Intrinsic robustness of the price of anarchy",
Journal of the ACM 62 (2015); Christodoulou and Koutsoupias (2005).
-/

open Finset

namespace MathlibExt.GameTheory.CongestionGame

/-- The load of resource `r` under a strategy profile `s` of a
singleton atomic congestion game: how many players chose `r`. -/
def loadOf {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (s : Fin n → R) (r : R) : ℕ :=
  (Finset.univ.filter fun i => s i = r).card

/-- Social cost with affine delays `d r k = a r * k + b r`: the sum
of all players' costs, where a player choosing `r` pays the delay at
the load including themselves. -/
noncomputable def socialCost {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (a b : R → ℝ) (s : Fin n → R) : ℝ :=
  ∑ i, (a (s i) * (loadOf s (s i) : ℝ) + b (s i))

/-- Smoothness core over the reals when the optimal load is at least 2. -/
private lemma key_ineq_aux (x y : ℝ) (hy : 2 ≤ y) :
    y * (x + 1) ≤ (5 / 3) * y ^ 2 + (1 / 3) * x ^ 2 := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  nlinarith [sq_nonneg (x - 3 * y / 2),
    mul_nonneg (show (0 : ℝ) ≤ y - 2 from by linarith) hy0]

/-- The `y = 1` case of the smoothness core; needs integrality of `x`. -/
private lemma key_ineq_one (x : ℕ) :
    (1 : ℝ) * ((x : ℝ) + 1) ≤ (5 / 3) * (1 : ℝ) ^ 2 + (1 / 3) * (x : ℝ) ^ 2 := by
  by_cases hx0 : x = 0
  · subst hx0
    norm_num
  by_cases hx1 : x = 1
  · subst hx1
    norm_num
  · have hx2 : 2 ≤ x := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hx2
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    nlinarith [sq_nonneg ((k : ℝ)), hk]

/-- Smoothness core for natural loads. This needs integrality
(it fails for `x = 3/2, y = 1` over the reals), so split on
`y = 0`, `y = 1`, and `y ≥ 2`. -/
private lemma key_ineq (x y : ℕ) :
    (y : ℝ) * ((x : ℝ) + 1) ≤ (5 / 3) * (y : ℝ) ^ 2 + (1 / 3) * (x : ℝ) ^ 2 := by
  by_cases hy0 : y = 0
  · subst hy0
    simp only [Nat.cast_zero, zero_mul]
    positivity
  by_cases hy1 : y = 1
  · subst hy1
    rw [Nat.cast_one]
    exact key_ineq_one x
  · have hy2 : 2 ≤ y := by omega
    have hy2' : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
    exact key_ineq_aux _ _ hy2'

/-- Per-resource smoothness inequality with affine coefficients. -/
private lemma smooth_per_resource {A B x y : ℝ}
    (ha : 0 ≤ A) (hb : 0 ≤ B) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (key : y * (x + 1) ≤ (5 / 3) * y ^ 2 + (1 / 3) * x ^ 2) :
    y * (A * (x + 1) + B)
      ≤ (5 / 3) * (y * (A * y + B)) + (1 / 3) * (x * (A * x + B)) := by
  have hK : (0 : ℝ) ≤ (5 / 3) * y ^ 2 + (1 / 3) * x ^ 2 - y * (x + 1) :=
    sub_nonneg.mpr key
  nlinarith [mul_nonneg ha hK, mul_nonneg hb hy, mul_nonneg hb hx]

/-- Reindex a sum over players by the resource they choose. -/
private lemma sum_eq_sum_fiber_mul {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (s : Fin n → R) (g : R → ℝ) :
    ∑ i, g (s i) = ∑ r, (loadOf s r : ℝ) * g r := by
  have hfib := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset R)) (g := s) (fun i _ => Finset.mem_univ (s i))
    (fun i => g (s i))
  unfold loadOf
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro r _
  have hcongr : ∀ i ∈ Finset.univ.filter (fun i => s i = r), g (s i) = g r := by
    intro i hi
    have h : s i = r := (Finset.mem_filter.mp hi).2
    rw [h]
  refine Eq.trans (Finset.sum_congr rfl hcongr) ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- Social cost as a sum over resources. -/
private lemma socialCost_eq_sum_load {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (a b : R → ℝ) (s : Fin n → R) :
    socialCost a b s = ∑ r, (loadOf s r : ℝ) * (a r * (loadOf s r : ℝ) + b r) := by
  unfold socialCost
  exact sum_eq_sum_fiber_mul s (fun r => a r * (loadOf s r : ℝ) + b r)

/-- Deviating to `r` adds at most one user to `r`. -/
private lemma loadOf_update_le {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (s : Fin n → R) (i : Fin n) (r : R) :
    loadOf (Function.update s i r) r ≤ loadOf s r + 1 := by
  unfold loadOf
  have hsub : Finset.univ.filter (fun j => Function.update s i r j = r)
      ⊆ Finset.univ.filter (fun j => s j = r) ∪ {i} := by
    intro j hj
    have hj' : Function.update s i r j = r := (Finset.mem_filter.mp hj).2
    by_cases hji : j = i
    · rw [hji]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self i))
    · have hjs : s j = r := by
        rw [Function.update_of_ne hji] at hj'
        exact hj'
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjs⟩))
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [Finset.card_singleton]

/-- Price of anarchy `5 / 2` for singleton atomic congestion games
with affine delays and nonnegative coefficients: every pure Nash
equilibrium (no player can lower their own cost by unilaterally
switching resources) has social cost at most `5 / 2` times the
optimal social cost.

The hypothesis is stated only for deviations to the comparison
profile `opt`: for each player, deviating to `opt i` does not lower
their cost. This is weaker than full Nash equilibrium (which quantifies
over every deviation), and the proof only uses these deviations, so
no player-specific feasible-set restriction is needed. -/
theorem congestion_poa {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (a b : R → ℝ) (ha : ∀ r, 0 ≤ a r) (hb : ∀ r, 0 ≤ b r)
    (s opt : Fin n → R)
    (hNash : ∀ (i : Fin n),
      a (s i) * (loadOf s (s i) : ℝ) + b (s i) ≤
        a (opt i) * ((loadOf (Function.update s i (opt i)) (opt i) : ℝ))
          + b (opt i)) :
    socialCost a b s ≤ (5 / 2) * socialCost a b opt := by
  have hSCs : socialCost a b s
      = ∑ r, (loadOf s r : ℝ) * (a r * (loadOf s r : ℝ) + b r) :=
    socialCost_eq_sum_load a b s
  have hSCo : socialCost a b opt
      = ∑ r, (loadOf opt r : ℝ) * (a r * (loadOf opt r : ℝ) + b r) :=
    socialCost_eq_sum_load a b opt
  have hNashSum : socialCost a b s
      ≤ ∑ r, (loadOf opt r : ℝ) * (a r * ((loadOf s r : ℝ) + 1) + b r) := by
    have hper : ∀ i : Fin n, a (s i) * (loadOf s (s i) : ℝ) + b (s i)
        ≤ a (opt i) * ((loadOf s (opt i) : ℝ) + 1) + b (opt i) := by
      intro i
      have hn := hNash i
      have hdev : (loadOf (Function.update s i (opt i)) (opt i) : ℝ)
          ≤ (loadOf s (opt i) : ℝ) + 1 := by
        have h := loadOf_update_le s i (opt i)
        have h' : ((loadOf (Function.update s i (opt i)) (opt i) : ℕ) : ℝ)
            ≤ ((loadOf s (opt i) + 1 : ℕ) : ℝ) := by
          exact_mod_cast h
        rwa [Nat.cast_add, Nat.cast_one] at h'
      have hmul : a (opt i) * (loadOf (Function.update s i (opt i)) (opt i) : ℝ)
          ≤ a (opt i) * ((loadOf s (opt i) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hdev (ha (opt i))
      have hadd := add_le_add_left hmul (b (opt i))
      exact le_trans hn hadd
    have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hper i)
    have h2 := sum_eq_sum_fiber_mul opt
      (fun r => a r * ((loadOf s r : ℝ) + 1) + b r)
    unfold socialCost
    exact le_trans h1 (le_of_eq h2)
  have hsmooth : ∀ r : R, (loadOf opt r : ℝ) * (a r * ((loadOf s r : ℝ) + 1) + b r)
      ≤ (5 / 3) * ((loadOf opt r : ℝ) * (a r * (loadOf opt r : ℝ) + b r))
        + (1 / 3) * ((loadOf s r : ℝ) * (a r * (loadOf s r : ℝ) + b r)) := by
    intro r
    exact smooth_per_resource (ha r) (hb r) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (key_ineq (loadOf s r) (loadOf opt r))
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hsmooth r)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [← hSCo, ← hSCs] at hsum
  have hfin : socialCost a b s
      ≤ (5 / 3) * socialCost a b opt + (1 / 3) * socialCost a b s :=
    le_trans hNashSum hsum
  linarith [hfin]

end MathlibExt.GameTheory.CongestionGame
