/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.BurgersBounds
import MathlibExt.Analysis.PDE.BurgersUniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Set Filter Real
open scoped ContDiff Topology
open ColeHopf

-- The initial spatial derivative is not an assumption of uniqueness.
example {u : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 < ν)
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t, 0 < t → ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a : ℝ) : ∀ t ∈ Icc 0 T, ∀ x, u t x = burgersSolution ν (u 0) a t x :=
  eq_burgersSolution_onStrip hν hc hu hb hpde a

-- Exact constant velocity, including a nonzero sign and a nonunit viscosity.
example (c a T : ℝ) : ∀ t ∈ Icc 0 T, ∀ x,
    burgersSolution 3 (fun _ => c) a t x = c := by
  have h := eq_burgersSolution_onStrip (u := fun _ _ => c) (by norm_num : (0 : ℝ) < 3)
    continuousOn_const contDiffOn_const ⟨|c|, fun _ _ _ => le_rfl⟩
    (by intros; simp [iteratedDeriv_const]) a (T := T)
  exact fun t ht x => (h t ht x).symm

-- Identification covers the final time, with a bound only on this strip.
example {u : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 5, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t, 0 < t → ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = 3 * iteratedDeriv 2 (u t) x)
    (x : ℝ) : u 5 x = burgersSolution 3 (u 0) (-7) 5 x :=
  eq_burgersSolution_onStrip (by norm_num) hc hu hb hpde (-7) 5 (by constructor <;> norm_num) x

-- The empty strip is legitimate and does not demand an initial bound.
example (T : ℝ) (hT : T < 0) : ∀ t ∈ Icc 0 T, ∀ x,
    (0 : ℝ) = burgersSolution 1 (fun _ => 0) 0 t x := by
  apply eq_burgersSolution_onStrip (by norm_num) continuousOn_const contDiffOn_const
  · exact ⟨-1, fun t ht _ => (by linarith [ht.1, ht.2])⟩
  · intros
    simp

-- A zero-length strip gives the initial value, without needing any positive-time bound.
example (x : ℝ) : (2 : ℝ) = burgersSolution 3 (fun _ => 2) (-7) 0 x :=
  eq_burgersSolution_onStrip (u := fun _ _ => 2) (ν := 3)
    (by norm_num) continuousOn_const contDiffOn_const
    ⟨2, by intros; norm_num⟩ (by intros; simp [iteratedDeriv_const]) (-7) 0 ⟨le_rfl, le_rfl⟩ x

-- The candidate has nonsmooth initial data. No assumption differentiates it at zero.
example {u : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ))
    (hb : ∀ T, 0 ≤ T → ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t, 0 < t → ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = 3 * iteratedDeriv 2 (u t) x)
    (h0 : ∀ x, u 0 x = |sin x|) : ∀ t, 0 ≤ t → ∀ x,
      u t x = burgersSolution 3 (fun y => |sin y|) 7 t x := by
  have h := eq_burgersSolution (by norm_num) hc hu hb hpde 7
  simpa only [funext h0] using h

private noncomputable def corner (x : ℝ) : ℝ := |sin x|
private theorem corner_continuous : Continuous corner := continuous_sin.abs
private theorem corner_bound : ∀ x, |corner x| ≤ 1 := by
  intro x
  simpa [corner] using abs_sin_le_one x

-- Two actual nonconstant bounded solutions, with different normalization anchors.
-- This also checks the arbitrary small positive viscosity interface.
example (a b : ℝ) : ∀ t, 0 ≤ t → ∀ x,
    burgersSolution (1 / 100) corner a t x = burgersSolution (1 / 100) corner b t x := by
  apply burgers_eq (by norm_num : (0 : ℝ) < 1 / 100)
    (burgersSolution_continuous_of_bounded corner_continuous ⟨1, corner_bound⟩
      (by norm_num) a).continuousOn
    (burgersSolution_continuous_of_bounded corner_continuous ⟨1, corner_bound⟩
      (by norm_num) b).continuousOn
    (burgersSolution_contDiffOn_of_bounded corner_continuous ⟨1, corner_bound⟩ (by norm_num) a)
    (burgersSolution_contDiffOn_of_bounded corner_continuous ⟨1, corner_bound⟩ (by norm_num) b)
    (fun _ _ => ⟨1, fun t _ x =>
      abs_burgersSolution_le corner_continuous (by norm_num) corner_bound a t x⟩)
    (fun _ _ => ⟨1, fun t _ x =>
      abs_burgersSolution_le corner_continuous (by norm_num) corner_bound b t x⟩)
    (fun t ht x => burgersSolution_burgers_of_bounded corner_continuous ⟨1, corner_bound⟩
      (by norm_num) a t x ht)
    (fun t ht x => burgersSolution_burgers_of_bounded corner_continuous ⟨1, corner_bound⟩
      (by norm_num) b t x ht)
  intro x
  rw [burgersSolution_zero corner_continuous (by norm_num),
    burgersSolution_zero corner_continuous (by norm_num)]

-- Negative-time values need not agree and may be discontinuous at the boundary.
private noncomputable def past (c t : ℝ) (_x : ℝ) : ℝ := if 0 ≤ t then 2 else c

private theorem past_continuous (c : ℝ) :
    ContinuousOn (Function.uncurry (past c)) (Ici 0 ×ˢ univ) :=
  (continuousOn_const (c := (2 : ℝ))).congr (fun p hp => by
    simp [Function.uncurry_def, past, show 0 ≤ p.1 from hp.1])

private theorem past_smooth (c : ℝ) :
    ContDiffOn ℝ 2 (Function.uncurry (past c)) (Ioi 0 ×ˢ univ) :=
  (contDiffOn_const (c := (2 : ℝ))).congr (fun p hp => by
    simp [Function.uncurry_def, past, le_of_lt hp.1])

private theorem past_burgers (c ν t x : ℝ) (ht : 0 < t) :
    deriv (fun s => past c s x) t + past c t x * deriv (past c t) x =
      ν * iteratedDeriv 2 (past c t) x := by
  have he : (fun s => past c s x) =ᶠ[𝓝 t] (fun _ => (2 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp [past, hs.le]
  have hx : past c t = fun _ => (2 : ℝ) := funext (fun _ => by simp [past, ht.le])
  rw [he.deriv_eq, hx]
  simp [iteratedDeriv_const]

example : ∀ t, 0 ≤ t → ∀ x, past 17 t x = past (-11) t x := by
  apply burgers_eq (by norm_num : (0 : ℝ) < 3)
    (past_continuous 17) (past_continuous (-11)) (past_smooth 17) (past_smooth (-11))
    (fun _ _ => ⟨2, fun t ht _ => by simp [past, ht.1]⟩)
    (fun _ _ => ⟨2, fun t ht _ => by simp [past, ht.1]⟩)
    (fun t ht x => past_burgers 17 3 t x ht)
    (fun t ht x => past_burgers (-11) 3 t x ht)
  intro x
  simp [past]

example : past 17 (-1) 0 ≠ past (-11) (-1) 0 := by norm_num [past]

-- A jump at zero solves Burgers for positive times and is bounded, but fails
-- initial continuity. Uniqueness itself detects why that hypothesis is necessary.
private noncomputable def jump (t : ℝ) (_x : ℝ) : ℝ := if t ≤ 0 then 0 else 1

private theorem jump_smooth : ContDiffOn ℝ 2 (Function.uncurry jump) (Ioi 0 ×ˢ univ) :=
  (contDiffOn_const (c := (1 : ℝ))).congr (fun p hp => by
    simp [Function.uncurry_def, jump, not_le.mpr hp.1])

private theorem jump_burgers (ν t x : ℝ) (ht : 0 < t) :
    deriv (fun s => jump s x) t + jump t x * deriv (jump t) x =
      ν * iteratedDeriv 2 (jump t) x := by
  have he : (fun s => jump s x) =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp [jump, not_le.mpr hs]
  have hx : jump t = fun _ => (1 : ℝ) := funext (fun _ => by simp [jump, not_le.mpr ht])
  rw [he.deriv_eq, hx]
  simp [iteratedDeriv_const]

example : ¬ ContinuousOn (Function.uncurry jump) (Ici 0 ×ˢ univ) := by
  intro hc
  have h := burgers_eq_onStrip (u := jump) (v := fun _ _ => 0)
    (by norm_num : (0 : ℝ) < 3) hc continuousOn_const jump_smooth contDiffOn_const
    (T := 1) ⟨1, fun t _ _ => by unfold jump; split_ifs <;> norm_num⟩
    ⟨0, by intros; simp⟩ (fun t ht x => jump_burgers 3 t x ht)
    (by intros; simp) (by intro x; simp [jump])
  have hh := h 1 (by constructor <;> norm_num) 0
  norm_num [jump] at hh

example (ν t x : ℝ) (ht : 0 < t) :
    deriv (fun s => jump s x) t + jump t x * deriv (jump t) x =
      ν * iteratedDeriv 2 (jump t) x := jump_burgers ν t x ht

example (x : ℝ) : jump 0 x = 0 ∧ jump 1 x = 1 := by norm_num [jump]
