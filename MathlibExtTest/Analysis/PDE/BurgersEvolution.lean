/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.BurgersEvolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum

open Set Filter Real
open scoped ContDiff Topology
open ColeHopf

example {u₀ : ℝ → ℝ} (hu : Continuous u₀) (hb : ∃ M, ∀ x, |u₀ x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (a s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    burgersSolution ν (burgersSolution ν u₀ a s) a t = burgersSolution ν u₀ a (s + t) :=
  burgersSolution_semigroup hu hb hν a s t hs ht

-- The identity at zero duration survives a change of normalization anchor.
example {u₀ : ℝ → ℝ} (hu : Continuous u₀) (hb : ∃ M, ∀ x, |u₀ x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (a b t x : ℝ) (ht : 0 ≤ t) :
    burgersSolution ν (burgersSolution ν u₀ a 0) b t x = burgersSolution ν u₀ a t x := by
  simpa only [zero_add] using burgersSolution_restart hu hb hν a b 0 t x le_rfl ht

example {u₀ : ℝ → ℝ} (hu : Continuous u₀) (hb : ∃ M, ∀ x, |u₀ x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (a s : ℝ) (hs : 0 ≤ s) :
    burgersSolution ν (burgersSolution ν u₀ a s) a 0 = burgersSolution ν u₀ a s := by
  simpa only [add_zero] using burgersSolution_semigroup hu hb hν a s 0 hs le_rfl

example {u₀ : ℝ → ℝ} (hu : Continuous u₀) (hb : ∃ M, ∀ x, |u₀ x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (a b t : ℝ) (ht : 0 ≤ t) :
    burgersSolution ν u₀ a t = burgersSolution ν u₀ b t :=
  funext (fun x => burgersSolution_anchor_independent hu hb hν a b t x ht)

-- Bounded continuous but nonsmooth initial data, nonunit viscosity and distinct anchors.
private noncomputable def corner (x : ℝ) : ℝ := |sin x|
private theorem corner_continuous : Continuous corner := continuous_sin.abs
private theorem corner_bound : ∀ x, |corner x| ≤ 1 := by
  intro x
  simpa [corner] using abs_sin_le_one x

example (x : ℝ) :
    burgersSolution (1 / 100) (burgersSolution (1 / 100) corner 7 2) (-5) 3 x =
      burgersSolution (1 / 100) corner 7 5 x := by
  simpa only [show (2 : ℝ) + 3 = 5 by norm_num] using
    burgersSolution_restart corner_continuous ⟨1, corner_bound⟩
      (by norm_num) 7 (-5) 2 3 x (by norm_num) (by norm_num)

example (t x : ℝ) (ht : 0 ≤ t) :
    burgersSolution 3 corner (-9) t x = burgersSolution 3 corner 17 t x :=
  burgersSolution_anchor_independent corner_continuous ⟨1, corner_bound⟩
    (by norm_num) (-9) 17 t x ht

-- Signed data are allowed; the positivity restriction is on viscosity, not velocity.
example (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    burgersSolution 3 (burgersSolution 3 sin 0 s) 0 t = burgersSolution 3 sin 0 (s + t) :=
  burgersSolution_semigroup continuous_sin ⟨1, abs_sin_le_one⟩ (by norm_num) 0 s t hs ht

-- Three successive restarts use the same API, including changing anchors twice.
example {u₀ : ℝ → ℝ} (hu : Continuous u₀) (hb : ∃ M, ∀ x, |u₀ x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (a b c x : ℝ) :
    burgersSolution ν (burgersSolution ν (burgersSolution ν u₀ a 2) b 3) c 5 x =
      burgersSolution ν u₀ a 10 x := by
  have hc2 : Continuous (burgersSolution ν u₀ a 2) :=
    (burgersSolution_continuous_of_bounded hu hb hν a).comp
      (continuous_const.prodMk continuous_id)
  have hb2 : ∃ M, ∀ y, |burgersSolution ν u₀ a 2 y| ≤ M := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun y => abs_burgersSolution_le hu hν hM a 2 y⟩
  rw [burgersSolution_restart hc2 hb2 hν b c 3 5 x (by norm_num) (by norm_num)]
  rw [burgersSolution_restart hu hb hν a b 2 (3 + 5) x (by norm_num) (by norm_num)]
  norm_num

-- Exact constant states are fixed points even across restarts with a different anchor.
example (c a b s t x : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    burgersSolution 3 (burgersSolution 3 (fun _ => c) a s) b t x = c := by
  rw [burgersSolution_restart continuous_const ⟨|c|, fun _ => le_rfl⟩
    (by norm_num) a b s t x hs ht]
  have h := burgersSolution_mem_Icc (u₀ := fun _ => c) continuous_const
    (by norm_num : (0 : ℝ) < 3)
    (a := c) (b := c) (fun _ => ⟨le_rfl, le_rfl⟩) a (s + t) x
  exact le_antisymm h.2 h.1

-- The generic restart theorem does not require the field's past to solve the PDE.
private noncomputable def past (t : ℝ) (_x : ℝ) : ℝ := if 0 ≤ t then 2 else -11

private theorem past_continuous :
    ContinuousOn (Function.uncurry past) (Ici 0 ×ˢ univ) :=
  (continuousOn_const (c := (2 : ℝ))).congr (fun p hp => by
    simp [Function.uncurry_def, past, show 0 ≤ p.1 from hp.1])

private theorem past_smooth :
    ContDiffOn ℝ 2 (Function.uncurry past) (Ioi 0 ×ˢ univ) :=
  (contDiffOn_const (c := (2 : ℝ))).congr (fun p hp => by
    simp [Function.uncurry_def, past, le_of_lt hp.1])

private theorem past_burgers (t x : ℝ) (ht : 0 < t) :
    deriv (fun r => past r x) t + past t x * deriv (past t) x =
      3 * iteratedDeriv 2 (past t) x := by
  have he : (fun r => past r x) =ᶠ[𝓝 t] (fun _ => (2 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    simp [past, hr.le]
  have hx : past t = fun _ => (2 : ℝ) := funext (fun _ => by simp [past, ht.le])
  rw [he.deriv_eq, hx]
  simp [iteratedDeriv_const]

example (a s t x : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    past (s + t) x = burgersSolution 3 (past s) a t x :=
  burgers_restart (by norm_num) past_continuous past_smooth
    (fun _ _ => ⟨2, fun r hr _ => by simp [past, hr.1]⟩)
    (fun r hr y => past_burgers r y hr) a s t x hs ht

example : past (-1) 0 ≠ past 0 0 := by norm_num [past]
