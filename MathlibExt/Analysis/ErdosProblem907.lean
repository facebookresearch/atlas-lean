/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/907.lean` (google-deepmind/formal-conjectures):
the definition of `conjecture` and the statement of `conjecture_holds`.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic.Linarith

/-!
# De Bruijn's theorem on continuous differences

`conjecture_holds` decomposes a real function with continuous differences into the sum of a
continuous function and an additive function. We construct the additive part by integrating
differences over a unit interval. Baire category supplies a local bound for the integrand
representing the remainder, so dominated convergence gives a point of continuity.
-/

@[expose] public section

namespace MathlibExt.Analysis.ErdosProblem907Wanted

/-- **Erdős Problem 907.** The statement that every function $f : \mathbb{R} \to \mathbb{R}$
such that $x \mapsto f(x + h) - f(x)$ is continuous for every $h > 0$ can be written as
$f = g + a$ with $g : \mathbb{R} \to \mathbb{R}$ continuous and $a : \mathbb{R} \to \mathbb{R}$
additive, that is, $a(x + y) = a(x) + a(y)$ for all real $x$ and $y$. -/
def conjecture : Prop :=
  ∀ f : ℝ → ℝ, (∀ h : ℝ, 0 < h → Continuous fun x => f (x + h) - f x) →
    ∃ g a : ℝ → ℝ, Continuous g ∧ (∀ x y, a (x + y) = a x + a y) ∧ f = g + a

open Filter MeasureTheory Set
open scoped Topology fwdDiff

private lemma continuous_fwdDiff (f : ℝ → ℝ) (hf : ∀ h, 0 < h → Continuous (Δ_[h] f))
    (h : ℝ) : Continuous (Δ_[h] f) := by
  rcases lt_trichotomy h 0 with hneg | rfl | hpos
  · have hc := ((hf (-h) (neg_pos.mpr hneg)).comp (continuous_id.add_const h)).neg
    change Continuous (fun x => -(f (x + h + -h) - f (x + h))) at hc
    change Continuous (fun x => f (x + h) - f x)
    simpa using hc
  · change Continuous (fun x => f (x + 0) - f x)
    simp [continuous_const]
  · exact hf h hpos

private noncomputable def avgDiff (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in 0..1, Δ_[x] f t

private noncomputable def correction (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in 0..x, Δ_[1] f t

-- Shifting the unit interval changes the average by two boundary integrals.
private lemma additive_avgDiff_sub_correction (f : ℝ → ℝ) (hc : ∀ h, Continuous (Δ_[h] f))
    (x y : ℝ) :
    avgDiff f (x + y) - correction f (x + y) =
      (avgDiff f x - correction f x) + (avgDiff f y - correction f y) := by
  have shift : avgDiff f (x + y) - avgDiff f x = ∫ t in x..1 + x, Δ_[y] f t := by
    unfold avgDiff
    rw [← intervalIntegral.integral_sub ((hc _).intervalIntegrable _ _)
      ((hc _).intervalIntegrable _ _)]
    have heq (t : ℝ) : Δ_[x + y] f t - Δ_[x] f t = Δ_[y] f (t + x) := by
      simp only [fwdDiff, add_assoc]
      abel
    simp_rw [heq]
    rw [intervalIntegral.integral_comp_add_right, zero_add]
  have boundary : (∫ t in 1..1 + x, Δ_[y] f t) - (∫ t in 0..x, Δ_[y] f t) =
      (∫ t in y..x + y, Δ_[1] f t) - correction f x := by
    have heq (t : ℝ) : Δ_[y] f (t + 1) - Δ_[y] f t = Δ_[1] f (t + y) - Δ_[1] f t := by
      simp only [fwdDiff, add_right_comm t 1 y]
      abel
    have translate (h k : ℝ) : (∫ t in k..x + k, Δ_[h] f t) =
        ∫ t in 0..x, Δ_[h] f (t + k) := by
      rw [intervalIntegral.integral_comp_add_right, zero_add]
    have cont (h k : ℝ) : Continuous fun t => Δ_[h] f (t + k) :=
      (hc h).comp (continuous_id.add_const k)
    unfold correction
    rw [add_comm 1 x, translate, translate]
    rw [← intervalIntegral.integral_sub ((cont y 1).intervalIntegrable _ _)
      ((hc y).intervalIntegrable _ _),
      ← intervalIntegral.integral_sub ((cont 1 y).intervalIntegrable _ _)
        ((hc 1).intervalIntegrable _ _)]
    simp_rw [heq]
  have swap := intervalIntegral.integral_interval_sub_interval_comm'
    ((hc y).intervalIntegrable x (1 + x) (μ := volume))
    ((hc y).intervalIntegrable 0 1) ((hc y).intervalIntegrable x 0)
  have join := intervalIntegral.integral_add_adjacent_intervals
    ((hc 1).intervalIntegrable 0 y (μ := volume)) ((hc 1).intervalIntegrable y (x + y))
  unfold avgDiff at shift ⊢
  unfold correction at boundary ⊢
  linarith only [shift, boundary, swap, join]

-- Separate continuity gives a uniform bound on a neighbourhood of some parameter.
private lemma exists_continuousAt_integral (F : ℝ → ℝ → ℝ) (ht : ∀ x, Continuous (F x))
    (hx : ∀ t, Continuous fun x => F x t) :
    ∃ p, ContinuousAt (fun x => ∫ t in (0 : ℝ)..1, F x t) p := by
  let S (n : ℕ) : Set ℝ := ⋂ t ∈ Icc (0 : ℝ) 1, {x | ‖F x t‖ ≤ n}
  have closed (n : ℕ) : IsClosed (S n) :=
    isClosed_biInter fun t _ => isClosed_le (hx t).norm continuous_const
  have cover : ⋃ n, S n = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image ((ht x).norm.continuousOn (s := Icc 0 1))
    obtain ⟨n, hn⟩ := exists_nat_ge M
    exact mem_iUnion.mpr ⟨n, mem_iInter₂.mpr fun t ht => (hM (mem_image_of_mem _ ht)).trans hn⟩
  obtain ⟨n, p, hp⟩ := nonempty_interior_of_iUnion_of_closed closed cover
  refine ⟨p, intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => (n : ℝ))
    (.of_forall fun x => (ht x).aestronglyMeasurable) ?_ intervalIntegrable_const
    (.of_forall fun t _ => (hx t).continuousAt)⟩
  filter_upwards [mem_interior_iff_mem_nhds.mp hp] with x h
  have bound := mem_iInter₂.mp h
  exact .of_forall fun t ht => bound t (Ioc_subset_Icc_self (by
    simpa only [uIoc_of_le zero_le_one] using ht))

private lemma continuous_of_continuousAt_of_fwdDiff (g : ℝ → ℝ) (hc : ∀ h, Continuous (Δ_[h] g))
    {p : ℝ} (hp : ContinuousAt g p) : Continuous g := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let h := p - x
  have he : x + h = p := add_sub_cancel _ _
  have hp' : ContinuousAt g (x + h) := he ▸ hp
  have hshift := hp'.comp (f := fun z => z + h) (continuous_id.add_const h).continuousAt
  have hsub := hshift.sub ((hc h).continuousAt (x := x))
  change ContinuousAt (fun z => g (z + h) - (g (z + h) - g z)) x at hsub
  simpa using hsub

/--
**De Bruijn's theorem on continuous differences (Erdős Problem 907).** Let
$f : \mathbb{R} \to \mathbb{R}$ be a function such that for every $h > 0$ the function
$x \mapsto f(x + h) - f(x)$ is continuous. Then there are functions
$g, a : \mathbb{R} \to \mathbb{R}$ with $g$ continuous and $a$ additive, that is,
$a(x + y) = a(x) + a(y)$ for all real $x$ and $y$, such that $f = g + a$.

Source: N. G. de Bruijn, Functions whose differences belong to a given class, Nieuw Archief voor
Wiskunde (2) (1951), 194–218, https://mathscinet.ams.org/mathscinet-getitem?mr=43870; External
Lean proof of Erdős Problem 907, plby/lean-proofs at commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos907.lean.
Moved from `OpenConjectures/Analysis/ErdosProblem907`.
-/
public theorem conjecture_holds : conjecture := by
  intro f hf
  have hc := continuous_fwdDiff f hf
  let a (x : ℝ) := avgDiff f x - correction f x
  let g (x : ℝ) := f x - a x
  have hadd : ∀ x y, a (x + y) = a x + a y := additive_avgDiff_sub_correction f hc
  refine ⟨g, a, ?_, hadd, funext fun x => by simp [g]⟩
  have hg (h : ℝ) : Continuous (Δ_[h] g) := by
    have heq : Δ_[h] g = fun x => Δ_[h] f x - a h := by
      funext x
      simp only [fwdDiff, g, hadd]
      abel
    rw [heq]
    exact (hc h).sub continuous_const
  -- The defect of additivity is symmetric and separately continuous.
  let F (x t : ℝ) := f x - Δ_[x] f t
  have hF (x : ℝ) : Continuous (F x) := continuous_const.sub (hc x)
  have hF' (t : ℝ) : Continuous fun x => F x t := by
    have heq : (fun x => F x t) = fun x => f t - Δ_[t] f x := by
      funext x
      simp only [F, fwdDiff, add_comm t x]
      abel
    rw [heq]
    exact continuous_const.sub (hc t)
  obtain ⟨p, hp⟩ := exists_continuousAt_integral F hF hF'
  have heq : g = fun x => (∫ t in (0 : ℝ)..1, F x t) + correction f x := by
    funext x
    simp only [F, intervalIntegral.integral_sub intervalIntegrable_const
      ((hc x).intervalIntegrable _ _), intervalIntegral.integral_const, sub_zero, one_smul]
    dsimp [g, a, avgDiff]
    abel
  -- The continuous differences propagate continuity from this point to every translate.
  apply continuous_of_continuousAt_of_fwdDiff g hg (p := p)
  rw [heq]
  exact hp.add (intervalIntegral.continuous_primitive (fun u v => (hc 1).intervalIntegrable u v)
    0).continuousAt

end MathlibExt.Analysis.ErdosProblem907Wanted
