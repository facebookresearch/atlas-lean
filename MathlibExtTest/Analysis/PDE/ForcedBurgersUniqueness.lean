/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.PDE.ForcedBurgersUniqueness
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

open Set Real
open scoped ContDiff
open ColeHopf

-- Finite spatial C2 potential data suffice for uniqueness; no time derivative
-- of q or second time derivative of the competitor is an input.
example {u q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hu : IsBoundedForcedBurgersSolutionOn ν q u₀ T u) (a : ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x = forcedBurgersSolution ν q u₀ a t x :=
  hu.eq_forcedBurgersSolution hν hT hqs hqc hqb a

private theorem corner_potential_data :
    (∀ s ∈ Icc (0 : ℝ) 3, ContDiff ℝ 2 (fun _ : ℝ => |s-1|)) ∧
    (∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ =>
      iteratedDeriv k (fun _ : ℝ => |p.1-1|) p.2) (Icc 0 3 ×ˢ univ)) ∧
    (∀ k ≤ 2, ∃ M, ∀ s ∈ Icc (0 : ℝ) 3, ∀ x : ℝ,
      |iteratedDeriv k (fun _ : ℝ => |s-1|) x| ≤ M) := by
  refine ⟨fun _ _ => contDiff_const,?_,?_⟩
  · intro k hk
    interval_cases k <;> simp only [iteratedDeriv_const] <;> norm_num
    all_goals fun_prop
  · intro k hk
    refine ⟨2,fun s hs x => ?_⟩
    interval_cases k <;> simp only [iteratedDeriv_const] <;> norm_num
    · rw [abs_le]
      constructor <;> linarith [hs.1,hs.2]

private theorem constant_competitor :
    IsBoundedForcedBurgersSolutionOn 3 (fun t _ => |t-1|) (fun _ => 1) 3 (fun _ _ => 1) := by
  refine ⟨by fun_prop,fun _ _ => contDiff_const,fun _ _ _ => differentiableAt_const _,
    ?_,?_,fun _ => rfl,⟨1,fun _ _ _ => by norm_num⟩⟩
  · simp only [deriv_const]
    fun_prop
  · intro t ht x
    simp [iteratedDeriv_succ]

-- The potential has a temporal corner, so this uses the finite potential class,
-- not a globally smooth potential specialization. The initial primitive is unbounded.
example (a x t : ℝ) (ht : t ∈ Icc 0 3) :
    forcedBurgersSolution 3 (fun s _ => |s-1|) (fun _ => 1) a t x = 1 := by
  obtain ⟨hqs,hqc,hqb⟩ := corner_potential_data
  exact (constant_competitor.eq_forcedBurgersSolution (by norm_num) (by norm_num)
    hqs hqc hqb a t ht x).symm

-- Profile identification names the actual Volterra evolution and includes terminal time.
example (a x : ℝ) :
    initialForcedInverseProfile 3 (fun _ _ => 1) (fun s _ => |s-1|) a 3 x =
      forcedBurgersProfile 3 (fun s _ => |s-1|) (fun _ => 1) a 3 x := by
  obtain ⟨hqs,hqc,hqb⟩ := corner_potential_data
  exact constant_competitor.inverseProfile_eq (by norm_num) (by norm_num)
    hqs hqc hqb a 3 (by constructor <;> norm_num) x

-- Two competitors agree even though their ambient extensions need not agree.
example {u v : ℝ → ℝ → ℝ}
    (hu : IsBoundedForcedBurgersSolutionOn 3 (fun s _ => |s-1|) (fun _ => 1) 3 u)
    (hv : IsBoundedForcedBurgersSolutionOn 3 (fun s _ => |s-1|) (fun _ => 1) 3 v)
    (t x : ℝ) (ht : t ∈ Icc 0 3) : u t x = v t x := by
  obtain ⟨hqs,hqc,hqb⟩ := corner_potential_data
  exact (hu.eq_forcedBurgersSolution (by norm_num) (by norm_num) hqs hqc hqb 0 t ht x).trans
    (hv.eq_forcedBurgersSolution (by norm_num) (by norm_num) hqs hqc hqb 0 t ht x).symm

-- The zero horizon permits arbitrary, even discontinuous, values outside the strip.
private theorem degenerate_competitor (f : ℝ → ℝ → ℝ) :
    IsBoundedForcedBurgersSolutionOn 3 (fun _ _ => 0) (fun _ => 1) 0
      (fun t x => if t = 0 then 1 else f t x) := by
  refine ⟨?_,?_,?_,?_,?_,fun x => by simp,⟨1,?_⟩⟩
  · apply (continuousOn_const (c := (1 : ℝ))).congr
    intro p hp
    have ht : p.1 = 0 := le_antisymm hp.1.2 hp.1.1
    simp [Function.uncurry_def,ht]
  · intro t ht
    exact False.elim (not_lt_of_ge ht.1.le ht.2)
  · intro t ht
    exact False.elim (not_lt_of_ge ht.1.le ht.2)
  · simp
  · intro t ht
    exact False.elim (not_lt_of_ge ht.1.le ht.2)
  · intro t ht x
    have he : t = 0 := le_antisymm ht.2 ht.1
    simp [he]

example (f : ℝ → ℝ → ℝ) (a x : ℝ) :
    (if (0 : ℝ) = 0 then 1 else f 0 x) =
      forcedBurgersSolution 3 (fun _ _ => 0) (fun _ => 1) a 0 x := by
  apply (degenerate_competitor f).eq_forcedBurgersSolution (by norm_num) le_rfl
    (fun _ _ => contDiff_const) (fun k _ => by simp; fun_prop)
    (fun k _ => ⟨0,fun _ _ _ => by simp⟩) a 0 ⟨le_rfl,le_rfl⟩ x

-- Actual existence in the uniqueness class accepts cusp initial data.
example (T : ℝ) (hT : 0 ≤ T) (a : ℝ) :
    IsBoundedForcedBurgersSolutionOn 3 (fun _ _ => 0) (fun x => |sin x|) T
      (forcedBurgersSolution 3 (fun _ _ => 0) (fun x => |sin x|) a) := by
  apply forcedBurgersSolution_isBoundedForcedBurgersSolutionOn (by norm_num) hT (by fun_prop)
    ⟨1,fun x => by simpa only [abs_abs] using abs_sin_le_one x⟩ (by fun_prop)
  intro n
  exact ⟨0,fun p _ => by simp [Function.uncurry_def]⟩

-- Membership also yields actual first-time-derivative continuity at positive times.
example {q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hu : Continuous u₀) (hub : ∃ M, ∀ x, |u₀ x| ≤ M)
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M) (a : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => forcedBurgersSolution ν q u₀ a s p.2) p.1)
      (Ioo 0 T ×ˢ univ) :=
  (forcedBurgersSolution_isBoundedForcedBurgersSolutionOn hν hT hu hub hq hb a).continuousOn_timeDeriv

-- The construction and uniqueness theorems use the same smooth-potential inputs;
-- users need not separately rebuild the finite spatial derivative bounds.
example {q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hu : Continuous u₀) (hub : ∃ M, ∀ x, |u₀ x| ≤ M)
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M) (a : ℝ) :
    IsBoundedForcedBurgersSolutionOn ν q u₀ T (forcedBurgersSolution ν q u₀ a) ∧
      ∀ v, IsBoundedForcedBurgersSolutionOn ν q u₀ T v →
        ∀ t ∈ Icc 0 T, ∀ x, v t x = forcedBurgersSolution ν q u₀ a t x := by
  exact ⟨forcedBurgersSolution_isBoundedForcedBurgersSolutionOn hν hT hu hub hq hb a,
    fun v hv => hv.eq_forcedBurgersSolution_of_contDiff hν hT hq hb a⟩
