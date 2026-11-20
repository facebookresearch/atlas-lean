/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.FK.EdgeMarginal
import Code.FK.Uniqueness

open Set Filter Topology

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK







section ConvexFunction

variable {g : ℝ → ℝ}



noncomputable def pressureRightDeriv (g : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin g (Ioi x) x



noncomputable def pressureLeftDeriv (g : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin g (Iio x) x






theorem pressureRightDeriv_monotone (hg : ConvexOn ℝ univ g) :
    Monotone (pressureRightDeriv g) := by
  have hm := hg.monotoneOn_rightDeriv
  rw [interior_univ] at hm
  intro x y hxy
  exact hm (mem_univ x) (mem_univ y) hxy



theorem pressureLeftDeriv_monotone (hg : ConvexOn ℝ univ g) :
    Monotone (pressureLeftDeriv g) := by
  have hm := hg.monotoneOn_leftDeriv
  rw [interior_univ] at hm
  intro x y hxy
  exact hm (mem_univ x) (mem_univ y) hxy




theorem pressureLeftDeriv_le_rightDeriv (hg : ConvexOn ℝ univ g) (x : ℝ) :
    pressureLeftDeriv g x ≤ pressureRightDeriv g x :=
  hg.leftDeriv_le_rightDeriv_of_mem_interior (x := x) (by rw [interior_univ]; trivial)








theorem pressureRightDeriv_le_leftDeriv_of_lt (hg : ConvexOn ℝ univ g) {z x : ℝ}
    (hzx : z < x) : pressureRightDeriv g z ≤ pressureLeftDeriv g x := by
  have h1 : pressureRightDeriv g z ≤ slope g z x :=
    hg.rightDeriv_le_slope_of_mem_interior (by rw [interior_univ]; trivial) (mem_univ x) hzx
  have h2 : slope g z x ≤ pressureLeftDeriv g x :=
    hg.slope_le_leftDeriv_of_mem_interior (mem_univ z) (by rw [interior_univ]; trivial) hzx
  exact h1.trans h2















theorem pressureLeftDeriv_eq_rightDeriv_of_continuousAt (hg : ConvexOn ℝ univ g) {x : ℝ}
    (hc : ContinuousAt (pressureRightDeriv g) x) :
    pressureLeftDeriv g x = pressureRightDeriv g x := by
  refine le_antisymm (pressureLeftDeriv_le_rightDeriv hg x) ?_
  have hlim : Tendsto (pressureRightDeriv g) (𝓝[<] x) (𝓝 (pressureRightDeriv g x)) :=
    hc.continuousWithinAt
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with z (hz : z < x)
  exact pressureRightDeriv_le_leftDeriv_of_lt hg hz














theorem countable_leftDeriv_ne_rightDeriv (hg : ConvexOn ℝ univ g) :
    {x : ℝ | pressureLeftDeriv g x ≠ pressureRightDeriv g x}.Countable := by
  refine ((pressureRightDeriv_monotone hg).countable_not_continuousAt).mono ?_
  intro x hx
  simp only [mem_setOf_eq] at hx ⊢
  exact fun hcont => hx (pressureLeftDeriv_eq_rightDeriv_of_continuousAt hg hcont)

end ConvexFunction









section Bridge

variable {E : Type*} [Fintype E] [DecidableEq E]


















theorem pressure_convex_countable_density_ne
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (ha_eq : ∀ p, edgeMargProb (μ p) e = pressureLeftDeriv g p)
    (hb_eq : ∀ p, edgeMargProb (ν p) e = pressureRightDeriv g p) :
    {p : ℝ | edgeMargProb (μ p) e ≠ edgeMargProb (ν p) e}.Countable := by
  refine (countable_leftDeriv_ne_rightDeriv hg).mono ?_
  intro p hp
  simp only [mem_setOf_eq] at hp ⊢
  rw [ha_eq p, hb_eq p] at hp
  exact hp


























theorem fk_uniqueness_of_pressure_convex
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (P : ℝ → ConfigSpace E × ConfigSpace E → ℝ)
    (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
    (hb_eq : ∀ p, edgeMargProb (ν p) e = pressureRightDeriv g p)
    (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ {A : Set (ConfigSpace E)}, IsIncreasing A →
        eventMassProb (μ p) A = eventMassProb (ν p) A := by
  
  have hbmono : Monotone (fun p => edgeMargProb (ν p) e) := by
    have : (fun p => edgeMargProb (ν p) e) = pressureRightDeriv g := by
      funext p; exact hb_eq p
    rw [this]; exact pressureRightDeriv_monotone hg
  
  exact phi0_eq_phi1_off_countable μ ν e P hcoup hbmono heq_at_cont








theorem countable_phi_ne_of_pressure_convex
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (P : ℝ → ConfigSpace E × ConfigSpace E → ℝ)
    (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
    (hb_eq : ∀ p, edgeMargProb (ν p) e = pressureRightDeriv g p)
    (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
    {p : ℝ | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧
        eventMassProb (μ p) A ≠ eventMassProb (ν p) A}.Countable := by
  have hbmono : Monotone (fun p => edgeMargProb (ν p) e) := by
    have : (fun p => edgeMargProb (ν p) e) = pressureRightDeriv g := by
      funext p; exact hb_eq p
    rw [this]; exact pressureRightDeriv_monotone hg
  exact countable_phi_ne μ ν e P hcoup hbmono heq_at_cont

end Bridge

end FK

end StatMech
