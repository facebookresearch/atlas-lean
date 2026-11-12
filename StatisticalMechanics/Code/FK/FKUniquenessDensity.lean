/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































































import Mathlib
import Code.FK.EdgeMarginal
import Code.FK.Uniqueness
import Code.FK.PressureDiff

open Set Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK




















theorem fud_eq_at_continuousAt_of_convex {a b g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (ha_eq : ∀ p, a p = pressureLeftDeriv g p)
    (hb_eq : ∀ p, b p = pressureRightDeriv g p)
    {p : ℝ} (hp : ContinuousAt b p) : a p = b p := by
  
  have hb_fun : b = pressureRightDeriv g := funext hb_eq
  have hc : ContinuousAt (pressureRightDeriv g) p := hb_fun ▸ hp
  rw [ha_eq p, hb_eq p]
  exact pressureLeftDeriv_eq_rightDeriv_of_continuousAt hg hc

variable {E : Type*} [Fintype E] [DecidableEq E]
































theorem fud_heq_at_cont_of_convexPerEdge
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E) (g : E → ℝ → ℝ)
    (hg : ∀ e', ConvexOn ℝ univ (g e'))
    (ha_eq : ∀ e' p, edgeMargProb (μ p) e' = pressureLeftDeriv (g e') p)
    (hb_eq : ∀ e' p, edgeMargProb (ν p) e' = pressureRightDeriv (g e') p)
    (hlink : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, ContinuousAt (fun p => edgeMargProb (ν p) e') p) :
    ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e' := by
  intro p hp e'
  
  have hp' : ContinuousAt (fun p => edgeMargProb (ν p) e') p := hlink p hp e'
  
  exact fud_eq_at_continuousAt_of_convex (hg e')
    (a := fun p => edgeMargProb (μ p) e') (b := fun p => edgeMargProb (ν p) e')
    (fun p => ha_eq e' p) (fun p => hb_eq e' p) hp'































theorem fud_heq_at_cont_of_homogeneous
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E) {a b g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (ha_hom : ∀ e' p, edgeMargProb (μ p) e' = a p)
    (hb_hom : ∀ e' p, edgeMargProb (ν p) e' = b p)
    (ha_eq : ∀ p, a p = pressureLeftDeriv g p)
    (hb_eq : ∀ p, b p = pressureRightDeriv g p) :
    ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e' := by
  intro p hp e'
  
  have href : (fun p => edgeMargProb (ν p) e) = b := funext fun p => hb_hom e p
  have hpb : ContinuousAt b p := href ▸ hp
  
  have hab : a p = b p := fud_eq_at_continuousAt_of_convex hg ha_eq hb_eq hpb
  
  rw [ha_hom e' p, hb_hom e' p, hab]





















theorem fud_countable_phi_ne_of_convexPerEdge
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (P : ℝ → ConfigSpace E × ConfigSpace E → ℝ)
    (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
    (hb : Monotone (fun p => edgeMargProb (ν p) e))
    (g : E → ℝ → ℝ) (hg : ∀ e', ConvexOn ℝ univ (g e'))
    (ha_eq : ∀ e' p, edgeMargProb (μ p) e' = pressureLeftDeriv (g e') p)
    (hb_eq : ∀ e' p, edgeMargProb (ν p) e' = pressureRightDeriv (g e') p)
    (hlink : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, ContinuousAt (fun p => edgeMargProb (ν p) e') p) :
    {p : ℝ | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧
        eventMassProb (μ p) A ≠ eventMassProb (ν p) A}.Countable :=
  countable_phi_ne μ ν e P hcoup hb
    (fud_heq_at_cont_of_convexPerEdge μ ν e g hg ha_eq hb_eq hlink)













theorem fud_countable_phi_ne_of_homogeneous
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (P : ℝ → ConfigSpace E × ConfigSpace E → ℝ)
    (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
    (hb_mono : Monotone (fun p => edgeMargProb (ν p) e))
    {a b g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (ha_hom : ∀ e' p, edgeMargProb (μ p) e' = a p)
    (hb_hom : ∀ e' p, edgeMargProb (ν p) e' = b p)
    (ha_eq : ∀ p, a p = pressureLeftDeriv g p)
    (hb_eq : ∀ p, b p = pressureRightDeriv g p) :
    {p : ℝ | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧
        eventMassProb (μ p) A ≠ eventMassProb (ν p) A}.Countable :=
  countable_phi_ne μ ν e P hcoup hb_mono
    (fud_heq_at_cont_of_homogeneous μ ν e hg ha_hom hb_hom ha_eq hb_eq)













theorem fud_norm_rightDeriv_zero : pressureRightDeriv (fun x : ℝ => ‖x‖) 0 = 1 := by
  unfold pressureRightDeriv
  have heq : Set.EqOn (fun x : ℝ => ‖x‖) (fun x : ℝ => x) (Ioi (0:ℝ)) := by
    intro x hx; rw [mem_Ioi] at hx; simp [Real.norm_eq_abs, abs_of_pos hx]
  rw [derivWithin_congr heq (by simp)]
  rw [derivWithin_id' 0 (Ioi 0) (uniqueDiffWithinAt_Ioi 0)]


theorem fud_norm_leftDeriv_zero : pressureLeftDeriv (fun x : ℝ => ‖x‖) 0 = -1 := by
  unfold pressureLeftDeriv
  have heq : Set.EqOn (fun x : ℝ => ‖x‖) (fun x : ℝ => -x) (Iio (0:ℝ)) := by
    intro x hx; rw [mem_Iio] at hx; simp [Real.norm_eq_abs, abs_of_neg hx]
  rw [derivWithin_congr heq (by simp)]
  have h1 : HasDerivWithinAt (fun x : ℝ => -x) (-1) (Iio 0) 0 := by
    simpa using (hasDerivWithinAt_id (0:ℝ) (Iio 0)).neg
  rw [h1.derivWithin (uniqueDiffWithinAt_Iio 0)]









theorem fud_homogeneous_datum_nonvacuous :
    ∃ g : ℝ → ℝ, ConvexOn ℝ univ g
      ∧ pressureLeftDeriv g 0 ≠ pressureRightDeriv g 0 :=
  ⟨fun x => ‖x‖, convexOn_univ_norm, by
    rw [fud_norm_leftDeriv_zero, fud_norm_rightDeriv_zero]; norm_num⟩

end FK

end StatMech
