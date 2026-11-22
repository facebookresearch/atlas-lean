/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Ring

/-!
# Tube bootstrap for perturbed ODE trajectories

A first-exit (bootstrap) form of Mathlib's Gronwall estimate for
two trajectories of the same field: the estimate
`dist_le_of_approx_trajectories_ODE_of_mem` is applied only on
intervals where tube membership is already known, and full-horizon
membership follows from a first-exit contradiction when the
Gronwall bound stays strictly below the tube margin. This is the
form needed by orbital-mechanics perturbation consumers, where the
field's Lipschitz constant is available only on a tube around a
nominal collision-free trajectory.

## Main results

* `MathlibExt.Analysis.ODE.TubeBootstrap.tube_bootstrap`: if
  `gronwallBound δ K ε T < margin`, a perturbed trajectory with
  residual `ε` and initial deviation `δ` stays in the closed
  `margin`-tube around an exact trajectory on `[0, T]`, with
  `dist (f t) (g t) ≤ gronwallBound δ K ε t` throughout.
-/

@[expose] public section

namespace MathlibExt.Analysis.ODE.TubeBootstrap

/-- Tube bootstrap for a perturbed trajectory: let `f` be an exact
trajectory of the field `v` on `[0, T]`, and `g` a perturbed
trajectory with residual `ε`, both in a normed space `E`. Assume
`v t` is Lipschitz with constant `K` on the closed `margin`-tube
around `f t` for every `t`, `g` has within-derivative `g' t` on
`Set.Ici t` with `dist (g' t) (v t (g t)) ≤ ε` whenever
`g t` is in the tube, `f` and `g` are continuous on `[0, T]`, and
the initial deviation is at most `δ`. If the Gronwall bound
`gronwallBound δ K ε T` is strictly below `margin`, then `g` never
leaves the tube on `[0, T]` and
`dist (f t) (g t) ≤ gronwallBound δ K ε t` for all `t ∈ [0, T]`.
The Gronwall inequality is applied only on intervals where tube
membership is already known; membership on the full horizon is the
bootstrap conclusion, not a premise. -/
theorem tube_bootstrap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : ℝ → E → E} {f g g' : ℝ → E}
    {K : NNReal} {ε δ margin T : ℝ} (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hmargin : 0 < margin)
    (hbound : gronwallBound δ K ε T < margin)
    (hv : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      LipschitzOnWith K (v t) (Metric.closedBall (f t) margin))
    (hf : ContinuousOn f (Set.Icc 0 T))
    (hf' : ∀ t : ℝ, t ∈ Set.Ico 0 T →
      HasDerivWithinAt f (v t (f t)) (Set.Ici t) t)
    (hg : ContinuousOn g (Set.Icc 0 T))
    (hg' : ∀ t : ℝ, t ∈ Set.Ico 0 T → g t ∈ Metric.closedBall (f t) margin →
      HasDerivWithinAt g (g' t) (Set.Ici t) t ∧
        dist (g' t) (v t (g t)) ≤ ε)
    (ha : dist (f 0) (g 0) ≤ δ) :
    ∀ t : ℝ, t ∈ Set.Icc 0 T →
      g t ∈ Metric.closedBall (f t) margin ∧
        dist (f t) (g t) ≤ gronwallBound δ K ε t := by
  have _hT : (0:ℝ) ≤ T := hT
  have hδ : 0 ≤ δ := dist_nonneg.trans ha
  have hK : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
  have hmono : Monotone (gronwallBound δ K ε) := gronwallBound_mono hδ hε hK
  have hD : ContinuousOn (fun u => dist (f u) (g u)) (Set.Icc 0 T) :=
    continuous_dist.comp_continuousOn (hf.prodMk hg)
  set Bad : Set ℝ := Set.Icc 0 T ∩ (fun u => dist (f u) (g u)) ⁻¹' (Set.Ici margin) with hBad_def
  have mem_Bad_iff : ∀ t : ℝ, t ∈ Bad ↔ (t ∈ Set.Icc 0 T ∧ margin ≤ dist (f t) (g t)) := by
    intro t
    simp only [hBad_def, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
  have hBadClosed : IsClosed Bad :=
    hD.preimage_isClosed_of_isClosed (t := Set.Ici margin) isClosed_Icc isClosed_Ici
  have hBdd : BddBelow Bad := by
    refine ⟨0, mem_lowerBounds.mpr ?_⟩
    intro b hb
    exact ((mem_Bad_iff b).mp hb).1.1
  have hmem_of : ∀ t ∈ Set.Icc (0:ℝ) T, t ∉ Bad → g t ∈ Metric.closedBall (f t) margin := by
    intro t htIcc htBad
    have hlt : dist (f t) (g t) < margin :=
      lt_of_not_ge (fun hge => htBad ((mem_Bad_iff t).mpr ⟨htIcc, hge⟩))
    rw [Metric.mem_closedBall, dist_comm (g t) (f t)]
    exact le_of_lt hlt
  by_cases hEmpty : Bad = ∅
  · have hnotmem : ∀ t : ℝ, t ∉ Bad := Set.eq_empty_iff_forall_notMem.mp hEmpty
    have hmemT : ∀ t ∈ Set.Ico (0:ℝ) T, g t ∈ Metric.closedBall (f t) margin := by
      intro t ht
      exact hmem_of t ⟨ht.1, le_of_lt ht.2⟩ (hnotmem t)
    have hG := dist_le_of_approx_trajectories_ODE_of_mem
      (s := fun t => Metric.closedBall (f t) margin)
      (f' := fun t => v t (f t)) (εf := (0:ℝ)) (a := (0:ℝ)) (b := T)
      (fun t ht => hv t ⟨ht.1, le_of_lt ht.2⟩)
      hf hf'
      (fun t _ => (dist_self (v t (f t))).le)
      (fun t _ => by
        show f t ∈ Metric.closedBall (f t) margin
        rw [Metric.mem_closedBall, dist_self]
        exact hmargin.le)
      hg
      (fun t ht => (hg' t ht (hmemT t ht)).1)
      (fun t ht => (hg' t ht (hmemT t ht)).2)
      hmemT ha
    intro t ht
    have hle := hG t ht
    simp only [zero_add, sub_zero] at hle
    exact ⟨hmem_of t ht (hnotmem t), hle⟩
  · have hNe : Bad.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    have ht0mem : sInf Bad ∈ Bad := hBadClosed.csInf_mem hNe hBdd
    set t0 : ℝ := sInf Bad
    obtain ⟨ht0Icc, ht0ge⟩ := (mem_Bad_iff t0).mp ht0mem
    obtain ⟨ht00, ht0T⟩ := ht0Icc
    have hmem : ∀ t ∈ Set.Ico (0:ℝ) t0, g t ∈ Metric.closedBall (f t) margin := by
      intro t ht
      refine hmem_of t ⟨ht.1, le_trans (le_of_lt ht.2) ht0T⟩ ?_
      intro hmt
      exact not_le_of_gt ht.2 (csInf_le hBdd hmt)
    have hG := dist_le_of_approx_trajectories_ODE_of_mem
      (s := fun t => Metric.closedBall (f t) margin)
      (f' := fun t => v t (f t)) (εf := (0:ℝ)) (a := (0:ℝ)) (b := t0)
      (fun t ht => hv t ⟨ht.1, le_trans (le_of_lt ht.2) ht0T⟩)
      (hf.mono (Set.Icc_subset_Icc_right ht0T))
      (fun t ht => hf' t ⟨ht.1, lt_of_lt_of_le ht.2 ht0T⟩)
      (fun t _ => (dist_self (v t (f t))).le)
      (fun t _ => by
        show f t ∈ Metric.closedBall (f t) margin
        rw [Metric.mem_closedBall, dist_self]
        exact hmargin.le)
      (hg.mono (Set.Icc_subset_Icc_right ht0T))
      (fun t ht => (hg' t ⟨ht.1, lt_of_lt_of_le ht.2 ht0T⟩ (hmem t ht)).1)
      (fun t ht => (hg' t ⟨ht.1, lt_of_lt_of_le ht.2 ht0T⟩ (hmem t ht)).2)
      hmem ha
    have hle := hG t0 ⟨ht00, le_refl t0⟩
    simp only [zero_add, sub_zero] at hle
    have hmono_le : gronwallBound δ (K:ℝ) ε t0 ≤ gronwallBound δ K ε T := hmono ht0T
    have hcon : margin < margin := lt_of_le_of_lt (le_trans ht0ge (le_trans hle hmono_le)) hbound
    exact (lt_irrefl margin hcon).elim

end MathlibExt.Analysis.ODE.TubeBootstrap
