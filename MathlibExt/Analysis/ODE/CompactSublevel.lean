/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

arnovich/forseti-lean, commit
0a81edc7fe82748af7c9b1139229c4d898f50c28,
`Gimle/Forseti/Nonlinear.lean` and `Gimle/Forseti/LocalTrapping.lean`. Authors: arnovich.

MIT License

Copyright (c) 2025 Gimle Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import MathlibExt.Analysis.ODE.LyapunovStability
public import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Analysis.Calculus.MeanValue
import MathlibExt.Analysis.ODE.FiniteIntervalSublevel

/-!
# Compact Lyapunov sublevels give forward global existence

Strict decrease on the level set `V = c` of a compact sublevel prevents exit.
Atlas's maximal-solution theorem then rules out a finite forward endpoint: the
space-time graph could not leave the product of a bounded time interval with
that compact sublevel. The field need only be locally Lipschitz, not globally
Lipschitz. No sign condition is required where `V < c`; the strict condition
does apply to every point where `V = c`, even an interior point of the sublevel.

A second version allows a nonpositive orbital derivative everywhere, including
conserved energies and degenerate levels. This supplements the conditional
estimates in `LyapunovStability` with existence rather than assuming a global
solution or that it already stays in the sublevel.
-/

@[expose] public section

open Set Filter
open scoped Topology NNReal

namespace MathlibExt.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strict decrease on the level set `V = c` prevents exit on a finite interval.
No sign condition is required where `V < c`. The level set may contain interior
points of the sublevel, so this hypothesis is stronger than boundary decrease. -/
theorem mapsTo_sublevel_of_boundary_deriv_neg
    {F : E → E} {V : E → ℝ} {c a b : ℝ} {x : ℝ → E}
    (hV : Differentiable ℝ V)
    (hbd : ∀ y, V y = c → fderiv ℝ V y (F y) < 0)
    (hx : IsIntegralCurveOn x (fun _ => F) (Icc a b)) (h₀ : V (x a) ≤ c) :
    MapsTo x (Icc a b) {y | V y ≤ c} := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (V ∘ x) (fderiv ℝ V (x t) (F (x t))) (Icc a b) t :=
    hx.hasDerivWithinAt_comp ht (hV (x t)).hasFDerivAt
  have hright (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt (V ∘ x) (fderiv ℝ V (x t) (F (x t))) (Ici t) t :=
    (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2)
        (Icc_subset_Icc_left ht.1))
  exact image_le_of_deriv_right_lt_deriv_boundary'
    (fun t ht => (hd t ht).continuousWithinAt) hright h₀
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (fun t _ ht => hbd (x t) ht)

private theorem exists_forward_solution_of_compact_trapping [CompleteSpace E]
    {F : E → E} {K : Set E} (hF : LocallyLipschitz F) (hK : IsCompact K)
    (a : ℝ) (x₀ : E)
    (hinv : ∀ (I : Set ℝ) (x : ℝ → E), x a = x₀ → a ∈ I →
      (∀ s ∈ I, ∀ t ∈ I, Icc s t ⊆ I) →
      (∀ t ∈ I, HasDerivAt x (F (x t)) t) →
      ∀ t ∈ I, a ≤ t → x t ∈ K) :
    ∃ x : ℝ → E, x a = x₀ ∧ (∀ t ∈ Ici a, x t ∈ K) ∧
      ∀ t ∈ Ici a, HasDerivAt x (F (x t)) t := by
  obtain ⟨I, x, hx₀, -, ha, hI, hx, hexit⟩ :=
    MaximalSolutionWanted.ode_maximal_solution_exit_compact univ
      (fun p => F p.2) a x₀ isOpen_univ trivial
      (hF.continuous.comp continuous_snd).continuousOn fun p _ => by
        obtain ⟨L, s, hs, hL⟩ := hF p.2
        exact ⟨L, univ ×ˢ s, prod_mem_nhds univ_mem hs,
          fun t y z hy hz => hL.dist_le_mul y hy.1.2 z hz.1.2⟩
  have htrap := hinv I x hx₀ ha hI (fun t ht => (hx t ht).2)
  have hglobal : Ici a ⊆ I := by
    intro b hb
    by_contra hbI
    obtain ⟨⟨d, hd, hexitd⟩, -⟩ :=
      hexit (Icc a b ×ˢ K) (isCompact_Icc.prod hK) (subset_univ _)
    have hm : max d a ∈ I := by
      rcases max_cases d a with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
      · exact hd
      · exact ha
    have hmb : max d a ≤ b := by
      by_contra h
      exact hbI (hI a ha _ hm ⟨hb, (not_le.mp h).le⟩)
    exact hexitd _ hm (le_max_left _ _)
      ⟨⟨le_max_right _ _, hmb⟩, htrap _ hm (le_max_right _ _)⟩
  exact ⟨x, hx₀, fun t ht => htrap t (hglobal ht) ht,
    fun t ht => (hx t (hglobal ht)).2⟩

/-- A compact Lyapunov sublevel with strict decrease on the level set `V = c`
contains a forward global solution through each of its points. No sign condition
is required where `V < c`.
The decrease condition is needed only when `V y = c`. -/
theorem exists_forward_solution_of_compact_sublevel [CompleteSpace E]
    {F : E → E} {V : E → ℝ} {c : ℝ}
    (hF : LocallyLipschitz F) (hV : Differentiable ℝ V)
    (hK : IsCompact {y | V y ≤ c}) (a : ℝ) {x₀ : E} (h₀ : V x₀ ≤ c)
    (hbd : ∀ y, V y = c → fderiv ℝ V y (F y) < 0) :
    ∃ x : ℝ → E, x a = x₀ ∧ (∀ t ∈ Ici a, V (x t) ≤ c) ∧
      ∀ t ∈ Ici a, HasDerivAt x (F (x t)) t := by
  apply exists_forward_solution_of_compact_trapping hF hK a x₀
  intro I x hx₀ ha hI hx t ht hat
  have hx' : IsIntegralCurveOn x (fun _ => F) (Icc a t) :=
    fun s hs => (hx s (hI a ha t ht hs)).hasDerivWithinAt
  exact mapsTo_sublevel_of_boundary_deriv_neg hV hbd hx'
    (by rw [hx₀]; exact h₀) ⟨hat, le_rfl⟩

/-- If the orbital derivative is nonpositive everywhere and the initial
sublevel is compact, a forward global solution exists in that sublevel.
Unlike strict level-set trapping, this includes conserved energies. -/
theorem exists_forward_solution_of_compact_sublevel_nonpos [CompleteSpace E]
    {F : E → E} {V : E → ℝ} {c : ℝ}
    (hF : LocallyLipschitz F) (hV : Differentiable ℝ V)
    (hK : IsCompact {y | V y ≤ c}) (a : ℝ) {x₀ : E} (h₀ : V x₀ ≤ c)
    (hdec : ∀ y, fderiv ℝ V y (F y) ≤ 0) :
    ∃ x : ℝ → E, x a = x₀ ∧ (∀ t ∈ Ici a, V (x t) ≤ c) ∧
      ∀ t ∈ Ici a, HasDerivAt x (F (x t)) t := by
  apply exists_forward_solution_of_compact_trapping hF hK a x₀
  intro I x hx₀ ha hI hx t ht hat
  have hd (s : ℝ) (hs : s ∈ Icc a t) := hx s (hI a ha t ht hs)
  exact finite_interval_mapsTo_sublevel hat
    (hV.continuous.comp_continuousOn (fun s hs => (hd s hs).continuousAt.continuousWithinAt))
    (fun s hs => hd s (Ioo_subset_Icc_self hs)) (fun s _ => hV (x s))
    (fun s _ => hdec (x s)) (by rw [hx₀]; exact h₀) ⟨hat, le_rfl⟩

end MathlibExt.Analysis.ODE
