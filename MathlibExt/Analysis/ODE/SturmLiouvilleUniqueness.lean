/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

namespace MathlibExt.Analysis.ODE.SturmLiouvilleUniqueness

open Function Set

/-!
# Uniqueness for the Sturm–Liouville Dirichlet problem on `[0, 1]`

If `V : C([0, 1], ℝ)` is nonnegative and `f : C([0, 1], ℝ)`, then any two
`C²` solutions `u₁, u₂` of `-u'' + V u = f` on `[0, 1]` with Dirichlet
boundary conditions `u(0) = u(1) = 0` agree on `[0, 1]`. The proof uses the
convexity of `u²` for the difference `u = u₁ - u₂`, which satisfies
`u'' = V u` with `V ≥ 0`, hence `u²` is convex, vanishes at both endpoints,
and so vanishes on `[0, 1]`.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.sturm_liouville_uniqueness`
(Theorem, Section on solving the Dirichlet problem).
This module ports the fully proved v1 uniqueness theorem. The v1 existence
statement `SpectralTheory.sturm_liouville_existence` is left unproved; an
independent proof is formalized in
`MathlibExt/Analysis/ODE/SturmLiouvilleExistence.lean`.
-/

/-- **Uniqueness for the Sturm–Liouville Dirichlet problem on the closed unit interval.** Let $V$
and $f$ be continuous real functions on $[0, 1]$ with $V \ge 0$, and let
$u_1, u_2 \colon \mathbb{R} \to \mathbb{R}$ be $C^2$ on $[0, 1]$. Suppose that for $i = 1, 2$,
$-u_i''(x) + V(x)\,u_i(x) = f(x)$ for every $x \in [0, 1]$, with the second derivative taken
within $[0, 1]$, and $u_i(0) = u_i(1) = 0$. Then $u_1$ and $u_2$ agree on $[0, 1]$. -/
theorem sturm_liouville_uniqueness
    (V : C(Set.Icc (0 : ℝ) 1, ℝ)) (hV : ∀ x : Set.Icc (0 : ℝ) 1, 0 ≤ V x)
    (f : C(Set.Icc (0 : ℝ) 1, ℝ))
    (u₁ u₂ : ℝ → ℝ)
    (h₁ : ContDiffOn ℝ 2 u₁ (Set.Icc 0 1) ∧
      (∀ x : ℝ, ∀ hx : x ∈ Set.Icc (0 : ℝ) 1, -(iteratedDerivWithin 2 u₁ (Set.Icc 0 1) x) +
        V ⟨x, hx⟩ * u₁ x = f ⟨x, hx⟩) ∧
      u₁ 0 = 0 ∧ u₁ 1 = 0)
    (h₂ : ContDiffOn ℝ 2 u₂ (Set.Icc 0 1) ∧
      (∀ x : ℝ, ∀ hx : x ∈ Set.Icc (0 : ℝ) 1, -(iteratedDerivWithin 2 u₂ (Set.Icc 0 1) x) +
        V ⟨x, hx⟩ * u₂ x = f ⟨x, hx⟩) ∧
      u₂ 0 = 0 ∧ u₂ 1 = 0) :
    Set.EqOn u₁ u₂ (Set.Icc 0 1) := by
  obtain ⟨h₁_smooth, h₁_ode, h₁_bc0, h₁_bc1⟩ := h₁
  obtain ⟨h₂_smooth, h₂_ode, h₂_bc0, h₂_bc1⟩ := h₂
  set u : ℝ → ℝ := u₁ - u₂ with hu_def
  have hu0 : u 0 = 0 := by simp [hu_def, Pi.sub_apply, h₁_bc0, h₂_bc0]
  have hu1 : u 1 = 0 := by simp [hu_def, Pi.sub_apply, h₁_bc1, h₂_bc1]
  have hu_smooth : ContDiffOn ℝ 2 u (Icc 0 1) := h₁_smooth.sub h₂_smooth

  have hu_ode : ∀ x : ℝ, ∀ hx : x ∈ Icc (0:ℝ) 1,
      iteratedDerivWithin 2 u (Icc 0 1) x = V ⟨x, hx⟩ * u x := by
    intro x hx
    have h_sub := iteratedDerivWithin_sub hx uniqueDiffOn_Icc_zero_one
      (h₁_smooth.contDiffWithinAt (hx := hx)) (h₂_smooth.contDiffWithinAt (hx := hx))
    simp only [hu_def, Pi.sub_apply] at h_sub ⊢
    have eq1 := h₁_ode x hx
    have eq2 := h₂_ode x hx
    linarith

  have hg_conv : ConvexOn ℝ (Icc 0 1) (fun x => (u x) ^ 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (f' := fun x => 2 * u x * deriv u x)
      (f'' := fun x => 2 * (deriv u x) ^ 2 + 2 * u x * deriv (deriv u) x)
    · exact hu_smooth.continuousOn.pow 2
    · intro x hx
      rw [interior_Icc] at hx
      have hu_at : ContDiffAt ℝ 2 u x := hu_smooth.contDiffAt (Icc_mem_nhds hx.1 hx.2)
      have hd : HasDerivAt u (deriv u x) x :=
        (hu_at.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasDerivAt
      have h : HasDerivAt (fun t => (u t) ^ 2) (2 * u x * deriv u x) x := by
        convert hd.pow 2 using 1; norm_num
      exact h.hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hu_at : ContDiffAt ℝ 2 u x := hu_smooth.contDiffAt (Icc_mem_nhds hx.1 hx.2)
      have hdu : HasDerivAt u (deriv u x) x :=
        (hu_at.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasDerivAt
      have hddu : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
        ((hu_at.derivWithin (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
          (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).hasDerivAt
      have h1 : HasDerivAt (fun t => 2 * u t) (2 * deriv u x) x := hdu.const_mul 2
      have h2 := h1.mul hddu
      have h3 : HasDerivAt (fun t => 2 * u t * deriv u t)
          (2 * (deriv u x) ^ 2 + 2 * u x * deriv (deriv u) x) x := by convert h2 using 1; ring
      exact h3.hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
      have hu_at : ContDiffAt ℝ 2 u x := hu_smooth.contDiffAt (Icc_mem_nhds hx.1 hx.2)
      have h_dd : deriv (deriv u) x = V ⟨x, hx'⟩ * u x := by
        have h1 := hu_ode x hx'
        have h2 : iteratedDerivWithin 2 u (Icc 0 1) x = iteratedDeriv 2 u x :=
          iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one hu_at hx'
        have h3 : iteratedDeriv 2 u x = deriv^[2] u x := congr_fun iteratedDeriv_eq_iterate x
        simp only [iterate_succ, comp, iterate_zero, id] at h3
        linarith
      rw [h_dd]
      nlinarith [sq_nonneg (deriv u x), sq_nonneg (u x), hV ⟨x, hx'⟩]

  intro x hx
  have hux_eq : u x = 0 := by
    have hg0 : (u 0) ^ 2 = 0 := by rw [hu0]; ring
    have hg1 : (u 1) ^ 2 = 0 := by rw [hu1]; ring
    have h_le : (u x) ^ 2 ≤ 0 := by
      have h01 : (0:ℝ) ∈ Icc (0:ℝ) 1 := left_mem_Icc.mpr (by norm_num)
      have h11 : (1:ℝ) ∈ Icc (0:ℝ) 1 := right_mem_Icc.mpr (by norm_num)
      have hx0 : (0:ℝ) ≤ 1 - x := by linarith [hx.2]
      have hx1 : (0:ℝ) ≤ x := hx.1
      have hsum : (1 - x) + x = 1 := by ring
      have key := hg_conv.2 h01 h11 hx0 hx1 hsum
      simp only [smul_eq_mul] at key
      have hsimp : (1 - x) * 0 + x * 1 = x := by ring
      rw [hsimp] at key
      rw [hg0, hg1] at key
      linarith
    nlinarith [sq_nonneg (u x)]
  simp [hu_def, Pi.sub_apply] at hux_eq
  linarith

end MathlibExt.Analysis.ODE.SturmLiouvilleUniqueness
