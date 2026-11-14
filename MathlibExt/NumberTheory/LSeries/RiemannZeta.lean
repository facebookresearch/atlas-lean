/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

@[expose] public section

/-!
# Meromorphicity of the Riemann zeta function

`riemannZeta` is meromorphic on `ℂ`: away from its pole at `s = 1` it equals
`(s - 1)⁻¹ + riemannZeta₀ s`, and `riemannZeta₀` is entire. At `s = 1` it has a simple pole:
its meromorphic order there is `-1`.
-/

open Filter Topology

/-- The Riemann zeta function is meromorphic on `ℂ`. -/
theorem meromorphicOn_riemannZeta : MeromorphicOn riemannZeta Set.univ := by
  have hInv : MeromorphicOn (fun s : ℂ => (s - 1)⁻¹) Set.univ :=
    (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.inv
  have h0 : AnalyticOnNhd ℂ riemannZeta₀ Set.univ := fun x _ =>
    differentiable_riemannZeta₀.analyticAt x
  have heq : (fun s : ℂ => (s - 1)⁻¹ + riemannZeta₀ s) =ᶠ[Filter.codiscreteWithin Set.univ]
      riemannZeta := by
    apply Filter.mem_of_superset (compl_singleton_mem_codiscreteWithin (1 : ℂ))
    intro s hs
    exact (riemannZeta_eq_inv_sub_add hs).symm
  exact (hInv.add h0.meromorphicOn).congr_codiscreteWithin heq isOpen_univ

/-- The Riemann zeta function is meromorphic at `1`. -/
theorem meromorphicAt_riemannZeta_one : MeromorphicAt riemannZeta 1 :=
  meromorphicOn_riemannZeta 1 (Set.mem_univ _)

/-- **The pole of `ζ`.** The Riemann zeta function has a simple pole at `1`. -/
theorem meromorphicOrderAt_riemannZeta_one : meromorphicOrderAt riemannZeta 1 = -1 := by
  set g : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1 with hg
  have hga : AnalyticAt ℂ g 1 := by
    refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have h1 : g =ᶠ[𝓝 z] (fun s => (s - 1) * riemannZeta s) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
        exact Function.update_of_ne hw _ _
      exact (((differentiableAt_id.sub_const 1).mul
        (differentiableAt_riemannZeta hz))).congr_of_eventuallyEq h1
    · simpa only [hg, continuousAt_update_same] using riemannZeta_residue_one
  have heq : ∀ᶠ z in 𝓝[≠] 1, riemannZeta z = (z - 1) ^ (-1 : ℤ) • g z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    rw [hg, Function.update_of_ne hz, smul_eq_mul, zpow_neg_one]
    field_simp
  have := (meromorphicOrderAt_eq_int_iff (n := -1) meromorphicAt_riemannZeta_one).2
    ⟨g, hga, by simp [hg], heq⟩
  simpa using this
